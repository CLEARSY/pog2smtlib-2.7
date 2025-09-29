/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2025
  pog2smtlib-2.7 is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/
#include "pog-translation.h"

#include <unordered_set>
#include <variant>

#include "cc-compatibility.h"
#include "signature.h"
#include "translate-predicate.h"
#include "translate-signature.h"

using std::make_pair;
using std::string;
using std::string_view;
using std::unordered_set;

string POGTranslations::to_string() const {
  string result;
  result.append("POGTranslations\n");
  result.append("  m_pogSignatures\n");
  result.append(m_pogSignatures.to_string());
  result.append("  m_groupPreludes\n");
  for (const auto &p : m_groupPreludes) {
    result.append(fmt::format("    {}: {}\n", p.first, toString(p.second)));
  }
  result.append("  m_groupScripts\n");
  for (const auto &p : m_groupScripts) {
    result.append(fmt::format("    {}: {}\n", p.first, p.second));
  }
  result.append("  m_localHypScripts\n");
  for (const auto &p : m_localHypScripts) {
    result.append(fmt::format("    {}, {}: {}\n", p.first.first, p.first.second,
                              p.second));
  }
  result.append("  m_hypothesisScripts\n");
  for (const auto &p : m_hypothesisScripts) {
    result.append(fmt::format("    {}, {}: {}\n", p.first.first, p.first.second,
                              p.second));
  }
  result.append("  m_defineScripts\n");
  for (const auto &p : m_defineScripts) {
    result.append(fmt::format("    {}: {}\n", p.first, p.second));
  }
  return result;
}

inline const string POGTranslations::assertCommand(const string &formula,
                                                   const string &label) {
  constexpr string_view pattern = R"((assert (!
  {}
  :named {}))
)";
  return fmt::format(pattern, formula, label);
}

inline const string POGTranslations::assertGoalCommand(const string &formula) {
  constexpr string_view pattern = R"((assert (!
  (not
{})
  :named |Goal|))
)";
  return fmt::format(pattern, formula);
}

inline const string POGTranslations::assertDefineHypothesisCommand(
    const string &formula, const string &name, size_t i) {
  constexpr string_view pattern = R"(|Define:{}:{}|)";
  return assertCommand(formula, fmt::format(pattern, name, i));
}

inline const string POGTranslations::assertHypothesisCommand(
    const string &formula, size_t i) {
  constexpr string_view pattern = R"(|Hypothesis:{}|)";
  return assertCommand(formula, fmt::format(pattern, i));
}

inline const string POGTranslations::assertLocalHypCommand(
    const string &formula, size_t i) {
  constexpr string_view pattern = R"(|Local_Hyp:{}|)";
  return assertCommand(formula, fmt::format(pattern, i));
}

string POGTranslations::ofGoal(const goal_t &goal) {
  static constexpr bool debug_me = false;
  const size_t &group = goal.first;
  const size_t &sgoal = goal.second;
  /*
  group is the index of the Proof_Obligation element for the current goal
  goal is the index of the Single_Goal element in the group

  result is the concatenation of :
  1. prelude : the concatenation of
    1.1 declarations for signature of group
    1.2 declarations for additional operators found in goal and in referenced
      local hypotheses (complement signature)
  2. script for group
  3. script for referenced local hypotheses
  4. script for goal (to be negated)
  */
  assert(group < m_pog.pos.size());
  const pog::POGroup &POGroup = m_pog.pos.at(group);
  assert(sgoal < POGroup.simpleGoals.size());

  string result;
  BConstruct::Context context;  // contains the constructs that have already
                                // been translated (initially it is empty)
  const string_view strGroupPrelude = groupPrelude(group, context);

  // 1.1 store in result the declarations for signature of group
  result.append(strGroupPrelude);
  if (debug_me) {
    std::cerr << "1.1" << std::endl
              << "-- context" << std::endl
              << ::toString(context) << std::endl
              << "-- result" << std::endl
              << result << std::endl;
  }
  // 1.2 find all additional operators found in goal and in referenced local
  // hypotheses

  // accumulate signature of all referenced local hypotheses in
  // localHypSignature
  Signature localHypSignature;
  const pog::PO &PO = POGroup.simpleGoals.at(sgoal);
  for (const auto localHypRef : PO.localHypsRef) {
    if (!(0 < localHypRef))
      throw std::runtime_error(
          "local hypothesis reference should be strictly positive");
    localHypSignature += m_pogSignatures.ofLocalHyp(group, localHypRef - 1);
  }

  const Signature goalSignature = m_pogSignatures.ofGoal(goal);
  Signature complementSignature;
  complementSignature += localHypSignature;
  complementSignature += goalSignature;
  complementSignature -= m_pogSignatures.ofGroup(group);
  const string strPreludeComplement = translate(complementSignature, context);
  // 1.2 append to result the declarations for additional operators found in
  // goal and in referenced local hypotheses
  result.append(strPreludeComplement);
  if (debug_me) {
    std::cerr << "1.2" << std::endl
              << "-- localHypSignature" << std::endl
              << localHypSignature.to_string() << std::endl
              << "-- goalSignature" << std::endl
              << goalSignature.to_string() << std::endl
              << "-- complementSignature" << std::endl
              << complementSignature.to_string() << std::endl
              << "-- context" << std::endl
              << ::toString(context) << std::endl
              << "-- result" << std::endl
              << result << std::endl;
  }

  const string_view &strGroupScript = groupScript(group);
  // 2. append to result the script for the group
  result.append(strGroupScript);

  // 3. append to result the script for the referenced local hypotheses
  for (const auto localHypRef : PO.localHypsRef) {
    if (!(0 < localHypRef))
      throw std::runtime_error(
          "local hypothesis reference should be strictly positive");
    const string_view &strlocalHypScript =
        localHypScript(group, localHypRef - 1);
    result.append(strlocalHypScript);
  }

  // 4. appeld to result the script for the (negation of) the goal
  const string strGoalScript = goalScript(goal);
  result.append(strGoalScript);

  // add check-sat/unsat-core ?
  return result;
}

const string &POGTranslations::groupPrelude(size_t group,
                                            BConstruct::Context &context) {
  assert(context.empty());
  auto itr = m_groupPreludes.find(group);
  if (itr != m_groupPreludes.end()) {
    context = itr->second.m_context;
    return itr->second.m_script;
  }
  const Signature &signature = m_pogSignatures.ofGroup(group);
  string script = translate(signature, context);
  groupPreludeCache preludeCache = {script, context};
  const auto p =
      m_groupPreludes.insert(make_pair(group, std::move(preludeCache)));
  return p.first->second.m_script;
}

const string &POGTranslations::groupScript(size_t group) {
  auto itr = m_groupScripts.find(group);
  if (itr != m_groupScripts.end()) {
    return itr->second;
  }
  string script;
  const pog::POGroup &pogroup = m_pog.pos.at(group);
  for (auto defName : pogroup.definitions) {
    string_view other = defineScript(defName);
    script.append(other);
  }
  size_t i = 1;
  for (const auto &pred : pogroup.hyps) {
    if (!pred.isPureTypingPredicate()) {
      const string translation = translate(pred);
      const string other = assertHypothesisCommand(translation, i);
      script.append(other);
    }
    ++i;
  }
  const auto &p = m_groupScripts.insert(make_pair(group, std::move(script)));
  const string &result = p.first->second;
  return result;
}

const string &POGTranslations::localHypScript(size_t group, size_t localHyp) {
  const bool debug_me = false;
  const goal_t index = make_pair(group, localHyp);
  auto itr = m_localHypScripts.find(index);
  if (itr != m_localHypScripts.end()) {
    return itr->second;
  }
  string script;
  assert(localHyp < m_pog.pos.at(group).localHyps.size());
  const Pred &pred = m_pog.pos.at(group).localHyps.at(localHyp);
  if (!pred.isPureTypingPredicate()) {
    const string translation = translate(pred);
    const string other = assertLocalHypCommand(translation, localHyp);
    script.append(other);
  }
  const auto &p = m_localHypScripts.insert(make_pair(index, std::move(script)));
  const string &result = p.first->second;
  if (debug_me) {
    std::cerr << fmt::format("-- POGTranslations::localHypScript({}, {})",
                             group, localHyp)
              << std::endl
              << result << std::endl;
  }
  return result;
}

const string POGTranslations::goalScript(const goal_t &goal) {
  string result;
  const Pred &pred = m_pog.pos.at(goal.first).simpleGoals.at(goal.second).goal;
  if (!pred.isPureTypingPredicate()) {
    static const unsigned indent = 2u;
    const string translation = translate(pred, indent);
    const string command = assertGoalCommand(translation);
    result.append(command);
  } else {
    static const string tautology = "true";
    const string command = assertGoalCommand(tautology);
    result.append(command);
  }
  return result;
}

const string &POGTranslations::defineScript(const std::string &name) {
  const auto &index = name;
  auto itr = m_defineScripts.find(index);
  if (itr != m_defineScripts.end()) {
    return itr->second;
  }
  string script;
  if ("B definitions" != name) {
    for (const auto &define : m_pog.defines) {
      if (define.name == name) {
        size_t index = 1;
        for (const auto &elem : define.contents) {
          if (std::holds_alternative<Pred>(elem)) {
            const Pred &pred = std::get<Pred>(elem);
            if (!pred.isPureTypingPredicate()) {
              const string &translation = translate(pred);
              const string &command =
                  assertDefineHypothesisCommand(translation, name, index);
              script.append(command);
            }
          }
          ++index;
        }
        break;
      }
    }
  }
  const auto &p = m_defineScripts.insert(make_pair(index, std::move(script)));
  const string &result = p.first->second;
  return result;
}

string POGTranslations::toString(
    POGTranslations::groupPreludeCache const &prelude) {
  return fmt::format("  - script: \n{}\n  -context: {}\n", prelude.m_script,
                     ::toString(prelude.m_context));
}
