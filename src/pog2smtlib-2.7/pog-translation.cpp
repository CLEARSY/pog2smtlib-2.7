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
#include "pure-typing.h"
#include "translate-predicate.h"
#include "translate-signature.h"

using std::make_pair;
using std::string;
using std::string_view;
using std::unordered_set;

static constexpr bool debug_me = false;

static string assertDefineHypothesisCommand(const string &formula,
                                            const string &name, int i);
static string assertHypothesisCommand(const string &formula, int i);
static string assertLocalHypCommand(const string &formula, int i);

inline string POGTranslations::assertGoalCommand(const string &formula) {
  constexpr string_view pattern = R"((assert (!
  (not {})
  :named |Goal|)
)
)";
  return fmt::format(pattern, formula);
}

string POGTranslations::ofGoal(int group, int goal) {
  if (debug_me) {
    std::cerr << fmt::format("{0} {1} {2}\n", FILE_NAME, group, goal);
  }
  /*
  result is the concatenation of :
  - prelude : the concatenation of
    - declarations for signature of group
    - declarations for additional operators found in goal and in referenced
      local hypotheses
  - script for group
  - script for referenced local hypotheses
  - script for goal (to be negated)
  */
  assert(group <= static_cast<int>(m_pog.pos.size() - 1));
  const pog::POGroup &POGroup = m_pog.pos.at(group);
  assert(goal <= static_cast<int>(POGroup.simpleGoals.size()) - 1);

  string result;
  BConstruct::Context context;  // contains the constructs that have already
                                // been translated (initially it is empty)
  const string_view strGroupPrelude = groupPrelude(group, context);
  result.append(strGroupPrelude);
  Signature localHypSignature;
  const pog::PO &PO = POGroup.simpleGoals.at(goal);
  for (const auto localHypRef : PO.localHypsRef) {
    localHypSignature += m_pogSignatures.ofLocalHyp(group, localHypRef);
  }
  if (debug_me) {
    std::cerr << fmt::format(
        "signature of local hypothesis :\n"
        "{0}\n"
        "fin signature of local hypothesis\n",
        toString(localHypSignature));
  }
  Signature goalSignature;
  goalSignature = m_pogSignatures.ofGoal(group, goal);
  if (debug_me) {
    std::cerr << fmt::format(
        "signature of goal :\n"
        "{0}\n"
        "fin signature of goal\n",
        toString(goalSignature));
  }
  Signature groupSignature;
  groupSignature = m_pogSignatures.ofGroup(group);
  if (debug_me) {
    std::cerr << fmt::format(
        "signature of group :\n"
        "{0}\n"
        "end signature of group\n",
        toString(groupSignature));
  }
  Signature signature;
  signature += localHypSignature;
  signature += goalSignature;
  signature -= groupSignature;
  const string strPreludeComplement = translate(signature, context);
  result.append(strPreludeComplement);

  const string_view &strGroupScript = groupScript(group);
  result.append(strGroupScript);
  for (const auto localHypRef : PO.localHypsRef) {
    const string_view &strlocalHypScript =
        localHypScript(group, localHypRef - 1);
    if (debug_me) {
      std::cerr << fmt::format(
          "script hypothese locale :\n"
          "{0}\n"
          "fin script hypothese locale\n",
          strlocalHypScript);
    }
    result.append(strlocalHypScript);
  }
  const string strGoalScript = goalScript(group, goal);
  if (debug_me) {
    std::cerr << fmt::format(
        "script but :\n"
        "{0}\n"
        "fin script but\n",
        strGoalScript);
  }
  result.append(strGoalScript);
  // add check-sat/unsat-core ?
  return result;
}

string_view POGTranslations::groupPrelude(int group,
                                          BConstruct::Context &context) {
  assert(context.empty());
  if (debug_me) {
    std::cerr << fmt::format("appel POGTranslations::groupPrelude({0})\n",
                             group);
  }
  auto itr = m_groupPreludes.find(group);
  if (itr != m_groupPreludes.end()) {
    return itr->second;
  }
  const Signature &signature = m_pogSignatures.ofGroup(group);
  if (debug_me) {
    std::cerr << fmt::format("{0} signature = {1}\n", FILE_NAME,
                             toString(signature));
  }
  string script = translate(signature, context);
  m_groupPreludes.insert(make_pair(group, std::move(script)));
  string_view result = m_groupPreludes.at(group);
  if (debug_me) {
    std::cerr << fmt::format(
        "prelude groupe {0}:\n {1}\n(fin prelude groupe {0})\n", group, result);
  }
  return result;
}

string_view POGTranslations::groupScript(int group) {
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
  int i = 1;
  for (const auto &pred : pogroup.hyps) {
    if (!pureTypingPredicate(pred)) {
      const string translation = translate(pred);
      const string other = assertHypothesisCommand(translation, i);
      script.append(other);
    }
    ++i;
  }
  m_groupScripts.insert(make_pair(group, std::move(script)));
  string_view result = m_groupScripts.at(group);
  if (debug_me) {
    std::cerr << fmt::format(
        "script groupe {0}:\n"
        "{1}\n"
        "(fin script groupe {0})",
        group, result);
  }
  return result;
}

string_view POGTranslations::localHypScript(int group, int localHyp) {
  const auto index = make_pair(group, localHyp);
  auto itr = m_localHypScripts.find(index);
  if (itr != m_localHypScripts.end()) {
    return itr->second;
  }
  string script;
  assert(0 <= localHyp);
  assert(localHyp < static_cast<int>(m_pog.pos.at(group).localHyps.size()));
  const Pred &pred = m_pog.pos.at(group).localHyps.at(localHyp);
  const string translation = translate(pred);
  const string other = assertLocalHypCommand(translation, localHyp);
  script.append(other);
  m_localHypScripts.insert(make_pair(index, std::move(script)));
  string_view result = m_localHypScripts.at(index);
  if (debug_me) {
    std::cerr << fmt::format(
        "script hypothese locale {0},{1}:\n"
        "{2}\n"
        "(fin script hypothese locale {0},{1})\n",
        group, localHyp, result);
  }
  return result;
}

string POGTranslations::goalScript(int group, int goal) {
  string result;
  const Pred &pred = m_pog.pos.at(group).simpleGoals.at(goal).goal;
  if (!pureTypingPredicate(pred)) {
    const string translation = translate(pred);
    const string command = assertGoalCommand(translation);
    result.append(command);
  } else {
    static const string tautology = "true";
    const string command = assertGoalCommand(tautology);
    result.append(command);
  }
  if (debug_me) {
    std::cerr << fmt::format(
        "script but {0},{1}:\n"
        "{2}\n"
        "(fin script but {0},{1})\n",
        group, goal, result);
  }
  return result;
}

string_view POGTranslations::defineScript(const std::string &name) {
  const auto &index = name;
  auto itr = m_defineScripts.find(index);
  if (itr != m_defineScripts.end()) {
    return itr->second;
  }
  string script;
  if ("B definitions" != name) {
    for (const auto &define : m_pog.defines) {
      if (define.name == name) {
        int index = 1;
        for (const auto &elem : define.contents) {
          if (std::holds_alternative<Pred>(elem)) {
            const Pred &pred = std::get<Pred>(elem);
            if (!pureTypingPredicate(pred)) {
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
  m_defineScripts.insert(make_pair(index, std::move(script)));
  string_view result = m_defineScripts.at(index);
  if (debug_me) {
    std::cerr << fmt::format(
        "script define {0}:\n"
        "{1}\n"
        "(fin script define {0})\n",
        name, result);
  }
  return result;
}

static string assertCommand(const string &formula, const string &label) {
  constexpr string_view pattern = R"((assert (!
  {}
  :named {})
)
)";
  return fmt::format(pattern, formula, label);
}

static string assertDefineHypothesisCommand(const string &formula,
                                            const string &name, int i) {
  constexpr string_view pattern = R"(|Define:{}:{}|)";
  return assertCommand(formula, fmt::format(pattern, name, i));
}

static string assertHypothesisCommand(const string &formula, int i) {
  constexpr string_view pattern = R"(|Hypothesis:{}|)";
  return assertCommand(formula, fmt::format(pattern, i));
}

static string assertLocalHypCommand(const string &formula, int i) {
  constexpr string_view pattern = R"(|Local_Hyp:{}|)";
  return assertCommand(formula, fmt::format(pattern, i));
}
