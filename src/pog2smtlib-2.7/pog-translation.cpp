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

string POGTranslations::ofGoal(const goal_t &goal, bool rp, bool fixpoint,
                               size_t rpN, bool dd) {
  if (!rp) {
    return this->ofGoal(goal);
  } else {
    return this->ofGoal(goal, fixpoint, rpN, dd);
  }
}

string POGTranslations::ofGoal(const goal_t &goal, bool fixpoint,
                               size_t lassoWidth, bool dd) {
  [[maybe_unused]] constexpr bool debugme = false;
  /*
  1. Compute the set of predicates corresponding to the initial goal : simple
  goal and local hypotheses. That is, unless dd is set true, in that case the
  set of predicates is just the simple goal.
  2. Then, lasso in all the predicates that have a common free symbol with the
  goal, set the result as the new goal, repeat this operation lassoWidth time.
  3. Compute the full signature of the lassoed predicates.
  4. Produce the translation of this signature and of the lassoed predicates.
  */

  /* 1 */
  const size_t &group = goal.first;
  const size_t &sgoal = goal.second;
  assert(group < m_pog.pos.size());
  const pog::POGroup &POGroup = m_pog.pos.at(group);
  assert(sgoal < POGroup.simpleGoals.size());

  // vocabulary collects the free symbols in the predicates in the
  // initial lasso seed: the goal predicate and, unless direct-deduction (dd)
  // is true, the local hypotheses.
  std::unordered_set<Data> vocabulary;

  [[maybe_unused]] auto to_string =
      [](const std::unordered_set<Data> &vocabulary) -> std::string {
    std::string result;
    for (auto data : vocabulary) {
      if (!result.empty()) {
        result += "|";
      }
      result += data.to_string();
    }
    return result;
  };

  const pog::PO &PO = POGroup.simpleGoals.at(sgoal);

  const Signature &s = m_pogSignatures.ofSimpleGoal(goal);
  Signature signature = s;  // the signature of the produced problem
  vocabulary.insert(s.m_data.begin(), s.m_data.end());  // the free symbols

  if (!dd) {
    for (const auto localHypRef : PO.localHypsRef) {
      if (!(0 < localHypRef))
        throw std::runtime_error(
            "local hypothesis reference should be strictly positive");
      const Signature &s2 = m_pogSignatures.ofLocalHyp(group, localHypRef);
      signature += s2;
      vocabulary.insert(s2.m_data.begin(), s2.m_data.end());
    }
  }

  // Step 1 complete: initialPreds now contains the seed predicates. Further
  // steps (lasso expansion, signature computation and translation) will use
  // this set.

  /* Step 2 (and 3)
   * if lassoWidth is different from zero then
   *   let accumulator be an initially empty vector of Pred references
   *   let rest be a vector of references of Pred instances that are in the
   *   Define elements used by the POGroup
   *   let counter be zero
   *   while counter < lassoWidth do
   *     increment counter
   *     let vocabulary_extension be a set of std::unordered_set<Data>;
   *     for each Pred reference r in rest
   *       let psig be m_pogSignatures of r
   *       if psig.m_data has an element in common with vocabulary then
   *          add r to accumulator
   *          remove r from rest
   *          if counter < lassoWidth then
   *            for each free symbol s in psig.m_data
   *              if s is not in vocabulary then
   *                insert s into vocabulary_extension
   *       end if
   *     end for
   *     if vocabulary_extension is empty
   *       exit from loop
   *     end if
   *     add vocabulary_extension to vocabulary
   *     increment counter
   *   end while
   *
   */

  /* hypotheses lassoed in the problem together with
     - the Define element name
     - the position in the Define element
   */
  std::vector<std::tuple<const Pred *, size_t>> accumulatorHypotheses;
  std::vector<std::tuple<const Pred *, const string &, size_t>> accumulator;
  if (fixpoint || 0 < lassoWidth) {
    /* hypotheses not lassoed in the problem, together with
      - the Define element name,
      - the position in the Define element,
      - their signature
    */
    std::list<std::tuple<const Pred *, size_t, const Signature &>>
        restHypotheses;
    std::list<
        std::tuple<const Pred *, const string &, size_t, const Signature &>>
        rest;

    // local function (should be in POG API really): get Define by name
    auto getDefine = [this](const string &definition) -> const pog::Define & {
      for (auto &define : m_pog.defines) {
        if (define.name == definition) return define;
      }
      throw std::runtime_error("cannot find Define element " + definition);
    };
    // get all the PO group hypotheses that may be lassoed in and their
    // signature
    for (size_t i = 0u; i < POGroup.hyps.size(); ++i) {
      const Pred *pred = &POGroup.hyps.at(i);
      if (!pred->isPureTypingPredicate()) {
        const Signature &s2 = m_pogSignatures.ofHypothesis(group, i);
        restHypotheses.push_back({pred, i, s2});
      }
    }
    // get all the Define hypotheses that may be lassoed in and their signature
    for (const string &definition : POGroup.definitions) {
      const pog::Define &define = getDefine(definition);
      size_t position = 0;
      for (const variant<pog::Set, Pred> &elem : define.contents) {
        if (std::holds_alternative<Pred>(elem)) {
          const Pred *pred = &std::get<Pred>(elem);
          if (!pred->isPureTypingPredicate()) {
            const Signature &signature =
                m_pogSignatures.ofGlobalHypothesis(pred);
            rest.push_back({pred, define.name, position, signature});
          }
        }
        ++position;
      }
    }
    // try to compute efficiently intersection of two sets
    auto intersects = [](const std::unordered_set<Data> &s1,
                         const std::unordered_set<Data> &s2) {
      const auto &smaller = s1.size() < s2.size() ? s1 : s2;
      const auto &larger = s1.size() < s2.size() ? s2 : s1;
      for (const auto &elem : smaller) {
        if (larger.find(elem) != larger.end()) {
          return true;
        }
      }
      return false;
    };
    unsigned counter = 0;
    // lasso predicates into the problem
    while (fixpoint || counter < lassoWidth) {
      ++counter;
      if (debugme) {
        std::cerr << "lasso iteration: " << counter << std::endl;
        std::cerr << to_string(vocabulary) << std::endl;
      }
      std::unordered_set<Data> newnames;
      Signature extension;
      auto itH = restHypotheses.begin();
      while (itH != restHypotheses.end()) {
        auto next = std::next(itH);
        auto [pred, pos, psig] = *itH;
        if (debugme) {
          std::cerr << "testing if pred is lassoed: " << pred->show() << " "
                    << to_string(psig.m_data) << std::endl;
        }
        if (intersects(vocabulary, psig.m_data)) {
          if (debugme) {
            std::cerr << pred->show() << " lassoed in" << std::endl;
          }
          for (const auto &data : psig.m_data) {
            if (debugme) {
              std::cerr << data.to_string() << " "
                        << (vocabulary.find(data) == vocabulary.end()
                                ? "is new"
                                : "is already present")
                        << std::endl;
            }
            if (vocabulary.find(data) == vocabulary.end()) {
              newnames.insert(data);
            }
          }
          accumulatorHypotheses.push_back({pred, pos});
          extension += psig;
          restHypotheses.erase(itH);
        }
        itH = next;
      }
      auto it = rest.begin();
      while (it != rest.end()) {
        auto next = std::next(it);
        auto [pred, name, pos, psig] = *it;
        if (debugme) {
          std::cerr << "testing if pred is lassoed: " << pred->show() << " "
                    << to_string(psig.m_data)
                    << " vocabulary=" << to_string(vocabulary) << std::endl;
        }
        if (intersects(vocabulary, psig.m_data)) {
          if (debugme) {
            std::cerr << pred->show() << " lassoed in" << std::endl;
          }
          for (const auto &data : psig.m_data) {
            if (debugme) {
              std::cerr << data.to_string() << " "
                        << (vocabulary.find(data) == vocabulary.end()
                                ? "is new"
                                : "is already present")
                        << std::endl;
            }
            if (vocabulary.find(data) == vocabulary.end()) {
              newnames.insert(data);
            }
          }
          accumulator.push_back({pred, name, pos});
          extension += psig;
          rest.erase(it);
        }
        it = next;
      }
      if (debugme) {
        std::cerr << "New names at iteration " << counter << ": " << std::endl;
        for (const auto &data : newnames) {
          std::cerr << "  " << data.to_string() << std::endl;
        }
      }
      if (newnames.empty()) {  // fixpoint is reached
        if (debugme) {
          std::cerr << "Fixpoint reached at iteration " << counter << std::endl;
        }
        signature += extension;
        break;
      }
      vocabulary.insert(std::make_move_iterator(newnames.begin()),
                        std::make_move_iterator(newnames.end()));
      if (debugme) {
        std::cerr << "Vocabulary at end of iteration " << counter << ": "
                  << std::endl;
        for (const auto &data : vocabulary) {
          std::cerr << "  " << data.to_string() << std::endl;
        }
      }
      signature += extension;
    }
  }
  // Steps 2, 3 complete

  // Step 4
  BConstruct::Context context;
  string script = translate(signature, context);
  if (!dd) {
    for (size_t i = 0u; i < POGroup.hyps.size(); ++i) {
      const Pred &pred = POGroup.hyps.at(i);
      if (!pred.isPureTypingPredicate()) {
        const string formula = translate(pred);
        script += assertHypothesisCommand(formula, i);
      }
    }
    for (const auto localHypRef : PO.localHypsRef) {
      const Pred &pred = POGroup.localHyps.at(localHypRef - 1);
      if (!pred.isPureTypingPredicate()) {
        const string formula = translate(pred);
        script += assertLocalHypCommand(formula, localHypRef - 1);
      }
    }
  }
  for (auto hyp : accumulatorHypotheses) {
    const auto &[pred, pos] = hyp;
    if (!pred->isPureTypingPredicate()) {
      const string formula = translate(*pred);
      script += assertHypothesisCommand(formula, pos);
    }
  }
  for (auto hyp : accumulator) {
    const auto &[pred, name, pos] = hyp;
    if (!pred->isPureTypingPredicate()) {
      const string formula = translate(*pred);
      script += assertDefineHypothesisCommand(formula, name, pos);
    }
  }
  if (!PO.goal.isPureTypingPredicate()) {
    static const unsigned indent = 2u;
    const string translation = translate(PO.goal, indent);
    const string command = assertGoalCommand(translation);
    script.append(command);
  } else {
    static const string tautology = "true";
    const string command = assertGoalCommand(tautology);
    script.append(command);
  }

  return script;
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
    localHypSignature += m_pogSignatures.ofLocalHyp(group, localHypRef);
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

const pog::Define &POGTranslations::define(const std::string &definition) {
  static pog::Define nil = pog::Define(std::string());
  if (m_defines.empty()) {
    for (const auto &define : m_pog.defines) {
      if ("B definitions" == define.name) continue;
      m_defines.insert({define.name, define});
    }
  }
  const auto &it = m_defines.find(definition);
  if (it == m_defines.end()) {
    return nil;
  } else {
    return it->second;
  }
}
