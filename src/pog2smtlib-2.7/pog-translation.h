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
#ifndef POG_TRANSLATION_H
#define POG_TRANSLATION_H

#include <map>
#include <ostream>
#include <string>
#include <string_view>

#include "bconstruct.h"
#include "pog-signatures.h"
#include "pog.h"

using std::ostream;

using goal_t = std::pair<size_t, size_t>;
class POGTranslations {
 public:
  // remove pogSignatures from parameters to have it owned by object (create
  // method to build signature information on demand)
  explicit POGTranslations(const pog::pog &pog, POGSignatures &pogSignatures)
      : m_pog(pog), m_pogSignatures(pogSignatures) {}

  void ofGoal(ostream &os, const goal_t &goal);  // todo
  std::string ofGoal(const goal_t &goal, bool rp, bool fixpoint, size_t rpN,
                     bool dd);

  string to_string() const;

 private:
  /**
   * @brief returns the Define set of hypotheses of the given name
   *
   * Returns an empty dummy Define value in case the given name is not
   * registered (or should be ignored).
   * */
  const pog::Define &define(const std::string &definition);

  std::string ofGoal(const goal_t &goal);

  /**
   * @brief gets the SMT encoding for a given goal applying intros/lasso tactics
   * @param goal the goal to encode
   * @param fixpoint apply lasso tactic until reaching a fixpoint
   * @param rpN apply lasso tactic up to a given width (only if fixpoint is
   * false)
   * @param dd do intros before applying lasso
   * @details The intros tactic consists in moving local hypotheses to the list
   * of global hypotheses. The lasso tactic consist in discarding global
   * hypotheses that have no free symbols appearing in the seed. When rpN is 0 :
   * all are discarded. Otherwise the seed is the result of lasso(rpN-1).
   */
  std::string ofGoal(const goal_t &goal, bool fixpoint, size_t rpN, bool dd);

  const pog::pog &m_pog;
  POGSignatures &m_pogSignatures;

  struct groupPreludeCache {
    std::string m_script;
    BConstruct::Context m_context;
  };
  static string toString(const groupPreludeCache &);

  std::map<const std::string, const pog::Define &> m_defines;
  std::map<size_t, groupPreludeCache> m_groupPreludes;
  std::map<size_t, std::string> m_groupScripts;
  std::map<goal_t, std::string> m_localHypScripts;
  std::map<goal_t, std::string> m_hypothesisScripts;
  std::map<std::string, std::string> m_defineScripts;

  static inline goal_t index(size_t group, size_t goal) {
    return std::make_pair(group, goal);
  }
  static inline size_t index(size_t group) { return group; }

  /**@brief returns the string (view) to the SMT commands fo
   * @param group the index of the group of POs in the POG
   * @param context (output) the constructs that have been translated
   * @pre context is empty
   */
  const std::string &groupPrelude(size_t group, BConstruct::Context &context);

  // the following contains SMT commands: labeled assert
  const std::string &groupScript(size_t group);
  const std::string &localHypScript(size_t group, size_t localHypRef);
  const std::string &defineScript(const std::string &name);
  const std::string goalScript(const goal_t &goal);

  static inline const std::string assertCommand(const string &formula,
                                                const string &label);
  static inline const std::string assertDefineHypothesisCommand(
      const string &formula, const string &name, size_t i);
  static inline const std::string assertHypothesisCommand(const string &formula,
                                                          size_t i);
  static inline const std::string assertLocalHypCommand(const string &formula,
                                                        size_t i);
  static inline const std::string assertGoalCommand(const string &formula);
};

#endif  // POG_TRANSLATION_H
