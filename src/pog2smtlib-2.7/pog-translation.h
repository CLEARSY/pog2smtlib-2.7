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

class POGTranslations {
 public:
  // remove pogSignatures from parameters to have it owned by object (create
  // method to build signature information on demand)
  explicit POGTranslations(const pog::pog &pog, POGSignatures &pogSignatures)
      : m_pog(pog), m_pogSignatures(pogSignatures) {}

  void ofGoal(ostream &os, int group, int goal);  // todo
  std::string ofGoal(int group, int goal);

  string to_string() const;

 private:
  const pog::pog &m_pog;
  POGSignatures &m_pogSignatures;

  using int_X_int = std::pair<int, int>;

  struct groupPreludeCache {
    std::string m_script;
    BConstruct::Context m_context;
  };
  static string toString(const groupPreludeCache &);
  static string toString(const BConstruct::Context &);

  std::map<int, groupPreludeCache> m_groupPreludes;
  std::map<int, std::string> m_groupScripts;
  std::map<int_X_int, std::string> m_localHypScripts;
  std::map<int_X_int, std::string> m_hypothesisScripts;
  std::map<std::string, std::string> m_defineScripts;

  static inline std::pair<int, int> index(int group, int goal) {
    return std::make_pair(group, goal);
  }
  static inline int index(int group) { return group; }

  /**@brief returns the string (view) to the SMT commands fo
   * @param group the index of the group of POs in the POG
   * @param context (output) the constructs that have been translated
   * @pre context is empty
   */
  const std::string &groupPrelude(int group, BConstruct::Context &context);

  // the following contains SMT commands: labeled assert
  const std::string &groupScript(int group);
  const std::string &localHypScript(int group, int localHypRef);
  const std::string &defineScript(const std::string &name);
  const std::string goalScript(int group, int goal);

  static inline const std::string assertCommand(const string &formula,
                                                const string &label);
  static inline const std::string assertDefineHypothesisCommand(
      const string &formula, const string &name, int i);
  static inline const std::string assertHypothesisCommand(const string &formula,
                                                          int i);
  static inline const std::string assertLocalHypCommand(const string &formula,
                                                        int i);
  static inline const std::string assertGoalCommand(const string &formula);
};

#endif  // POG_TRANSLATION_H
