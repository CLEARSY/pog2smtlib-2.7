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

 private:
  const pog::pog &m_pog;
  POGSignatures &m_pogSignatures;

  using int_X_int = std::pair<int, int>;

  std::map<int, std::string> m_groupPreludes;
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
  std::string_view groupPrelude(int group, BConstruct::Context &context);

  // the following contains SMT commands: labeled assert
  std::string_view groupScript(int group);
  std::string_view localHypScript(int group, int localHypRef);
  std::string_view defineScript(const std::string &name);
  std::string_view hypothesisScript(int group, int hypothesis);
  std::string goalScript(int group, int goal);

  static std::string assertCommand(const string &&formula,
                                   const string &&label);
  static std::string assertGoalCommand(const string &&formula);
  static inline std::string assertGoalCommand(const string &formula);
};

#endif  // POG_TRANSLATION_H
