/******************************* CLEARSY **************************************
This file is part of b2smtlib

Copyright (C) 2024 CLEARSY (contact@clearsy.com)

b2smtlib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License version 3 as published by
the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/
#ifndef SMTLIB_H
#define SMTLIB_H

#include <QDomDocument>
#include <map>
#include <vector>

#include "pog.h"

using goal_selection_t = std::map<int, std::vector<size_t>>;

namespace smtlib {
///@todo ne devrait plus être utilisé
enum class Logic { UF, QF_UF, UFNIA, QF_UFNIA, UFNRA, QF_UFNRA };

class Po {
 public:
  int group;
  std::vector<std::string> definitions;
  std::vector<std::string> hypotheses;
  std::vector<std::string> localHypotheses;
  std::vector<std::pair<int, std::string>> simpleGoals;
};

class SmtLibException : public std::exception {
 public:
  SmtLibException(const std::string desc) : description{desc} {}
  ~SmtLibException() throw() {}
  const char *what() const noexcept override {
    std::string message{"b2smtlib"};
    message.append(description);
    const char *res = message.c_str();
    return res;
  }

 private:
  std::string description;
};

extern void saveSmtLibFileIncrSome(Logic logic, const pog::Pog &pog,
                                   const goal_selection_t &goals,
                                   const std::string &output,
                                   bool produce_model);

extern void saveSmtLibFileIncr(Logic logic, const pog::Pog &pog,
                               const std::string &output, bool produce_model);

extern void saveSmtLibFileNonIncrOne(Logic logic, const pog::Pog &pog,
                                     int groupId, size_t goalId,
                                     const std::string &output,
                                     bool produce_model);

extern void saveSmtLibFileNonIncr(Logic logic, const pog::Pog &pog,
                                  const std::string &output,
                                  bool produce_model);

}  // namespace smtlib

#endif  // SMTLIB_H
