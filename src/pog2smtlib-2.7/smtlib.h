/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2024-2025
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
#ifndef SMTLIB_H
#define SMTLIB_H

#include <cstddef>
#include <map>
#include <vector>

#include "pog.h"

using std::size_t;
using goal_t = std::pair<size_t, size_t>;  // <group, simple_goal>
using goal_index_t = std::vector<goal_t>;
using goal_selection_t = std::map<size_t, std::vector<size_t>>;

/** @brief builds the translation to SMTLIB of one POG goal saves the
 * translation to file
 */
extern void saveSmtLibFileOne(const pog::pog &pog, const goal_t &goal,
                              const std::string &output,
                              bool produce_unsat_core, bool produce_model);

extern void saveSmtLibFile(const pog::pog &pog, const std::string &output,
                           bool produce_unsat_core, bool produce_model);

#endif  // SMTLIB_H
