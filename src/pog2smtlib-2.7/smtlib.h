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

#include <map>
#include <vector>

#include "pog.h"

using goal_selection_t = std::map<int, std::vector<size_t>>;

/** @brief builds the translation to SMTLIB of one POG goal saves the
 * translation to file
 * @param groupId 0-indexed position of the POG goal group
 * @param goalId 0-indexed position of the goal within its POG group.
 */
extern void saveSmtLibFileOne(const pog::pog &pog, int groupId, size_t goalId,
                              const std::string &output,
                              bool produce_unsat_core, bool produce_model);

extern void saveSmtLibFile(const pog::pog &pog, const std::string &output,
                           bool produce_unsat_core, bool produce_model);

#endif  // SMTLIB_H
