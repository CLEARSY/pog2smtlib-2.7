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

struct smt_options_t {
  bool produce_unsat_core;
  bool produce_model;

  // If reduce_po_set is true then reduce_po contains the value of --reduce-po
  // (n >= 0). When reduce_po_set is false, the option was not provided.
  bool reduce_po_set;
  size_t reduce_po;

  // When true, enables direct deduction behavior. It is only valid when
  // reduce_po_set is true (validation is done by the caller).
  bool direct_deduction;

  smt_options_t()
      : produce_unsat_core{false},
        produce_model{false},
        reduce_po_set{false},
        reduce_po{0},
        direct_deduction{false} {}
};

/** @brief builds the translation to SMTLIB of one POG goal saves the
 * translation to file
 */
extern void saveSmtLibFileOne(const pog::pog &pog, const goal_t &goal,
                              const std::string &output,
                              const smt_options_t &options);

extern void saveSmtLibFile(const pog::pog &pog, const std::string &output,
                           const smt_options_t &options);

#endif  // SMTLIB_H
