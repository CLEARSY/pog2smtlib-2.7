/*
  This file is part of pog2smtlib-2.7.
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

#ifndef TRANSLATE_PREDICATE_H
#define TRANSLATE_PREDICATE_H
#include <string>

class Pred;

/** @brief translates a predicate to SMT
 * @param pred a B predicate
 * @details realizes a syntactic translation of the formula, without the
 * declaration, definition and assertion of the operators and data types
 * occurring in the formula.
 * @see translate(const std::unordered_set<MonomorphizedOperator> &)
 */
extern std::string translate(const Pred& pred);

#endif  // TRANSLATE_PREDICATE_H
