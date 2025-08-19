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

#ifndef TRANSLATE_SIGNATURE_H
#define TRANSLATE_SIGNATURE_H

#include <memory>
#include <string>
#include <unordered_set>

#include "bconstruct.h"

class Signature;  // forward declaration

/** @brief the text script containing SMT commands to declare and define
 * translations of operators
 * @param signature the signature monomorphized pre-defined operators and
 * identifiers
 * @details the translation of each monomorphized instantiation of an operator
 * may contain SMT declarations, definitions and assertions.
 * */
extern std::string translate(const Signature& signature,
                             BConstruct::Context& context);
/** @brief the text script containing SMT commands to declare and define
 * translations of operators
 * @param signature the signature monomorphized pre-defined operators and
 * identifiers
 * @details the translation of each monomorphized instantiation of an operator
 * may contain SMT declarations, definitions and assertions.
 * */
extern std::string translate(const Signature& signature);

#endif  // TRANSLATE_SIGNATURE_H
