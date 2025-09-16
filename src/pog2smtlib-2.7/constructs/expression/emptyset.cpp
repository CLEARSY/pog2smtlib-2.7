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
#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "btype.h"
#include "pred.h"
namespace BConstruct::Expression {

// 0: the SMT symbol for generic empty set operator
// 1: the SMT symbol for the generic "is element of" operator
// 2: the SMT symbol for the type of the monomorphized empty set operator
// 3: the SMT symbol for the element type of 2
// 4: the auxiliary SMT symbol for 3
static constexpr std::string_view SCRIPT = R"((declare-const |{0} {4}| {2})
(assert (!
  (forall ((e {3})) (not (|{1} {4}| e |{0} {4}|)))
  :named |ax.set.in.empty {4}|))
)";
static constexpr std::string_view emptySetOperatorStr = "set.empty";
static constexpr std::string_view isElementOfOperatorStr = "set.in";

EmptySet::EmptySet(const BType &t) : UnaryBType(t) {
  const BType pt = BType::POW(t);
  m_script = fmt::format(SCRIPT, emptySetOperatorStr, isElementOfOperatorStr,
                         symbol(pt), symbol(t), symbolInner(t));
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Type::Type>(pt),
       std::make_shared<BConstruct::Predicate::SetMembership>(t)});
  m_label = "{}";
  m_debug_string = fmt::format("{{}}_<{}>", t.to_string());
}

};  // namespace BConstruct::Expression
