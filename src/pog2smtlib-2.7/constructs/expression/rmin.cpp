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
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) {1})
(assert (!
  (forall ((s {2}))
    (=> (not (= s {3})) ({4} ({0} s) s)))
  :named |ax.rmin.is.member|))
 (assert (!
   (forall ((s {2}))
     (forall ((e {1}))
        (=> ({4} e s) (<= ({0} s) e))))
  :named |ax.rmin.is.ge|))
)";

RMin::RMin() {
  m_script = fmt::format(
      SCRIPT,
      /*0*/ smtSymbol(Expr::UnaryOp::RMinimum),
      /*1*/ symbol(BType::REAL),
      /*2*/ symbol(BType::POW(BType::REAL)),
      /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::REAL),
      /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::REAL));
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(BType::REAL),
       std::make_shared<BConstruct::Expression::EmptySet>(BType::REAL)});
  m_label = "rmin";
  m_debug_string = "rmin";
}
};  // namespace BConstruct::Expression
