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

static constexpr std::string_view SCRIPT = R"((declare-const {0} {2})
(assert (!
  (forall ((e |{1}|)) (= ({3} e {0}) (and (<= {4} e) (<= e {5}))))
  :named |ax.set.in.INT|))
)";

Int::Int() {
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::Visitor::EConstant::INT),
                  /*1*/ symbolInner(BType::INT),
                  /*2*/ symbol(BType::POW(BType::INT)),
                  /*3*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
                  /*4*/ smtSymbol(Expr::Visitor::EConstant::MinInt),
                  /*5*/ smtSymbol(Expr::Visitor::EConstant::MaxInt));
  m_label = "INT";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT),
       std::make_shared<BConstruct::Expression::Maxint>(),
       std::make_shared<BConstruct::Expression::Minint>()});
  m_debug_string = "INT";
}
};  // namespace BConstruct::Expression