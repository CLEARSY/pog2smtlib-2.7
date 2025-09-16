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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {2})
(assert (!
  (forall ((s {1}) (t {1}))
    (= ({3} s ({0} t))
       (and ({3} s ({4} t))
            (not (= s {5})))))
  :named |ax.non empty sub-sets {6}|))
)";

PowerSet1::PowerSet1(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto PPT = BType::POW(PT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Non_Empty_Subsets, T),
                         /*1*/ symbol(PT),
                         /*2*/ symbol(PPT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                         /*4*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                         /*5*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, T),
                         /*6*/ symbolInner(T));
  m_label = "POW1";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::EmptySet>(T),
       std::make_shared<BConstruct::Predicate::SetMembership>(PT),
       std::make_shared<BConstruct::Expression::PowerSet>(T)});
  m_debug_string = fmt::format("POW1_{}", T.to_string());
}

};  // namespace BConstruct::Expression
