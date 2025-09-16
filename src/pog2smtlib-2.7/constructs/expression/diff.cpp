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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {1}) {1})
(assert (!
  (forall ((e |{3}|) (s {1}) (t {1}))
    (= ({2} e ({0} s t))
       (and ({2} e s) (not ({2} e t)))))
  :named |ax.set.in.diff {3}|))
)";

Difference::Difference(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Set_Difference, T),
                         /*1*/ symbol(PT),
                         /*2*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                         /*3*/ symbolInner(T));
  m_label = "-";
  m_prerequisites.insert(
      std::make_shared<BConstruct::Predicate::SetMembership>(T));
  m_debug_string = fmt::format("-_{}", T.to_string());
}

};  // namespace BConstruct::Expression
