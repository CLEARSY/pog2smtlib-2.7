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
(declare-fun {0} ({2} {1}) {2})
(assert (!
  (forall ((s {2})(x {1})(p {3}))
    (= ({4} p ({0} s x))
       (or (= p (maplet ({5} s) x))
           ({4} p s))))
  :named |ax.insert.tail.def {6}|))
)";

Insert_At_Tail::Insert_At_Tail(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Tail_Insertion, T),
                         /*1*/ symbol(T),
                         /*2*/ symbol(PZxT),
                         /*3*/ symbol(ZxT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*5*/ smtSymbol(Expr::UnaryOp::Size, T),
                         /*6*/ symbolInner(T));
  m_label = "←";
  m_prerequisites.insert({
      std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
      std::make_shared<BConstruct::Expression::Size>(T),
  });
  m_debug_string = fmt::format("←_{}", T.to_string());
}

};  // namespace BConstruct::Expression
