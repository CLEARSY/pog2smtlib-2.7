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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {1})
(assert (!
  (forall ((R {1})(p {2}))
    (= ({3} p ({0} R))
       (or (= (fst p) (snd p))
           ({3} p ({5} R)))))
  :named |ax.closure {4}|))
)";

Closure::Closure(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Closure, T),
                         /*1*/ symbol(PTxT),
                         /*2*/ symbol(TxT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, TxT),
                         /*4*/ symbolInner(T),
                         /*5*/ smtSymbol(Expr::UnaryOp::Transitive_Closure, T));
  m_label = "closure";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxT),
       std::make_shared<BConstruct::Expression::Closure1>(T)});
  m_debug_string = fmt::format("closure_{}", T.to_string());
}

};  // namespace BConstruct::Expression
