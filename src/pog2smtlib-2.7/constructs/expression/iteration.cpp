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
(declare-fun {0} ({1} {2}) {1})
(assert (!
  (forall ((R {1})) (= ({0} R 1) R))
  :named |ax.set.iterate.1 {4}|))
(assert (!
  (forall ((R {1})(n {2}))
    (= ({0} R (+ n 1)) ({3} R ({0} R n))))
  :named |ax.set.iterate.n+1 {4}|))
)";

Iteration::Iteration(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Iteration, T),
                         /*1*/ symbol(PTxT),
                         /*2*/ symbol(BType::INT),
                         /*3*/ smtSymbol(Expr::BinaryOp::Composition, T, T, T),
                         /*4*/ symbolInner(BType::INT));
  m_label = "iterate";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Composition>(T, T, T)});
  m_debug_string = fmt::format("iterate_{}", T.to_string());
}

};  // namespace BConstruct::Expression
