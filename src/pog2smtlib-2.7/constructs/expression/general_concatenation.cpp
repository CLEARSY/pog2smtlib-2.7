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
(declare-fun {0} ({1}) {2})
(assert (!
  (= ({0} |seq.empty {3}|) |seq.empty {6}|)
  :named |ax.generalized.concatenation.empty {6}|
))
(assert (!
  (forall ((s {1})(x {2}))
    (= ({0} ({4} x s))
       ({5} x ({0} s))))
  :named |ax.generalized.concatenation.not.empty {6}|
))
)";

General_Concatenation::General_Concatenation(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  const auto ZxPZxT = BType::PROD(BType::INT, PZxT);
  const auto PZxPZxT = BType::POW(ZxPZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Concatenation, T),
                         /*1*/ symbol(PZxPZxT),
                         /*2*/ symbol(PZxT),
                         /*3*/ symbolInner(PZxT),
                         /*4*/ smtSymbol(Expr::BinaryOp::Head_Insertion, PZxT),
                         /*5*/ smtSymbol(Expr::BinaryOp::Concatenation, T),
                         /*6*/ symbolInner(T));
  m_label = "conc";
  m_prerequisites.insert({
      std::make_shared<BConstruct::Expression::Insert_In_Front>(PZxT),
      std::make_shared<BConstruct::Expression::Concatenation>(T),
      std::make_shared<BConstruct::Expression::EmptySeq>(PZxT),
      std::make_shared<BConstruct::Expression::EmptySeq>(T),
  });
  m_debug_string = fmt::format("conc_{}", T.to_string());
}

};  // namespace BConstruct::Expression
