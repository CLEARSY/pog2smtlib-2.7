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

static constexpr std::string_view SCRIPT =
    R"((define-fun {0} ((s {1})) {1} ({2} s (- ({3} s) 1)))
)";

Front::Front(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Front, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ smtSymbol(Expr::BinaryOp::Head_Restriction, T),
                         /*3*/ smtSymbol(Expr::UnaryOp::Size, T));
  m_label = "front";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Size>(T),
       std::make_shared<BConstruct::Expression::Restrict_In_Front>(T)});
  m_debug_string = fmt::format("front_{}", T.to_string());
}

};  // namespace BConstruct::Expression
