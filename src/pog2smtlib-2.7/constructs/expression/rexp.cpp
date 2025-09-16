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
    R"((define-fun-rec {0} ((n {1}) (p {2})) {1}
 (ite (= p 0)
    1.0
    (ite (> p 0)
        (* n ({0} n (- p 1)))
        0.0))
 )
 )";

RExponentiation::RExponentiation() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::BinaryOp::RExponentiation),
                         symbol(BType::REAL), symbol(BType::INT));
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Type::Type>(BType::INT),
       std::make_shared<BConstruct::Type::Type>(BType::REAL)});
  m_label = "**r";
  m_debug_string = "**r";
}
};  // namespace BConstruct::Expression
