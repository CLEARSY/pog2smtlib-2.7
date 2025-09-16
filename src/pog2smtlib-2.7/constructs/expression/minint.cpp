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

static constexpr std::string_view SCRIPT = R"((define-const {0} {1} {2})
)";

Minint::Minint() {
  std::string smtLiteral;
  if (Parameters::MININT.at(0) == '-') {
    smtLiteral = fmt::format(
        "(- {})", Parameters::MININT.substr(1, Parameters::MININT.size() - 1));
  } else {
    smtLiteral = Parameters::MININT;
  }

  m_script = fmt::format(SCRIPT, smtSymbol(Expr::Visitor::EConstant::MinInt),
                         symbol(BType::INT), smtLiteral);
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Type::Type>(BType::INT)});
  m_label = "MININT";
  m_debug_string = "MININT";
}
};  // namespace BConstruct::Expression
