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
#include "minint.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "../type/type.h"
#include "btype.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((define-const {0} {1} {2})
)";

namespace Expression {

shared_ptr<Minint> Minint::m_cache;

Minint::Minint(const std::string &script, const PreRequisites &requisites)
    : Uniform(script, requisites, "MININT") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Minint() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Minint::m_cache);
  if (!result) {
    std::string smtLiteral;
    if (Parameters::MININT.at(0) == '-') {
      smtLiteral = fmt::format("(- {})", Parameters::MININT.substr(
                                             1, Parameters::MININT.size() - 1));
    } else {
      smtLiteral = Parameters::MININT;
    }
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::Visitor::EConstant::MinInt),
                    /*1*/ symbol(BType::INT),
                    /*2*/ smtLiteral);
    const PreRequisites requisites{Factory::Type(BType::INT)};
    result = make(BConstruct::Expression::Minint::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
