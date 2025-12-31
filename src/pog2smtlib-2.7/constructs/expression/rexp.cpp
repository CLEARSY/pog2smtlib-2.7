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
#include "rexp.h"

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

static constexpr std::string_view SCRIPT =
    R"((define-fun-rec {0} ((n {1}) (p {2})) {1}
  (ite (= p 0)
    1.0
    (ite (> p 0)
      (* n ({0} n (- p 1)))
      0.0)))
)";

namespace Expression {

std::shared_ptr<RExponentiation> RExponentiation::m_cache;

RExponentiation::RExponentiation(const std::string &script,
                                 const PreRequisites &requisites)
    : Uniform(script, requisites, "**r") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::RExponentiation() {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::RExponentiation::m_cache);
  if (!result) {
    const string script =
        fmt::format(SCRIPT, smtSymbol(Expr::BinaryOp::RExponentiation),
                    symbol(BType::REAL), symbol(BType::INT));
    const PreRequisites requisites{Factory::Type(BType::INT),
                                   Factory::Type(BType::INT),
                                   Factory::Type(BType::REAL)};
    result = make(BConstruct::Expression::RExponentiation::m_cache, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
