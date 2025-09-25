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
#include "maxint.h"

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

shared_ptr<Maxint> Maxint::m_cache;

Maxint::Maxint(const std::string &script, set<shared_ptr<Abstract>> &requisites)
    : Uniform(script, requisites, "MAXINT") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Maxint() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Maxint::m_cache);
  if (!result) {
    const string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::Visitor::EConstant::MaxInt),
                    /*1*/ symbol(BType::INT), /*2*/ Parameters::MAXINT);
    set<shared_ptr<Abstract>> requisites{Factory::Type(BType::INT)};
    result = make(BConstruct::Expression::Maxint::m_cache, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
