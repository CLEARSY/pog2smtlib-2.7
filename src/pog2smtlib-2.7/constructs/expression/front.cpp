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
#include "front.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT =
    R"((define-fun {0} ((s {1})) {1} ({2} s (- ({3} s) 1)))
)";

namespace Expression {

MapUnaryBType<Front> Front::m_cache;

Front::Front(const BType& T, const std::string& script,
             set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "front") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Front(const BType& T) {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Front::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Front, T),
                    /*1*/ symbol(PZxT),
                    /*2*/ smtSymbol(Expr::BinaryOp::Head_Restriction, T),
                    /*3*/ smtSymbol(Expr::UnaryOp::Size, T));
    set<shared_ptr<Abstract>> requisites = {Factory::Size(T),
                                            Factory::Restrict_In_Front(T)};
    result =
        make(BConstruct::Expression::Front::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
