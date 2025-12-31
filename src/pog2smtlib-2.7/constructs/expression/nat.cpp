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
#include "nat.h"

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

static constexpr std::string_view SCRIPT = R"((declare-const {0} {2})
(assert (!
  (forall ((e {1})) (= ({3} e {0}) (and (<= 0 e) (<= e {4}))))
  :named |ax.set.in.NAT|))
)";

namespace Expression {

std::shared_ptr<Nat> Nat::m_cache;

Nat::Nat(const std::string &script, const PreRequisites &requisites)
    : Uniform(script, requisites, "NAT") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Nat() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Nat::m_cache);
  if (!result) {
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::Visitor::EConstant::NAT),
                    /*1*/ symbol(BType::INT),
                    /*2*/ symbol(BType::POW(BType::INT)),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
                    /*4*/ smtSymbol(Expr::Visitor::EConstant::MaxInt));
    const PreRequisites requisites{Factory::SetMembership(BType::INT),
                                   Factory::Maxint()};
    result = make(BConstruct::Expression::Nat::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
