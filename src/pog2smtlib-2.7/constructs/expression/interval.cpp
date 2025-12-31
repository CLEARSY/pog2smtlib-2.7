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
#include "interval.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {1}) {2})
 (assert (!
    (forall ((l {1}) (u {1}) (e {1}))
        (= ({3} e ({0} l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
)";

namespace Expression {

shared_ptr<Interval> Interval::m_cache;

Interval::Interval(const std::string& script, const PreRequisites& requisites)
    : Uniform(script, requisites, "..") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Interval() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Interval::m_cache);
  if (!result) {
    const auto& PZ = BType::POW(BType::INT);
    const string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Interval),
        /*1*/ symbol(BType::INT),
        /*2*/ symbol(PZ),
        /*3*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT));
    const PreRequisites requisites{Factory::SetMembership(BType::INT)};
    result =
        make(BConstruct::Expression::Interval::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
