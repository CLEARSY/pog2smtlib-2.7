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
#include "rmax.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2}) {1})
(assert (!
  (forall ((s {2}))
    (=> (not (= s {3})) ({4} ({0} s) s)))
  :named |ax.rmax.is.member|))
(assert (!
  (forall ((s {2}))
    (forall ((e {1}))
      (=> ({4} e s) (<= e ({0} s)))))
    :named |ax.rmax.is.ge|))
)";

namespace Expression {

std::shared_ptr<RMax> RMax::m_cache;

RMax::RMax(const std::string &script, set<shared_ptr<Abstract>> &requisites)
    : Uniform(script, requisites, "rmax") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::RMax() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::RMax::m_cache);
  if (!result) {
    const string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::RMaximum),
        /*1*/ symbol(BType::REAL),
        /*2*/ symbol(BType::POW(BType::REAL)),
        /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::REAL),
        /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::REAL));
    set<shared_ptr<Abstract>> requisites{Factory::EmptySet(BType::REAL)};
    result = make(BConstruct::Expression::RMax::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
