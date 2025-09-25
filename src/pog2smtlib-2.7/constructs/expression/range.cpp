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
#include "range.h"

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
  (forall ((r {2}) (e |{6}|))
    (= ({3} e ({0} r))
       (exists ((x |{7}|)) ({4} (maplet x e) r))))
  :named |ax:set.in.range {5}|))
)";

namespace Expression {

MapBinaryBType<Range> Range::m_cache;

Range::Range(const BType &U, const BType &V, const string &script,
             set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "ran") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Range(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Range::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Range, U, V),
                    /*1*/ symbol(PV),
                    /*2*/ symbol(PUxV),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                    /*5*/ symbolInner(UxV),
                    /*6*/ symbolInner(V),
                    /*7*/ symbolInner(U));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(UxV)};
    result =
        make(BConstruct::Expression::Range::m_cache, U, V, script, requisites);
  }
  return result;
}

};  // namespace BConstruct