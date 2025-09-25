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
#include "restriction_domain.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2} {1}) {1})
(assert (!
  (forall ((r {1}) (e {2}))
    (forall ((x {3}))
      (= ({4} x ({0} e r))
        (and ({4} x r) ({5} (fst x) e)))))
  :named |ax:set.in.restrict.dom {6}|))
)";

namespace Expression {

MapBinaryBType<Restriction_Domain> Restriction_Domain::m_cache;

Restriction_Domain::Restriction_Domain(const BType &U, const BType &V,
                                       const string &script,
                                       set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "◁") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Restriction_Domain(const BType &U,
                                                 const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Restriction_Domain::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Domain_Restriction, U, V),
        /*1*/ symbol(PUxV),
        /*2*/ symbol(PU),
        /*3*/ symbol(UxV),
        /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, U),
        /*6*/ symbolInner(UxV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(UxV)};
    result = make(BConstruct::Expression::Restriction_Domain::m_cache, U, V,
                  script, requisites);
  }
  return result;
}
};  // namespace BConstruct