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
#include "restrict_in_front.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2} {1}) {2})
(assert (!
  (forall ((s {2})(x {1})(p {3}))
    (= ({4} p ({0} s x))
       (and ({5} (fst p) ({6} 1 x))
            ({4} p s))))
  :named |ax.restrict.front.def {7}|))
)";

namespace Expression {

MapUnaryBType<Restrict_In_Front> Restrict_In_Front::m_cache;

Restrict_In_Front::Restrict_In_Front(const BType& T, const std::string& script,
                                     set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "↑") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Restrict_In_Front(const BType& T) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Restrict_In_Front::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Head_Restriction, T),
        /*1*/ symbol(BType::INT),
        /*2*/ symbol(PZxT),
        /*3*/ symbol(ZxT),
        /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
        /*6*/ smtSymbol(Expr::BinaryOp::Interval),
        /*7*/ symbolInner(T));
    set<shared_ptr<Abstract>> requisites = {
        Factory::SetMembership(ZxT),
        Factory::SetMembership(BType::INT),
        Factory::Interval(),
    };
    result = make(BConstruct::Expression::Restrict_In_Front::m_cache, T, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct
