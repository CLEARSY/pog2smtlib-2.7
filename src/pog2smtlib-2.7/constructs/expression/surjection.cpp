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
#include "surjection.h"

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
    R"((declare-fun |surjections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}))
    (forall ((f {5}))
      (= ({6} f (|surjections {0} {1}| X Y))
         (= ({7} f) Y)
      )))
  :named |ax:set.in.surjections {8}|))
)";

namespace Expression {

MapBinaryBType<Surjection> Surjection::m_cache;

Surjection::Surjection(const BType &U, const BType &V, const string &script,
                       set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "_surj") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Surjection(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Surjection::m_cache, U, V);
  if (!result) {

    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto xUV = BType::PROD(U, V);
    const auto PxUV = BType::POW(xUV);
    const auto PPxUV = BType::POW(PxUV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ symbolInner(U),
                    /*1*/ symbolInner(V),
                    /*2*/ symbol(PU),
                    /*3*/ symbol(PV),
                    /*4*/ symbol(PPxUV),
                    /*5*/ symbol(PxUV),
                    /*6*/ smtSymbol(Pred::ComparisonOp::Membership, PxUV),
                    /*7*/ smtSymbol(Expr::UnaryOp::Range, U, V),
                    /*8*/ symbolInner(xUV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(PxUV),
                                            Factory::Equality(PU),
                                            Factory::Range(U, V)};
    result = make(BConstruct::Expression::Surjection::m_cache, U, V, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct