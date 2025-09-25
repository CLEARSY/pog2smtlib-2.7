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
#include "bijection.h"

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
    R"((declare-fun |bijections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}))
    (forall ((f {5}))
      (= ({6} f (|bijections {0} {1}| X Y))
         (and ({6} f (|injections {0} {1}| X Y))
              ({6} f (|surjections {0} {1}| X Y))))))
  :named |ax:set.in.bijections {7}|))
)";

namespace Expression {

MapBinaryBType<Bijection> Bijection::m_cache;

Bijection::Bijection(const BType &U, const BType &V, const string &script,
                     set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "_bij") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Bijection(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Bijection::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const auto PPUxV = BType::POW(PUxV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ symbolInner(U),
                    /*1*/ symbolInner(V),
                    /*2*/ symbol(PU),
                    /*3*/ symbol(PV),
                    /*4*/ symbol(PPUxV),
                    /*5*/ symbol(PUxV),
                    /*6*/ smtSymbol(Pred::ComparisonOp::Membership, PUxV),
                    /*7*/ symbolInner(UxV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(PUxV),
                                            Factory::Injection(U, V),
                                            Factory::Surjection(U, V)};
    result = make(BConstruct::Expression::Bijection::m_cache, U, V, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct
