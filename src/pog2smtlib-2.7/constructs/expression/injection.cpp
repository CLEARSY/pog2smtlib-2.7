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
#include "injection.h"

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
    R"((declare-fun |injections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}) (f {5}))
     (= ({6} f (|injections {0} {1}| X Y))
        (forall ((p {7}) (q {7}))
          (=> (and ({8} p f) ({8} q f) (= (snd p) (snd q)))
              (= (fst p) (fst q))))))
  :named |ax:set.in.injections {9}|))
)";

namespace Expression {

MapBinaryBType<Injection> Injection::m_cache;

Injection::Injection(const BType &U, const BType &V, const string &script,
                     const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "_inj") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Injection(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Injection::m_cache, U, V);
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
                    /*7*/ symbol(UxV),
                    /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                    /*9*/ symbolInner(UxV));
    PreRequisites requisites = {Factory::SetMembership(PUxV),
                                Factory::Equality(U), Factory::Equality(V)};
    result = make(BConstruct::Expression::Injection::m_cache, U, V, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
