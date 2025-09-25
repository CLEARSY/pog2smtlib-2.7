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
#include "totalinjections.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"
#include "functionstotal.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {3})
(assert (!
  (forall ((e1 {1}) (e2 {2}))
    (forall ((f {4}))
      (= ({5} f ({0} e1 e2))
         (and ({5} f ({9} e1 e2))
              ({5} f (|injections {6} {7}| e1 e2))))))
 :named |ax:def.tinj {8}|))
)";

namespace Expression {

MapBinaryBType<Total_Injection> Total_Injection::m_cache;

Total_Injection::Total_Injection(const BType &U, const BType &V,
                                 const string &script,
                                 set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, ">->") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Total_Injection(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Total_Injection::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const auto PPUxV = BType::POW(PUxV);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Total_Injections, U, V),
        /*1*/ symbol(PU),
        /*2*/ symbol(PV),
        /*3*/ symbol(PPUxV),
        /*4*/ symbol(PUxV),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, PUxV),
        /*6*/ symbolInner(U),
        /*7*/ symbolInner(V),
        /*8*/ symbolInner(UxV),
        /*9*/ smtSymbol(Expr::BinaryOp::Total_Functions, U, V));
    set<shared_ptr<Abstract>> requisites = {Factory::Total_Function(U, V),
                                            Factory::Injection(U, V)};
    result = make(BConstruct::Expression::Total_Injection::m_cache, U, V,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
