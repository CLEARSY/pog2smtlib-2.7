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
#include "cartesianproduct.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {3})
(assert (!
  (forall ((s1 {1}) (s2 {2}))
    (forall ((p {4}))
      (= ({5} p ({0} s1 s2))
        (and ({6} (fst p) s1) ({7} (snd p) s2)))))
  :named |ax.set.in.product.1 {8}|))
(assert (!
  (forall ((s1 {1}) (s2 {2}))
    (forall ((x1 {9}) (x2 {10}))
      (= ({5} (maplet x1 x2) ({0} s1 s2))
        (and ({6} x1 s1) ({7} x2 s2)))))
  :named |ax.set.in.product.2 {8}|))
)";

namespace Expression {

MapBinaryBType<CartesianProduct> CartesianProduct::m_cache;

CartesianProduct::CartesianProduct(const BType &U, const BType &V,
                                   const string &script,
                                   set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "*") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::ExpressionCartesianProduct(const BType &U,
                                                         const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::CartesianProduct::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Cartesian_Product, U, V),
        /*1*/ symbol(PU),
        /*2*/ symbol(PV),
        /*3*/ symbol(PUxV),
        /*4*/ symbol(UxV),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
        /*6*/ smtSymbol(Pred::ComparisonOp::Membership, U),
        /*7*/ smtSymbol(Pred::ComparisonOp::Membership, V),
        /*8*/ symbolInner(UxV),
        /*9*/ symbol(U),
        /*10*/ symbol(V));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(UxV)};
    result = make(BConstruct::Expression::CartesianProduct::m_cache, U, V,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
