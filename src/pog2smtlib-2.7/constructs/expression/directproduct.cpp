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
#include "directproduct.h"

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
  (forall ((R1 {1}) (R2 {2}) (p {4}))
    (= ({5} p ({0} R1 R2))
       (and
         ({6} (maplet (fst p) (fst (snd p))) R1)
         ({7} (maplet (fst p) (snd (snd p))) R2)
       )
    )
  )
  :named |ax.set.in.directproduct {8}|))
)";

namespace Expression {

MapTernaryBType<Direct_Product> Direct_Product::m_cache;

Direct_Product::Direct_Product(const BType &T, const BType &U, const BType &V,
                               const string &script,
                               set<shared_ptr<Abstract>> &requisites)
    : TernaryBType(T, U, V, script, requisites, "⊗") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Direct_Product(const BType &T, const BType &U,
                                             const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Direct_Product::m_cache, T, U, V);
  if (!result) {
    const auto xTU = BType::PROD(T, U);
    const auto xxTUV = BType::PROD(xTU, V);
    const auto PxTU = BType::POW(xTU);
    const auto xTV = BType::PROD(T, V);
    const auto PxTV = BType::POW(xTV);
    const auto xUV = BType::PROD(U, V);
    const auto xTxUV = BType::PROD(T, xUV);
    const auto PxTxUV = BType::POW(xTxUV);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Direct_Product, T, U, V),
        /*1*/ symbol(PxTU),
        /*2*/ symbol(PxTV),
        /*3*/ symbol(PxTxUV),
        /*4*/ symbol(xTxUV),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, xTxUV),
        /*6*/ smtSymbol(Pred::ComparisonOp::Membership, xTU),
        /*7*/ smtSymbol(Pred::ComparisonOp::Membership, xTV),
        /*8*/ symbolInner(xxTUV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(xTxUV),
                                            Factory::SetMembership(xTU),
                                            Factory::SetMembership(xTV)};
    result = make(BConstruct::Expression::Direct_Product::m_cache, T, U, V,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
