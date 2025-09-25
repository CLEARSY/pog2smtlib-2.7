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
#include "composition.h"

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
  (forall ((r {1}) (s {2}) (p {4}))
    (= ({5} p ({0} r s))
       (exists ((y {6}))
         (and
           ({7} (maplet (fst p) y) r)
           ({8} (maplet y (snd p)) s)))))
  :named |ax.set.in.relcomp {9}|))
)";

namespace Expression {

MapTernaryBType<Composition> Composition::m_cache;

Composition::Composition(const BType &T, const BType &U, const BType &V,
                         const string &script,
                         set<shared_ptr<Abstract>> &requisites)
    : TernaryBType(T, U, V, script, requisites, ";") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Composition(const BType &T, const BType &U,
                                          const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Composition::m_cache, T, U, V);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto TxU = BType::PROD(T, U);
    const auto PTxU = BType::POW(TxU);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const auto TxV = BType::PROD(T, V);
    const auto PTxV = BType::POW(TxV);
    const auto TxUxV = BType::PROD(TxU, V);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Composition, T, U, V),
        /*1*/ symbol(PTxU),
        /*2*/ symbol(PUxV),
        /*3*/ symbol(PTxV),
        /*4*/ symbol(TxV),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, TxV),
        /*6*/ symbol(U),
        /*7*/ smtSymbol(Pred::ComparisonOp::Membership, TxU),
        /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
        /*9*/ symbolInner(TxUxV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(TxU),
                                            Factory::SetMembership(TxV),
                                            Factory::SetMembership(UxV)};
    result = make(BConstruct::Expression::Composition::m_cache, T, U, V, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
