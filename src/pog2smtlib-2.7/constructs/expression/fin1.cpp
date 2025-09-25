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
#include "fin1.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {2})
(assert (!
  (forall ((s {1}) (t {1}))
    (= ({3} s ({0} t))
       (and ({3} s ({6} t))
            (not  (= s {4})))))
  :named |ax.non empty finite sub-sets {5}|))
)";

namespace Expression {

MapUnaryBType<Fin1> Fin1::m_cache;

Fin1::Fin1(const BType& T, const string& script,
           set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "FIN1") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Fin1(const BType& T) {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Fin1::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto PPT = BType::POW(PT);
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Non_Empty_Finite_Subsets, T),
        /*1*/ symbol(PT),
        /*2*/ symbol(PPT),
        /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
        /*4*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, T),
        /*5*/ symbolInner(T),
        /*6*/ smtSymbol(Expr::UnaryOp::Finite_Subsets, T));
    set<shared_ptr<Abstract>> requisites = {
        Factory::EmptySet(T), Factory::Fin(T), Factory::SetMembership(PT)};
    result = make(BConstruct::Expression::Fin1::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct