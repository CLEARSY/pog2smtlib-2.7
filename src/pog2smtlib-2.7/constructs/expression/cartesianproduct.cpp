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

/*
; declaration - requisites: PxUV, PU, PV
(declare-fun |set.product U V| (|POW U| |POW V|) |POW (U x V)|)
; rewriting with triggers - requisites:
(assert (!
  (forall ((s1 |POW U|)) ((s2 |POW V|)) ((p |(U x V)|))
    (!
      (= (|set.in (U x V)| p (|set.product U V| s1 s2))
        (and (|set.in U| (fst p) s1) (|set.in V| (snd p) s2))
      :pattern ((|set.in U| (fst p) s1) (|set.in V| (snd p) s2))))
  :named |ax.set.product U V|))
; rewriting no triggers requisites:
(assert (!
  (forall ((s1 |POW U|)) ((s2 |POW V|)) ((p |(U x V)|))
    (= (|set.in (U x V)| p (|set.product U V| s1 s2))
      (and (|set.in U| (fst p) s1) (|set.in V| (snd p) s2))))
  :named |ax.set.product U V|))
; definition requisites : set.intent T :> set.in T, POW T
(define-fun |set.product U V| ((s1 |POW U|)(s2 |POW V|)) |POW (U x V)|
  (|set.intent (U x V)|
    (lambda ((p |(U x V)|))
      (and (|set.in U| (fst p) s1) (|set.in V| (snd p) s2)))))

pattern variables:
0: |set.product U V| => smtSymbol(Expr::BinaryOp::Cartesian_Product, U, V)
1: |POW U| => symbol(PU)
2: |POW V| => symbol(PV)
3: |POW (U x V)| => symbol(PxUV)
4: |(U x V)| => symbol(xUV)
5: |set.in (U x V)| => smtSymbol(Pred::ComparisonOp::Membership, xUV)
6: |set.in U| => smtSymbol(Pred::ComparisonOp::Membership, U)
7: |set.in V| => smtSymbol(Pred::ComparisonOp::Membership, V)
8: |set.intent (U x V)| => smtSymbol(Expr::NaryOp::Set, xUV)
9: |ax.set.product U V|
*/

static const string DECLARATION =
    R"((declare-fun {0} ({1} {2}) {3})
)";
static const string SCRIPT = R"((assert (!
  (forall ((U {1})(V {2})(p {4}))
    (= ({5} p ({0} U V))
      (and ({6} (fst p) U) ({7} (snd p) V))))
  :named {9}))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((U {1})(V {2})(p {4}))
    (!
      (= ({5} p ({0} U V))
        (and ({6} (fst p) U) ({7} (snd p) V)))
      :pattern (({5} p ({0} U V)))))
  :named {9}))
)";
/*
static const string DEFINITION = R"((define-fun {0} ((s1 {1})(s2 {2})) {3}
  ({8}
    (lambda ((p {4})) (and ({6} (fst p) s1) ({7} (snd p) s2)))))
)";
*/
namespace Expression {

MapBinaryBType<CartesianProduct> CartesianProduct::m_cache;

CartesianProduct::CartesianProduct(const BType &U, const BType &V,
                                   const string &script,
                                   const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "*") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::ExpressionCartesianProduct(const BType &U,
                                                         const BType &V) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::CartesianProduct::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto xUV = BType::PROD(U, V);
    const auto PxUV = BType::POW(xUV);
    const string arg0{smtSymbol(Expr::BinaryOp::Cartesian_Product, U, V)};
    const string arg1{symbol(PU)};
    const string arg2{symbol(PV)};
    const string arg3{symbol(PxUV)};
    const string arg4{symbol(xUV)};
    const string arg5{smtSymbol(Pred::ComparisonOp::Membership, xUV)};
    const string arg6{smtSymbol(Pred::ComparisonOp::Membership, U)};
    const string arg7{smtSymbol(Pred::ComparisonOp::Membership, V)};
    const string arg8{smtSymbol(Expr::NaryOp::Set, xUV)};
    const string arg9{fmt::format("|ax.set.product {0}|", symbolInner(xUV))};
    const std::string script =
        fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4, arg5, arg6,
                    arg7, arg8, arg9);
    const BConstruct::PreRequisites requisites{
        Factory::Type(PxUV),
        Factory::Type(PU),
        Factory::Type(PV),
        Factory::SetMembership(xUV),
    };
    result = make(BConstruct::Expression::CartesianProduct::m_cache, U, V,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
