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
#include "union.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "btype.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

/*
; declaration - requisites : POW T,
(declare-fun |set.union T| (|POW T| |POW T|) |POW T|)
; rewriting with triggers - requisites : set.in T, POW T
(assert (!
  (forall ((U |POW T|)) ((V |POW T|)) ((e |T|))
    (!
      (= (|set.in T| e (|set.union T| U V))
        (or (|set.in T| e U) (|set.in T| e V))
      :pattern ((|set.in T| e (|set.union T| U V)))))
  :named |ax.rw.union T|))
; rewriting no triggers requisites : set.in T
(assert (!
  (forall ((U |POW T|)) ((V |POW T|)) ((e |T|))
    (= (|set.in T| e (|set.union T| U V))
      (or (|set.in T| e U) (|set.in T| e V))))
  :named |ax.rw.union T|))
; definition requisites : set.intent T :> set.in T, POW T
(define-fun |set.union T| ((U |POW T|)(V |POW T|)) |POW T|
  (|set.intent T| (|lambda ((_c |T|) (or (|set.in T| _c U) (|set.in T| _c V)))))

pattern variables:
0: |set.union T| => smtSymbol(Expr::BinaryOp::Union, T)
1: |T| => symbol(T)
2: |POW T| =>symbol(PT)
3: |set.in T| => smtSymbol(Pred::ComparisonOp::Membership, T)
4: |set.intent T|
5: |ax.set.in.union T|
*/
static const string DECLARATION = R"((declare-fun {0} ({1} {1}) {1})
)";
static const string SCRIPT = R"((assert (!
  (forall ((e {3}) (s {1}) (t {1}))
    (= ({2} e ({0} s t))
       (or ({2} e s) ({2} e t))))
  :named {4}))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((e {3}) (s {1}) (t {1}))
    (= ({2} e ({0} s t))
       (or ({2} e s) ({2} e t)))
  :pattern (({2} e ({0} s t)))
  :named {4}))
)";

namespace Expression {

MapUnaryBType<Union> Union::m_cache;

Union::Union(const BType& T, const string& script,
             const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "\\/") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::Union(const BType& T) {
  static string script_pattern{};  // the script pattern is the same for all
                                   // types T (compute only once)
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Union::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const string arg0{smtSymbol(Expr::BinaryOp::Union, T)};
    const string arg1{symbol(PT)};
    const string arg2{smtSymbol(Pred::ComparisonOp::Membership, T)};
    const string arg3{symbol(T)};
    const string arg4{fmt::format("|ax.set.in.union {0}|", symbolInner(T))};
    const string script =
        fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4);
    const BConstruct::PreRequisites requisites{Factory::SetMembership(T)};
    result =
        make(BConstruct::Expression::Union::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
