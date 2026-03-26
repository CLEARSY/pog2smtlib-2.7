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
#include "diff.h"

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
; declaration - requisites : POW T,
(declare-fun |set.diff T| (|POW T| |POW T|) |POW T|)
; rewriting with triggers - requisites : set.in T, POW T
(assert (!
  (forall ((U |POW T|)) ((V |POW T|)) ((e |T|))
    (!
      (= (|set.in T| e (|set.diff T| U V))
        (and (|set.in T| e U) (not (|set.in T| e V)))
      :pattern ((|set.in T| e (|set.diff T| U V)))))
  :named |ax.rw.diff T|))
; rewriting no triggers requisites : set.in T
(assert (!
  (forall ((U |POW T|)) ((V |POW T|)) ((e |T|))
    (= (|set.in T| e (|set.diff T| U V))
      (and (|set.in T| e U) (not (|set.in T| e V)))))
  :named |ax.rw.diff T|))
; definition requisites : set.intent T :> set.in T, POW T
(define-fun |set.diff T| ((U |POW T|)(V |POW T|)) |POW T|
  (|set.intent T| (|lambda ((_c |T|) (and (|set.in T| _c U) (not (|set.in T| _c
V))))))

pattern variables:
0: |set.diff T| => smtSymbol(Expr::BinaryOp::Set_Difference, T)
1: |T| => symbol(T)
2: |POW T| =>symbol(PT)
3: |set.in T| => smtSymbol(Pred::ComparisonOp::Membership, T)
4: |set.intent T|
5: |ax.rw.diff T|
*/
static const std::string_view DECLARATION =
    R"((declare-fun {0} ({2} {2}) {2})
)";
static const std::string_view SCRIPT = R"((assert (!
  (forall ((e {1}) (s {2}) (t {2}))
    (= ({3} e ({0} s t))
       (and ({3} e s) (not ({3} e t)))))
  :named {4}))
)";
static const std::string_view SCRIPT_T = R"((assert (!
  (forall ((e {1}) (s {2}) (t {2})) (!
    (= ({3} e ({0} s t))
       (and ({3} e s) (not ({3} e t)))))
    :pattern ( ({3} e ({0} s t) )))
  :named {4}))
)";
/*
static const string DEFINITION =
    R"((define-fun {0} ((U {2})(V {2})) {2}
  ({4} (lambda ((_c {1})) (and ({3} _c U) (not ({3} _c V))))))
)";
*/
namespace Expression {

MapUnaryBType<Difference> Difference::m_cache;

Difference::Difference(const BType& T, const string& script,
                       const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "-") {}

}  // namespace Expression

std::shared_ptr<Abstract> Factory::Difference(const BType& T) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Difference::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const string arg0{smtSymbol(Expr::BinaryOp::Set_Difference, T)};
    const string arg1{symbol(T)};
    const string arg2{symbol(PT)};
    const string arg3{smtSymbol(Pred::ComparisonOp::Membership, T)};
    const string arg4{fmt::format("|ax.set.in.diff {0}|", symbolInner(T))};
    const string script =
        fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4);
    const BConstruct::PreRequisites requisites{Factory::SetMembership(T)};
    result = make(BConstruct::Expression::Difference::m_cache, T, script,
                  requisites);
  }
  return result;
}

}  // namespace BConstruct
