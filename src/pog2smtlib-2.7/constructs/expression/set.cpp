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
#include "set.h"

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
; sort
(define-sort |? T| () (-> |T| Bool))
; declaration - requisites : POW T,
(declare-fun |set.intent T| (|? T|) |POW T|)
; rewriting with triggers - requisites:
(assert (!
  (forall ((p |? T|) (x |T|)) (!
    (= (|set.in T| x (|set.intent T| p))
      (p x))
    :pattern ((|set.in T| x (|set.intent T| p)))))
  :named |ax:rw.intent T|))
; rewriting no triggers requisites:
(assert (!
  (forall ((p |? T|) (x |T|))
    (= (|set.in T| x (|set.intent T| p))
      (p x))))
  :named |ax.rw.intent T|))
; this construct cannot be given a definitional semantics.

pattern variables:
0: T => symbolInner(T)
1: |T| => symbol(T)
2: |set.intent T| => smtSymbol(Expr::NaryOp::Set, T)
3: |POW T| =>symbol(PT)
4: |set.in T| => smtSymbol(Pred::ComparisonOp::Membership, T)
5: |ax.rw.intent T|
*/

static const string SORT =
    R"((define-sort |? {0}| () (-> {1} Bool))
)";
static const string DECLARATION =
    R"((declare-const {2} (-> |? {0}| {3}))
)";
static const string SCRIPT = R"((assert (!
  (forall ((p |? {0}|))
    (forall ((x {1}))
      (= ({4} x ({2} p))
         (@ p x))))
  :named |ax:set.in.intent {0}|))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((p |? {0}|) (x {1})) (!
    (= ({4} x ({2} p))
      (p x))
    :pattern (({4} x ({2} p)))))
  :named {5}))
)";
namespace Expression {

MapUnaryBType<Set> Set::m_cache;

Set::Set(const BType& T, const string& script, const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "_set") {}

}  // namespace Expression

std::shared_ptr<Abstract> Factory::Set(const BType& T) {
  string script_pattern{};
  if (script_pattern.empty()) {
    script_pattern.append(SORT);
    script_pattern.append(DECLARATION);
    if (Parameters::encodingOptions.axiomTriggers) {
      script_pattern.append(SCRIPT_T);
    } else {
      script_pattern.append(SCRIPT);
    }
  }
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Set::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const string arg0{symbolInner(T)};
    const string arg1{symbol(T)};
    const string arg2{smtSymbol(Expr::NaryOp::Set, T)};
    const string arg3{symbol(PT)};
    const string arg4{smtSymbol(Pred::ComparisonOp::Membership, T)};
    const string arg5{fmt::format("|ax.rw.intent {0}|", arg0)};
    const string script =
        fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4, arg5);
    const PreRequisites requisites{Factory::SetMembership(T)};
    result = make(BConstruct::Expression::Set::m_cache, T, script, requisites);
  }
  return result;
}

}  // namespace BConstruct
