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
#include <fmt/core.h>

#include <string>

using std::string;

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

/*
; declaration - requisites : POW T,
(declare-const TYPE |POW T|)
; rewriting with triggers - requisites : set.in T
(assert (!
  (forall ((e |T|))
    (! (|set.in T| e TYPE)
      :pattern ((|set.in T| e TYPE))))
  :named |ax.rw.universe T|))
; rewriting no triggers requisites : set.in T
(assert (!
  (forall ((e |T|))
    (|set.in T| e TYPE))
  :named |ax.rw.universe T|))
; definition requisites : set.intent T
(define-fun TYPE () |POW T|
  (|set.intent T| (|lambda ((_c |T|) true)))

pattern variables:
0: TYPE => name
1: |T| => symbol(T)
2: |POW T| => symbol(PT)
3: |set.in T| => smtSymbol(Pred::ComparisonOp::Membership, T)
4: |set.intent T| => smtSymbol(Expr::NaryOp::Set, T)
5: |ax.rw.universe T|
*/
static const string DECLARATION = R"((declare-const {0} {2})
)";
static const string SCRIPT = R"((assert (!
  (forall ((e {1}))
    ({3} e {0}))
  :named {5}))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((e {1}))
    (! ({3} e {0})
      :pattern (({3} e {0}))))
  :named {5}))
)";
/*
static const string DEFINITION =
    R"((define-fun {0} () {2}
  ({4} (lambda ((_c {1})) true)))
)";
*/

std::string universeScript(const std::string& name, const BType& T) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  const auto PT = BType::POW(T);
  const string& arg0{name};
  const string arg1{symbol(T)};
  const string arg2{symbol(PT)};
  const string arg3{smtSymbol(Pred::ComparisonOp::Membership, T)};
  const string arg4{smtSymbol(Expr::NaryOp::Set, T)};
  const string arg5{fmt::format("|ax.rw.universe {0}|", symbolInner(T))};

  // BType ptype = BType::POW(type);
  return fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4, arg5);
}
};  // namespace BConstruct::Expression