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
#include "interval.h"

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
; declaration - requisites : POW Z,
(declare-fun |interval| (|Z| |Z|) |POW Z|)
; rewriting with triggers - requisites : set.in Z
(assert (!
  (forall ((l |Z|)(u |Z|)(e |Z|))
    (!
      (= (|set.in Z| e (|interval| u t))
        (and (<= l e) (<= e u)))
      :pattern ((|set.in Z| e (|interval| u t)))
    ))
  :named |ax.set.in.interval|))
; rewriting no triggers requisites : set.in T
(assert (!
  (forall ((l |Z|)(u |Z|)(e |Z|))
    (= (|set.in Z| e (|interval| u t))
        (and (<= l e) (<= e u)))))
  :named |ax.set.in.interval|))
; definition requisites : set.intent T
(define-fun |interval| ((l |Z|) (u |Z|)) |POW Z|
  (|set.intent Z| (|lambda ((e |Z|) (and (<= l e) (<= e u)))))

pattern variables:
0: |interval| => smtSymbol(Expr::BinaryOp::Interval)
1: |Z| => symbol(BType::INT)
2: |POW Z| =>symbol(BType::POW(BType::INT))
3: |set.in Z| => smtSymbol(Pred::ComparisonOp::Membership, symbol(BType::INT))
4: |set.intent Z|
5: |ax.set.in.interval|
*/

static constexpr std::string_view DECLARATION =
    R"((declare-fun {0} ({1} {1}) {2})
)";
static constexpr std::string_view SCRIPT_T = R"((assert (!
  (forall ((l {1})(u {1})(e {1})) (!
    (= ({3} e ({0} l u))
      (and (<= l e) (<= e u)))
    :pattern (({3} e ({0} l u)))))
  :named {5}))
)";
static constexpr std::string_view SCRIPT = R"((assert (!
  (forall ((l {1})(u {1})(e {1}))
    (= ({3} e ({0} l u))
      (and (<= l e) (<= e u))))
  :named {5}))
)";
/*
static const string DEFINITION = R"((define-fun {0} ((l {1}) (u {1})) {2}
  ({4} (lambda ((e {1})) (and (<= l e) (<= e u)))))
)";
*/

namespace Expression {

shared_ptr<Interval> Interval::m_cache;

Interval::Interval(const std::string& script, const PreRequisites& requisites)
    : Uniform(script, requisites, "..") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Interval() {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  shared_ptr<Abstract> result = find(BConstruct::Expression::Interval::m_cache);
  if (!result) {
    const auto& Z = BType::INT;
    const auto& PZ = BType::POW(Z);
    const string arg0{smtSymbol(Expr::BinaryOp::Interval)};
    const string arg1{symbol(Z)};
    const string arg2{symbol(PZ)};
    const string arg3{smtSymbol(Pred::ComparisonOp::Membership, Z)};
    const string arg4{smtSymbol(Expr::NaryOp::Set, Z)};
    const string arg5{"|ax.set.in.interval|"};
    const string script =
        fmt::format(script_pattern, arg0, arg1, arg2, arg3, arg4, arg5);
    PreRequisites requisites{Factory::SetMembership(Z)};
    result =
        make(BConstruct::Expression::Interval::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
