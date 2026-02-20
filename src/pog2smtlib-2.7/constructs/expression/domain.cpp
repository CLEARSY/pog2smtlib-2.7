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
#include "domain.h"

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
; declaration - requisites: PxUV, PU
(declare-fun |rel.domain U V| (|POW (U x V)|) |POW U|)
; rewriting with triggers - requisites:
(assert (!
  (forall ((r |POW (U x V)|) (e |U|)) (!
    (= (|set.in U| e (|rel.domain U V| r))
       (exists ((y |V|)) (|set.in (U x V)| (maplet e y) r)))
    :pattern ((|set.in U| e (|rel.domain U V| r)))))
  :named |ax.rw.domain U V|))
; rewriting no triggers requisites: |set.in (U x V)| > |set.in U|
(assert (!
  (forall ((r |POW (U x V)|) (e |U|))
    (= (|set.in U| e (|rel.domain U V| r))
       (exists ((y |V|)) (|set.in (U x V)| (maplet e y) r))))
  :named |ax.rw.domain U V|))
; definition requisites : set.intent T :> set.in T, POW T
(define-fun |rel.domain U V| ((r |POW (U x V)|)) |POW U|
  (|set.intent U|
    (lambda ((x |U|))
      (exists ((y |V|)) (|set.in (U x V)| (maplet e y) r)))))

pattern variables:
0: |rel.domain U V| =>
1: |POW (U x V)| => symbol(PxUV)
2: |POW U| => symbol(PU)
3: |set.in U| => smtSymbol(Pred::ComparisonOp::Membership, U)
4: |U| => symbol(U)
5: |V| => symbol(V)
6: |set.in (U x V)| => smtSymbol(Pred::ComparisonOp::Membership, xUV)
7: |set.intent U| => smtSymbol(Expr::NaryOp::Set, U)
8: |ax.rw.domain U V|

*/

static const std::string_view DECLARATION = R"((declare-fun {0} ({1}) {2})
)";
static const std::string_view SCRIPT = R"((assert (!
  (forall ((r {1}) (e {4}))
    (= ({3} e ({0} r))
       (exists ((y {5})) ({6} (maplet e y) r))))
  :named {8}))
)";
static const std::string_view SCRIPT_T = R"((assert (!
  (forall ((r {1}) (e {4})) (!
    (= ({3} e ({0} r))
       (exists ((y {5})) ({6} (maplet e y) r)))
    :pattern (({3} e ({0} r)))))
  :named {8}))
)";

namespace Expression {

MapBinaryBType<Domain> Domain::m_cache;

Domain::Domain(const BType &U, const BType &V, const std::string &script,
               const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "dom") {}
};  // namespace Expression

shared_ptr<Abstract> Factory::Domain(const BType &U, const BType &V) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Domain::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto xUV = BType::PROD(U, V);
    const auto PxUV = BType::POW(xUV);
    const string arg0{smtSymbol(Expr::UnaryOp::Domain, U, V)};
    const string arg1{symbol(PxUV)};
    const string arg2{symbol(PU)};
    const string arg3{smtSymbol(Pred::ComparisonOp::Membership, U)};
    const string arg4{symbol(U)};
    const string arg5{symbol(V)};
    const string arg6{smtSymbol(Pred::ComparisonOp::Membership, xUV)};
    const string arg7{smtSymbol(Expr::NaryOp::Set, U)};
    const string arg8{fmt::format("|ax:set.in.domain {0}|", symbolInner(xUV))};
    const std::string script = fmt::format(script_pattern, arg0, arg1, arg2,
                                           arg3, arg4, arg5, arg6, arg7, arg8);
    const BConstruct::PreRequisites requisites{Factory::SetMembership(xUV),
                                               Factory::SetMembership(U)};
    result =
        make(BConstruct::Expression::Domain::m_cache, U, V, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
