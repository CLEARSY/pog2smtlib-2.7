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
#include "emptyset.h"

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
(declare-const |set.empty T| |POW T|)
; rewriting with triggers - requisites : set.in T
(assert (!
  (forall ((e |T|))
    (!
      (not (|set.in T| e |set.empty T|))
      :pattern ((|set.in T| e |set.empty T|))
    ))
  :named |ax.set.in.empty T|))
; rewriting no triggers requisites : set.in T
(assert (!
  (forall ((e |T|)) (not (|set.in T| e |set.empty T|)))
  :named |ax.set.in.empty T|))
; definition requisites : set.intent T
(define-fun |set.empty T| () |P T| (|set.intent T| (|lambda ((_c |T|) false)))

pattern variables:
0: |set.empty T| => smtSymbol(Expr::Visitor::EConstant::EmptySet, T)
1: |T| => symbol(T)
2: |POW T| =>symbol(PT)
3: |set.in T| => smtSymbol(Pred::ComparisonOp::Membership, T)
4: |set.intent T| => smtSymbol(Expr::NaryOp::Set, T)
5: |ax.set.in.empty T|
*/

static const string DECLARATION = R"((declare-const {0} {2})
)";
static const string SCRIPT = R"((assert (!
  (forall ((e {1})) (not ({3} e {0})))
  :named {5}))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((e {1})) (!
    (not ({3} e {0}))
    :pattern (({3} e {0}))))
  :named {5}))
)";
/*
static const string DEFINITION = R"((define-fun {0} () {2}
  ({4} (lambda ((_c {1})) false)))
)";
*/
namespace Expression {

MapUnaryBType<EmptySet> EmptySet::m_cache;

EmptySet::EmptySet(const BType& T, const string& script,
                   const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "{}") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::EmptySet(const BType& T) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::EmptySet::m_cache, T);
  if (!result) {
    const BType PT = BType::POW(T);
    const string script =
        fmt::format(script_pattern,
                    /*0*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, T),
                    /*1*/ symbol(T),
                    /*2*/ symbol(PT),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                    /*4*/ smtSymbol(Expr::NaryOp::Set, T),
                    /*5*/ fmt::format("|ax.set.in.empty {0}|", symbolInner(T)));
    const BConstruct::PreRequisites requisites{Factory::SetMembership(T)};
    result =
        make(BConstruct::Expression::EmptySet::m_cache, T, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
