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
#include "inclusion.h"

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
string pattern positional parameters:
0 : smtSymbol(Pred::ComparisonOp::Subset, T),
1 : symbol(PT),
2 : symbolInner(T)
3 : smtSymbol(Pred::ComparisonOp::Membership, T)
4 : symbol(T)
*/
static const string DECLARATION =
    R"((declare-fun {0} ({1} {1}) Bool)
)";

static const string SCRIPT = R"((assert (!
  (forall ((s {1}) (t {1}) (e {4}))
    (=>
      (and ({0} s t) ({3} e s))
      ({3} e t)))
  :named |ax.set.subseteq.elim {2}|))
(assert (!
  (forall ((s {1}) (t {1}))
    (=>
      (forall ((e {4})) (=> ({3} e s) ({3} e t)))
      ({0} s t)))
  :named |ax.set.subseteq.intro {2}|))
)";

static const string SCRIPT_T = R"((assert (!
  (forall ((s {1}) (t {1}) (e {4}))
    (!
      (=>
        (and ({0} s t) ({3} e s))
        ({3} e t))
    :pattern (({0} s t) ({3} e s))))
  :named |ax.set.subseteq.elim {2}|))
(assert (!
  (forall ((s {1}) (t {1}))
    (=>
      (forall ((e {4})) (=> ({3} e s) ({3} e t)))
      ({0} s t)))
  :named |ax.set.subseteq.intro {2}|))
)";
/*
static const string DEFINITION =
    R"((define-fun {0} ((s {1}) (t {1})) Bool
  (forall ((e |{2}|)) (=> ({3} e s) ({3} e t))))
)";
*/

namespace Predicate {

MapUnaryBType<Inclusion> Inclusion::m_cache;

Inclusion::Inclusion(const BType& T, const std::string& script,
                     const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "<:") {}

}  // namespace Predicate

shared_ptr<Abstract> Factory::Inclusion(const BType& T) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  std::shared_ptr<Abstract> result =
      find(BConstruct::Predicate::Inclusion::m_cache, T);
  if (!result) {
    const BType PT = BType::POW(T);
    const std::string op = smtSymbol(Pred::ComparisonOp::Membership, T);
    const string script =
        fmt::format(script_pattern, smtSymbol(Pred::ComparisonOp::Subset, T),
                    symbol(PT), symbolInner(T),
                    smtSymbol(Pred::ComparisonOp::Membership, T), symbol(T));
    const PreRequisites requisites = {Factory::SetMembership(T)};
    result =
        make(BConstruct::Predicate::Inclusion::m_cache, T, script, requisites);
  }
  return result;
}

}  // namespace BConstruct
