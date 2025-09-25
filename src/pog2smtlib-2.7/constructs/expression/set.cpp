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

static constexpr std::string_view SCRIPT =
    R"((define-sort |? {0}| () (-> {1} Bool))
(declare-const {2} (-> |? {0}| {3}))
(assert (!
  (forall ((p |? {0}|))
    (forall ((x {1}))
      (= ({4} x ({2} p))
         (p x))))
  :named |ax:set.in.intent {0}|))
)";

namespace Expression {

MapUnaryBType<Set> Set::m_cache;

Set::Set(const BType& T, const string& script,
         set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "_set") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::Set(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Set::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const string script =
        fmt::format(SCRIPT, /*0*/ symbolInner(T),
                    /*1*/ symbol(T),
                    /*2*/ smtSymbol(Expr::NaryOp::Set, T),
                    /*3*/ symbol(PT),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, T));
    set<shared_ptr<Abstract>> requisites{Factory::SetMembership(T)};
    result = make(BConstruct::Expression::Set::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
