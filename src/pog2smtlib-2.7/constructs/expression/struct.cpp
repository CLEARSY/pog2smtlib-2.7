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
#include "struct.h"

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
    R"((declare-const {0} (-> |? {1}| {2}))
(assert (!
  (forall ((p |? {1}|))
    (forall ((x {3}))
      (= ({4} x ({0} p))
         (p x))))
  :named |ax.struct.definition {1}|))
)";

namespace Expression {

MapUnaryBType<Struct> Struct::m_cache;

Struct::Struct(const BType& T, const string& script,
               set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "struct") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::Struct(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Struct::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::EKind::Struct, T),
                    /*1*/ symbolInner(T),
                    /*2*/ symbol(PT),
                    /*3*/ symbol(T),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, T));
    set<shared_ptr<Abstract>> requisites{Factory::Set(T)};
    result =
        make(BConstruct::Expression::Struct::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
