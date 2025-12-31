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
#include "setmembership.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "../type/type.h"
#include "btype.h"
#include "pred.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) Bool)
)";

namespace Predicate {

MapUnaryBType<SetMembership> SetMembership::m_cache;

SetMembership::SetMembership(const BType& T, const std::string& script,
                             const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, ":") {}

};  // namespace Predicate

shared_ptr<Abstract> Factory::SetMembership(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Predicate::SetMembership::m_cache, T);
  if (!result) {
    const BType PT = BType::POW(T);
    const std::string op = smtSymbol(Pred::ComparisonOp::Membership, T);
    const string script = fmt::format(SCRIPT, op, symbol(T), symbol(PT));
    PreRequisites requisites = {Factory::Type(PT)};
    switch (T.getKind()) {
      case BType::Kind::PowerType:
        requisites.insert({Factory::SetMembership(T.toPowerType().content)});
        break;
      case BType::Kind::ProductType:
        requisites.insert({Factory::SetMembership(T.toProductType().lhs),
                           Factory::SetMembership(T.toProductType().rhs)});
        break;
      default:
        break;
    }
    result = make(BConstruct::Predicate::SetMembership::m_cache, T, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
