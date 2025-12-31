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
#include "equality.h"

#include <fmt/core.h>

#include <string>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "btype.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((assert (!
  (forall ((s {1}) (t {1}))
    (=
      (= s t)
      (forall ((e |{0}|)) (= (|set.in {0}| e s) (|set.in {0}| e t)))))
  :named |ax.set.eq {0}|))
)";

namespace Predicate {

MapUnaryBType<Equality> Equality::m_cache;

Equality::Equality(const BType &T, const std::string &script,
                   const PreRequisites &requisites)
    : UnaryBType(T, script, requisites, "=") {}

};  // namespace Predicate

shared_ptr<Abstract> Factory::Equality(const BType &T) {

  std::shared_ptr<Abstract> result =
      find(BConstruct::Predicate::Equality::m_cache, T);
  if (!result) {
    string script{};
    PreRequisites requisites{};
    if (T.getKind() == BType::Kind::PowerType) {
      const BType &U = T.toPowerType().content;
      script = fmt::format(SCRIPT, symbolInner(U), symbol(T));
      requisites.insert({Factory::SetMembership(U)});
    }
    result =
        make(BConstruct::Predicate::Equality::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct