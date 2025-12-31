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
#include "strictinclusion.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {1}) Bool)
(assert (!
  (forall ((s {1}) (t {1}))
    (=
      ({0} s t)
      (and
        ({2} s t)
        (not (= s t)))))
  :named |ax.set.subset {3}|))
)";

namespace Predicate {

MapUnaryBType<StrictInclusion> StrictInclusion::m_cache;

StrictInclusion::StrictInclusion(const BType& T, const std::string& script,
                                 const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "<<:") {}

};  // namespace Predicate

shared_ptr<Abstract> Factory::StrictInclusion(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Predicate::StrictInclusion::m_cache, T);
  if (!result) {
    const BType PT = BType::POW(T);
    const std::string op = smtSymbol(Pred::ComparisonOp::Membership, T);
    const string script = fmt::format(
        SCRIPT, smtSymbol(Pred::ComparisonOp::Strict_Subset, T), symbol(PT),
        smtSymbol(Pred::ComparisonOp::Subset, T), symbolInner(T));
    const PreRequisites requisites = {Factory::Equality(T),
                                      Factory::Inclusion(T)};
    result = make(BConstruct::Predicate::StrictInclusion::m_cache, T, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
