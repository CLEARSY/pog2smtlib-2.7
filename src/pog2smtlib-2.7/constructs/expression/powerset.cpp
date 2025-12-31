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
#include "powerset.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2}) {3})
(assert (!
  (forall ((s {2}) (t {2}))
    (=
      ({1} s ({0} t))
      ({4} s t)))
  :named |ax.sub-sets {5}|))
)";

namespace Expression {

MapUnaryBType<PowerSet> PowerSet::m_cache;

PowerSet::PowerSet(const BType& T, const string& script,
                   const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "POW") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::PowerSet(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::PowerSet::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto PPT = BType::POW(PT);
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                    /*1*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                    /*2*/ symbol(PT),
                    /*3*/ symbol(PPT),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Subset, T),
                    /*5*/ symbolInner(T));
    const PreRequisites requisites{Factory::SetMembership(PT),
                                   Factory::Inclusion(T)};
    result =
        make(BConstruct::Expression::PowerSet::m_cache, T, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
