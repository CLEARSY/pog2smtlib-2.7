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
#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) {3})
(assert (!
  (forall ((s {2}) (t {2}))
    (=
      ({1} s ({0} t))
      ({4} s t)))
  :named |ax.sub-sets {5}|))
)";

PowerSet::PowerSet(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto PPT = BType::POW(PT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                         /*1*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                         /*2*/ symbol(PT),
                         /*3*/ symbol(PPT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Subset, T),
                         /*5*/ symbolInner(T));
  m_label = "POW";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(PT),
       std::make_shared<BConstruct::Predicate::Inclusion>(T)});
  m_debug_string = fmt::format("POW_{}", T.to_string());
}

};  // namespace BConstruct::Expression
