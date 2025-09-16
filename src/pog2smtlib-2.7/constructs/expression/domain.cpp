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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2}) {1})
(assert (!
  (forall ((r {2}) (e |{6}|))
    (= ({3} e ({0} r))
       (exists ((y |{7}|)) ({4} (maplet e y) r))))
  :named |ax:set.in.domain {5}|))
)";

Domain::Domain(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Domain, U, V),
                         /*1*/ symbol(PU),
                         /*2*/ symbol(PUxV),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*5*/ symbolInner(UxV),
                         /*6*/ symbolInner(U),
                         /*7*/ symbolInner(V));
  m_label = "dom";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(U)});
  m_debug_string = fmt::format("dom_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression