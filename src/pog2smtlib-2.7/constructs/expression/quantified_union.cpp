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
(declare-fun {0} (|? {1}| (-> {2} {3})) {3})
(assert (!
  (forall ((P |? {1}|)(E (-> {2} {3}))(x {5}))
    (= ({4} x ({0} P E))
       (exists ((e {2})) (and (P e) ({4} x (E e))))))
  :named |ax.set.in.quantified.union {6}|))
)";

Quantified_Union::Quantified_Union(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::QuantifiedOp::Union, U, V),
                         /*1*/ symbolInner(U),
                         /*2*/ symbol(U),
                         /*3*/ symbol(PV),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                         /*5*/ symbol(V),
                         /*6*/ symbolInner(UxV));
  m_label = "UNION";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(V),
       std::make_shared<BConstruct::Expression::Set>(U)});
  m_debug_string = fmt::format("UNION_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
