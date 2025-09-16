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

static constexpr std::string_view SCRIPT =
    R"((declare-fun {0} (|? {1}| (-> |{1}| |{2}|)) {3})
(assert (!
  (forall ((P |? {1}|)(E (-> |{1}| |{2}|)))
    (forall ((p |({1} x {2})|))
      (= ({4} p ({0} P E))
         (and (P (fst p))
              (= (snd p) (E (fst p)))))))
    :named |ax.set.in.lambda {1} {2}|))
)";

Lambda::Lambda(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::QuantifiedOp::Lambda, U, V),
                         /*1*/ symbolInner(U),
                         /*2*/ symbolInner(V),
                         /*3*/ symbol(PUxV),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV));
  m_label = "λ";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Expression::Set>(U),
       std::make_shared<BConstruct::Predicate::Equality>(V)});
  m_debug_string = fmt::format("λ_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
