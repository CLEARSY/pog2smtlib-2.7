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
(declare-fun {0} ({1}) {2})
(assert (!
  (forall ((R {1}))
    (= ({0} R)
       ({3}
         (lambda ((x |{4}|))
           ({5} (maplet (snd x) (fst x)) R)))))
  :named |def.reverse {6}|))
)";

Reverse::Reverse(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto VxU = BType::PROD(V, U);
  const auto PVxU = BType::POW(VxU);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Inverse, U, V),
                         /*1*/ symbol(PUxV),
                         /*2*/ symbol(PVxU),
                         /*3*/ smtSymbol(Expr::NaryOp::Set, VxU),
                         /*4*/ symbolInner(VxU),
                         /*5*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*6*/ symbolInner(UxV));
  m_label = "~";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Set>(VxU),
       std::make_shared<BConstruct::Predicate::SetMembership>(UxV)});
  m_debug_string = fmt::format("~_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
