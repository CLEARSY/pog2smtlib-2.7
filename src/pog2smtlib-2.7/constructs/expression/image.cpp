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
(declare-fun {0} ({1} {2}) {3})
(assert (!
  (forall ((r {1}) (s {2}) (x {4}))
    (= ({5} x ({0} r s))
       (exists ((y {6})) (and ({7} y s) ({8} (maplet y x) r)))))
  :named |ax:set.in.image {9}|))
)";

Image::Image(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  const auto UxPUxV = BType::PROD(U, PUxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Image, U, V),
                         /*1*/ symbol(PUxV),
                         /*2*/ symbol(PU),
                         /*3*/ symbol(PV),
                         /*4*/ symbol(V),
                         /*5*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                         /*6*/ symbol(U),
                         /*7*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                         /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*9*/ symbolInner(UxPUxV));
  m_label = "image";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(U),
       std::make_shared<BConstruct::Predicate::SetMembership>(V),
       std::make_shared<BConstruct::Predicate::SetMembership>(UxV)});
  m_debug_string = fmt::format("image_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression