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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {2})
(assert (!
  (forall ((E {1})(s {3}))
    (= ({4} s ({0} E))
       (and ({4} s ({5} E)) (not (= s |seq.empty {6}|)))))
  :named |ax.iseq1 {6}|))
)";

Injective_Seq1::Injective_Seq1(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  const auto PPZxT = BType::POW(PZxT);
  m_script = fmt::format(
      SCRIPT,
      /*0*/ smtSymbol(Expr::UnaryOp::Non_Empty_Injective_Sequences, T),
      /*1*/ symbol(PT),
      /*2*/ symbol(PPZxT),
      /*3*/ symbol(PZxT),
      /*4*/ smtSymbol(Pred::ComparisonOp::Membership, PZxT),
      /*5*/ smtSymbol(Expr::UnaryOp::Injective_Sequences, T),
      /*6*/ symbolInner(T));
  m_label = "iseq1";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Injective_Seq>(T),
       std::make_shared<BConstruct::Predicate::SetMembership>(PZxT),
       std::make_shared<BConstruct::Expression::EmptySeq>(T)});
  m_debug_string = fmt::format("iseq1_{}", T.to_string());
}

};  // namespace BConstruct::Expression
