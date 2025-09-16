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
  (forall ((E {1}) (s {3}))
    (=>
      ({4} s ({0} E))
      ((_ is Finite) ({5} s))))
  :named |ax.seq.is.finite {10}|))
(assert (!
  (forall ((E {1}))
    ({6}
      ({0} E)
      ({7} ({8} 1 (Value ({9} E))) E)))
  :named |ax.seq.is.total.fun {10}|))
)";

Seq::Seq(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  const auto PPZxT = BType::POW(PZxT);
  m_script = fmt::format(
      SCRIPT,
      /*0*/ smtSymbol(Expr::UnaryOp::Sequences, T),
      /*1*/ symbol(PT),
      /*2*/ symbol(PPZxT),
      /*3*/ symbol(PZxT),
      /*4*/ smtSymbol(Pred::ComparisonOp::Membership, PZxT),
      /*5*/ smtSymbol(Expr::UnaryOp::Cardinality, ZxT),
      /*6*/ smtSymbol(Pred::ComparisonOp::Subset, PZxT),
      /*7*/ smtSymbol(Expr::BinaryOp::Total_Functions, BType::INT, T),
      /*8*/ smtSymbol(Expr::BinaryOp::Interval),
      /*9*/ smtSymbol(Expr::UnaryOp::Cardinality, T),
      /*10*/ symbolInner(T));
  m_label = "seq";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Interval>(),
       std::make_shared<BConstruct::Expression::Card>(T),
       std::make_shared<BConstruct::Expression::Card>(ZxT),
       std::make_shared<BConstruct::Expression::Total_Function>(BType::INT, T),
       std::make_shared<BConstruct::Predicate::Inclusion>(PZxT)});
  m_debug_string = fmt::format("seq_{}", T.to_string());
}

};  // namespace BConstruct::Expression
