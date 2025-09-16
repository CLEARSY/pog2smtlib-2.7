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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {3})
(assert (!
  (forall ((R1 {1}) (R2 {2}) (p {4}))
    (= ({5} p ({0} R1 R2))
       (and
         ({6} (maplet (fst (fst p)) (fst (snd p))) R1)
         ({7} (maplet (snd (fst p)) (snd (snd p))) R2)
       )
    )
  )
  :named |ax.set.in.parallelproduct {8}|))
)";

Parallel_Product::Parallel_Product(const BType &T, const BType &U,
                                   const BType &V, const BType &W)
    : NaryBType(T, U, V, W) {
  const auto TxU = BType::PROD(T, U);
  const auto TxUxV = BType::PROD(TxU, V);
  const auto TxUxVxW = BType::PROD(TxUxV, W);
  const auto VxW = BType::PROD(V, W);
  const auto TxVxUxW = BType::PROD(TxU, VxW);
  const auto PTxU = BType::POW(TxU);
  const auto PVxW = BType::POW(VxW);
  const auto PTxVxUxW = BType::POW(TxVxUxW);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Parallel_Product, T, U, V, W),
                  /*1*/ symbol(PTxU),
                  /*2*/ symbol(PVxW),
                  /*3*/ symbol(PTxVxUxW),
                  /*4*/ symbol(TxVxUxW),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, TxVxUxW),
                  /*6*/ smtSymbol(Pred::ComparisonOp::Membership, TxU),
                  /*7*/ smtSymbol(Pred::ComparisonOp::Membership, VxW),
                  /*8*/ symbolInner(TxUxVxW));
  m_label = "∥";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxVxUxW),
       std::make_shared<BConstruct::Predicate::SetMembership>(TxU),
       std::make_shared<BConstruct::Predicate::SetMembership>(VxW)});
  m_debug_string = fmt::format("∥_<{},{},{}>", T.to_string(), U.to_string(),
                               V.to_string(), W.to_string());
}

};  // namespace BConstruct::Expression
