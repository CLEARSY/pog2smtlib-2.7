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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {3})
(assert (!
  (forall ((X {1}))
    (= ({0} X)
       ({2}
         (lambda ((x {6}))
           (and ({5} (fst x) X) (= (fst x) (snd x)))))))
  :named |def.id {4}|))
)";

Identity::Identity(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PT = BType::POW(T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Identity, T),
                         /*1*/ symbol(PT),
                         /*2*/ smtSymbol(Expr::NaryOp::Set, TxT),
                         /*3*/ symbol(PTxT),
                         /*4*/ symbolInner(T),
                         /*5*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                         /*6*/ symbol(TxT));
  m_label = "id";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(T),
       std::make_shared<BConstruct::Expression::Set>(TxT)});
  m_debug_string = fmt::format("id_<{}>", T.to_string());
}

};  // namespace BConstruct::Expression
