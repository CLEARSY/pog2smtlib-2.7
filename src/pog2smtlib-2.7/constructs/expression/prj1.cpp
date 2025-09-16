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
  (forall ((E {1}) (F {2}) (t {4}))
    (= ({5} t ({0} E F))
       (and
				 ({6} (fst (fst t)) E)
				 ({7} (snd (fst t)) F)
				 (= (snd t) (fst (fst t))))))
  :named |ax.set.in.prj1 {8}|))
)";

Prj1::Prj1(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto UxVxU = BType::PROD(UxV, U);
  const auto PUxVxU = BType::POW(UxVxU);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::First_Projection, U, V),
                  /*1*/ symbol(PU),
                  /*2*/ symbol(PV),
                  /*3*/ symbol(PUxVxU),
                  /*4*/ symbol(UxVxU),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, UxVxU),
                  /*6*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                  /*7*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                  /*8*/ symbolInner(UxV));
  m_label = "prj1";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxVxU),
       std::make_shared<BConstruct::Predicate::SetMembership>(U),
       std::make_shared<BConstruct::Predicate::SetMembership>(V)});
  m_debug_string = fmt::format("prj1_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
