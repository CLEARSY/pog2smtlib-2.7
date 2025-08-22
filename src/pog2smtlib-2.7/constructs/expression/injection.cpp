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
(declare-fun |injections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}) (f {5}))
     (= ({6} f (|injections {0} {1}| X Y))
        (forall ((p1 {7}) (p2 {7}))
          (=> (and ({8} p1 f) ({8} p2 f) (= (snd p1) (snd p2)))
              (= (fst p1) (fst p2))))))
  :named |ax:set.in.injections {9}|))
)";

Injection::Injection(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  const auto PPUxV = BType::POW(PUxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ symbolInner(U),
                         /*1*/ symbolInner(V),
                         /*2*/ symbol(PU),
                         /*3*/ symbol(PV),
                         /*4*/ symbol(PPUxV),
                         /*5*/ symbol(PUxV),
                         /*6*/ smtSymbol(Pred::ComparisonOp::Membership, PUxV),
                         /*7*/ symbol(UxV),
                         /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*9*/ symbolInner(UxV));
  m_label = "inj";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(PUxV),
       std::make_shared<BConstruct::Predicate::Equality>(U),
       std::make_shared<BConstruct::Predicate::Equality>(V)});
  m_debug_string = fmt::format("inj_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
