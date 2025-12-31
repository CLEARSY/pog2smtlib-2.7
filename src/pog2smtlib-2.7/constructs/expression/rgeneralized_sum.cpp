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
#include "rgeneralized_sum.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({2}) |{1}|)
(assert (!
  (= 0 ({0} {3}))
  :named |ax.rsigma.empty|))
(assert (!
  (forall ((s {2}))
    (forall ((e |{1}|))
      (= ({4} e s)
        (= ({0} s)
          (+ e
             ({0}
               ({5}
                 (lambda ((x |{1}|)) (and ({4} x s) (not (= x e)))))))))))
  :named |ax.rsigma.incr|))
)";

namespace Expression {

shared_ptr<RGeneralizedSum> RGeneralizedSum::m_cache;

RGeneralizedSum::RGeneralizedSum(const std::string &script,
                                 const PreRequisites &requisites)
    : Uniform(script, requisites, "rΣ") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::RGeneralizedSum() {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::RGeneralizedSum::m_cache);
  if (!result) {
    const auto PREAL = BType::POW(BType::REAL);
    const string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::QuantifiedOp::RSum),
        /*1*/ symbolInner(BType::REAL),
        /*2*/ symbol(PREAL),
        /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::REAL),
        /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::REAL),
        /*5*/ smtSymbol(Expr::NaryOp::Set, BType::REAL));
    const PreRequisites requisites{Factory::Set(BType::REAL),
                                   Factory::EmptySet(BType::REAL)};
    result = make(BConstruct::Expression::RGeneralizedSum::m_cache, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
