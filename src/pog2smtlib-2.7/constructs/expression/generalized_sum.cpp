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
#include "generalized_sum.h"

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
  :named |ax.sigma.empty|))
(assert (!
  (forall ((s {2}))
    (forall ((e |{1}|))
      (= ({4} e s)
        (= ({0} s)
          (+ e
             ({0}
               ({5}
                 (lambda ((x |{1}|)) (and ({4} x s) (not (= x e)))))))))))
  :named |ax.sigma.incr|))
)";

namespace Expression {

shared_ptr<GeneralizedSum> GeneralizedSum::m_cache;

GeneralizedSum::GeneralizedSum(const std::string &script,
                               set<shared_ptr<Abstract>> &requisites)
    : Uniform(script, requisites, "Σ") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::GeneralizedSum() {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::GeneralizedSum::m_cache);
  if (!result) {
    const auto PZ = BType::POW(BType::INT);
    const string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::QuantifiedOp::ISum),
        /*1*/ symbolInner(BType::INT),
        /*2*/ symbol(PZ),
        /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::INT),
        /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
        /*5*/ smtSymbol(Expr::NaryOp::Set, BType::INT));
    set<shared_ptr<Abstract>> requisites{Factory::Set(BType::INT),
                                         Factory::EmptySet(BType::INT)};
    result = make(BConstruct::Expression::GeneralizedSum::m_cache, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
