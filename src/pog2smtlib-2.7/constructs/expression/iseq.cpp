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
#include "iseq.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {2})
(assert (!
  (forall ((E {1})(s {3}))
    (= ({4} s ({0} E))
       (and ({4} s ({5} E))
            ({4} s (|injections {6} {7}| {8} E)))))
  :named |ax.iseq {7}|))
)";

namespace Expression {

MapUnaryBType<Injective_Seq> Injective_Seq::m_cache;

Injective_Seq::Injective_Seq(const BType& T, const std::string& script,
                             set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "iseq") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Injective_Seq(const BType& T) {

  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Injective_Seq::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const auto PPZxT = BType::POW(PZxT);
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::UnaryOp::Injective_Sequences, T),
                    /*1*/ symbol(PT),
                    /*2*/ symbol(PPZxT),
                    /*3*/ symbol(PZxT),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, PZxT),
                    /*5*/ smtSymbol(Expr::UnaryOp::Sequences, T),
                    /*6*/ symbolInner(BType::INT),
                    /*7*/ symbolInner(T),
                    /*8*/ smtSymbol(Expr::Visitor::EConstant::NATURAL1));
    set<shared_ptr<Abstract>> requisites = {
        Factory::Seq(T), Factory::SetMembership(PZxT), Factory::Natural1(),
        Factory::Injection(BType::INT, T)};

    result = make(BConstruct::Expression::Injective_Seq::m_cache, T, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct
