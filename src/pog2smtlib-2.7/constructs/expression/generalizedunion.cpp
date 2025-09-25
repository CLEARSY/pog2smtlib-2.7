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
#include "generalizedunion.h"

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
  (forall ((E {1}) (x {3}))
    (= ({4} x ({0} E))
       (exists ((e {2})) (and ({4} x e) ({5} e E)))))
  :named |ax.set.in.generalized.union {6}|))
)";

namespace Expression {

MapUnaryBType<GeneralizedUnion> GeneralizedUnion::m_cache;

GeneralizedUnion::GeneralizedUnion(const BType& T, const string& script,
                                   set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "union") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::GeneralizedUnion(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::GeneralizedUnion::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto PPT = BType::POW(PT);
    const string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Union, T),
                    /*1*/ symbol(PPT),
                    /*2*/ symbol(PT),
                    /*3*/ symbol(T),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                    /*5*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                    /*6*/ symbolInner(T));
    set<shared_ptr<Abstract>> requisites{Factory::SetMembership(PT)};
    result = make(BConstruct::Expression::GeneralizedUnion::m_cache, T, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct
