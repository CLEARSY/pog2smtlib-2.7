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
#include "intorelation.h"

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
  (forall ((f {1})(p {3}))
    (= ({4} p ({0} f))
       (exists ((q {5}))
           (and ({6} q f) (= (fst p) (fst q)) ({7} (snd p) (snd q))))))
  :named |ax.rel {8}|))
)";
namespace Expression {

MapBinaryBType<Transformed_Into_Relation> Transformed_Into_Relation::m_cache;

Transformed_Into_Relation::Transformed_Into_Relation(
    const BType &U, const BType &V, const string &script,
    const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "rel") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Transformed_Into_Relation(const BType &U,
                                                        const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Transformed_Into_Relation::m_cache, U, V);
  if (!result) {
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto UxPV = BType::PROD(U, PV);
    const auto PUxPV = BType::POW(UxPV);
    const auto PUxV = BType::POW(UxV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Rel, U, V),
                    /*1*/ symbol(PUxPV),
                    /*2*/ symbol(PUxV),
                    /*3*/ symbol(UxV),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                    /*5*/ symbol(UxPV),
                    /*6*/ smtSymbol(Pred::ComparisonOp::Membership, UxPV),
                    /*7*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                    /*8*/ symbolInner(UxV));
    const PreRequisites requisites = {Factory::SetMembership(UxV),
                                      Factory::SetMembership(UxPV),
                                      Factory::SetMembership(V)};
    result = make(BConstruct::Expression::Transformed_Into_Relation::m_cache, U,
                  V, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
