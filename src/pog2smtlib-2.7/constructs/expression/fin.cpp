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
#include "fin.h"

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
  (forall ((s {1}) (t {1}))
    (= ({3} s ({0} t))
       (and
         ({3} s ({4} t))
         (not (= ({5} s) Infinite)))))
  :named |ax.finite sub-sets {6}|))
)";

namespace Expression {

MapUnaryBType<Fin> Fin::m_cache;

Fin::Fin(const BType& T, const string& script, const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "FIN") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Fin(const BType& T) {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Fin::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto PPT = BType::POW(PT);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Finite_Subsets, T),
                    /*1*/ symbol(PT),
                    /*2*/ symbol(PPT),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                    /*4*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                    /*5*/ smtSymbol(Expr::UnaryOp::Cardinality, T),
                    /*6*/ symbolInner(T));
    const PreRequisites requisites = {Factory::PowerSet(T), Factory::Card(T)};
    result = make(BConstruct::Expression::Fin::m_cache, T, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
