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
#include "relations.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {4})
(assert (!
  (forall ((X {1}) (Y {2}))
    (= ({0} X Y)
       ({3} ({5} X Y))))
    :named |def.relations {6}|))
)";

namespace Expression {

MapBinaryBType<Relation> Relation::m_cache;

Relation::Relation(const BType &U, const BType &V, const string &script,
                   const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "<->") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Relation(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Relation::m_cache, U, V);
  if (!result) {
    const auto PU = BType::POW(U);
    const auto PV = BType::POW(V);
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const auto PPUxV = BType::POW(PUxV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Relations, U, V),
                    /*1*/ symbol(PU),
                    /*2*/ symbol(PV),
                    /*3*/ smtSymbol(Expr::UnaryOp::Subsets, UxV),
                    /*4*/ symbol(PPUxV),
                    /*5*/ smtSymbol(Expr::BinaryOp::Cartesian_Product, U, V),
                    /*6*/ symbolInner(UxV));
    const PreRequisites requisites = {Factory::ExpressionCartesianProduct(U, V),
                                      Factory::PowerSet(UxV)};
    result = make(BConstruct::Expression::Relation::m_cache, U, V, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
