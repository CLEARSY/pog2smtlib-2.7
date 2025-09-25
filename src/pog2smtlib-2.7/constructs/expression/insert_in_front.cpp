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
#include "insert_in_front.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {2})
(assert (!
  (forall ((x {1})(s {2})(p {3}))
    (= ({4} p ({0} x s))
       (or (= p (maplet 1 x))
           ({4} (maplet (- (fst p) 1) (snd p)) s))))
  :named |ax.insert.front.def {5}|))
)";

namespace Expression {

MapUnaryBType<Insert_In_Front> Insert_In_Front::m_cache;

Insert_In_Front::Insert_In_Front(const BType& T, const std::string& script,
                                 set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "→") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Insert_In_Front(const BType& T) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Insert_In_Front::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Head_Insertion, T),
                    /*1*/ symbol(T),
                    /*2*/ symbol(PZxT),
                    /*3*/ symbol(ZxT),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                    /*5*/ symbolInner(T));
    set<shared_ptr<Abstract>> requisites = {
        Factory::SetMembership(ZxT),
    };
    result = make(BConstruct::Expression::Insert_In_Front::m_cache, T, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
