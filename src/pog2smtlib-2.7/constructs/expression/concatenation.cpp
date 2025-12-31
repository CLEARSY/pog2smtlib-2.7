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
#include "concatenation.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {1}) {1})
(assert (!
  (forall ((s1 {1})(s2 {1})(p {2}))
    (= ({3} p ({0} s1 s2))
       (or ({3} p s1)
           ({3} (maplet (- (fst p) ({4} s1)) (snd p)) s2))))
  :named |ax.conc.definition {5}|
))
)";

namespace Expression {

MapUnaryBType<Concatenation> Concatenation::m_cache;

Concatenation::Concatenation(const BType& T, const std::string& script,
                             const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "^") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Concatenation(const BType& T) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Concatenation::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Concatenation, T),
                    /*1*/ symbol(PZxT),
                    /*2*/ symbol(ZxT),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                    /*4*/ smtSymbol(Expr::UnaryOp::Size, T),
                    /*5*/ symbolInner(T));
    const BConstruct::PreRequisites requisites = {
        Factory::SetMembership(T),
        Factory::Size(T),
    };
    result = make(BConstruct::Expression::Concatenation::m_cache, T, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
