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
#include "general_concatenation.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"
#include "emptyseq.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {2})
(assert (!
  (= ({0} |seq.empty {3}|) |seq.empty {6}|)
  :named |ax.generalized.concatenation.empty {6}|
))
(assert (!
  (forall ((s {1})(x {2}))
    (= ({0} ({4} x s))
       ({5} x ({0} s))))
  :named |ax.generalized.concatenation.not.empty {6}|
))
)";

namespace Expression {

MapUnaryBType<General_Concatenation> General_Concatenation::m_cache;

General_Concatenation::General_Concatenation(
    const BType& T, const std::string& script,
    set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "conc") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::General_Concatenation(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::General_Concatenation::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const auto ZxPZxT = BType::PROD(BType::INT, PZxT);
    const auto PZxPZxT = BType::POW(ZxPZxT);
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::UnaryOp::Concatenation, T),
                    /*1*/ symbol(PZxPZxT),
                    /*2*/ symbol(PZxT),
                    /*3*/ symbolInner(PZxT),
                    /*4*/ smtSymbol(Expr::BinaryOp::Head_Insertion, PZxT),
                    /*5*/ smtSymbol(Expr::BinaryOp::Concatenation, T),
                    /*6*/ symbolInner(T));
    set<shared_ptr<Abstract>> requisites = {
        Factory::Insert_In_Front(PZxT),
        Factory::Concatenation(T),
        Factory::EmptySeq(PZxT),
        Factory::EmptySeq(T),
    };
    result = make(BConstruct::Expression::General_Concatenation::m_cache, T,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
