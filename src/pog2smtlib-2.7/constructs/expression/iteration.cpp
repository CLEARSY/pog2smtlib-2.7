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
#include "iteration.h"

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

static constexpr std::string_view DECLARATION =
    R"((declare-fun {0} ({1} {2}) {1})
)";
static constexpr std::string_view BASE_SCRIPT = R"((assert (!
  (forall ((R {1})) (= ({0} R 1) R))
  :named |ax.set.iterate.1 {4}|))
)";
static constexpr std::string_view BASE_SCRIPT_T = R"((assert (!
  (forall ((R {1})) (! (= ({0} R 1) R) :pattern ({0} R 1)))
  :named |ax.set.iterate.1 {4}|))
)";
static constexpr std::string_view INDUCT_SCRIPT = R"((assert (!
  (forall ((R {1})(n {2}))
    (= ({0} R (+ n 1)) ({3} R ({0} R n))))
  :named |ax.set.iterate.n+1 {4}|))
)";
static constexpr std::string_view INDUCT_SCRIPT_T = R"((assert (!
  (forall ((R {1})(n {2}))
    (! (= ({0} R (+ n 1)) ({3} R ({0} R n))) :pattern ({0} R (+ n 1))))
  :named |ax.set.iterate.n+1 {4}|))
)";

namespace Expression {

MapUnaryBType<Iteration> Iteration::m_cache;

Iteration::Iteration(const BType& T, const string& script,
                     const PreRequisites& requisites)
    : UnaryBType(T, script, requisites, "iterate") {}

}  // namespace Expression

std::shared_ptr<Abstract> Factory::Iteration(const BType& T) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, BASE_SCRIPT_T, INDUCT_SCRIPT_T,
                    BASE_SCRIPT, INDUCT_SCRIPT);
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Iteration::m_cache, T);
  if (!result) {
    const auto TxT = BType::PROD(T, T);
    const auto PTxT = BType::POW(TxT);
    const string script =
        fmt::format(script_pattern,
                    /*0*/ smtSymbol(Expr::BinaryOp::Iteration, T),
                    /*1*/ symbol(PTxT),
                    /*2*/ symbol(BType::INT),
                    /*3*/ smtSymbol(Expr::BinaryOp::Composition, T, T, T),
                    /*4*/ symbolInner(T));
    const PreRequisites requisites{Factory::Composition(T, T, T)};
    result =
        make(BConstruct::Expression::Iteration::m_cache, T, script, requisites);
  }
  return result;
}

}  // namespace BConstruct
