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
#include "eval.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1} {2}) {3})
 (assert (!
    (forall ((f {1})(x {2}))
        ({4} (maplet x ({0} f x)) f))
    :named |ax.fun.eval {5}|))
)";

namespace Expression {

MapBinaryBType<Evaluation> Evaluation::m_cache;

Evaluation::Evaluation(const BType &U, const BType &V, const string &script,
                       set<shared_ptr<Abstract>> &requisites)
    : BinaryBType(U, V, script, requisites, "_eval") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Evaluation(const BType &U, const BType &V) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Evaluation::m_cache, U, V);
  if (!result) {
    const auto UxV = BType::PROD(U, V);
    const auto PUxV = BType::POW(UxV);
    const std::string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Application, U, V),
                    /*1*/ symbol(PUxV),
                    /*2*/ symbol(U),
                    /*3*/ symbol(V),
                    /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                    /*5*/ symbolInner(UxV));
    set<shared_ptr<Abstract>> requisites = {Factory::SetMembership(UxV)};
    result = make(BConstruct::Expression::Evaluation::m_cache, U, V, script,
                  requisites);
  }
  return result;
}
};  // namespace BConstruct
