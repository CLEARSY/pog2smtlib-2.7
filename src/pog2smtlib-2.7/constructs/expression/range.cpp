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
#include "range.h"

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

static const string DECLARATION = R"((declare-fun {0} ({2}) {1})
)";
static const string SCRIPT = R"((assert (!
  (forall ((r {2}) (e |{6}|))
    (= ({3} e ({0} r))
       (exists ((x |{7}|)) ({4} (maplet x e) r))))
  :named {8}))
)";
static const string SCRIPT_T = R"((assert (!
  (forall ((r {2}) (e |{6}|)) (!
    (= ({3} e ({0} r))
       (exists ((x |{7}|)) ({4} (maplet x e) r)))
    :pattern ( ({3} e ({0} r)) )))
  :named {8}))
)";

namespace Expression {

MapBinaryBType<Range> Range::m_cache;

Range::Range(const BType &U, const BType &V, const string &script,
             const PreRequisites &requisites)
    : BinaryBType(U, V, script, requisites, "ran") {}

}  // namespace Expression

shared_ptr<Abstract> Factory::Range(const BType &U, const BType &V) {
  static string script_pattern{};
  initScriptPattern(script_pattern, DECLARATION, SCRIPT_T, SCRIPT);
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Range::m_cache, U, V);
  if (!result) {
    const auto PV = BType::POW(V);
    const auto xUV = BType::PROD(U, V);
    const auto PxUV = BType::POW(xUV);
    const string arg0{smtSymbol(Expr::UnaryOp::Range, U, V)};
    const string arg1{symbol(PV)};
    const string arg2{symbol(PxUV)};
    const string arg3{smtSymbol(Pred::ComparisonOp::Membership, V)};
    const string arg4{smtSymbol(Pred::ComparisonOp::Membership, xUV)};
    const string arg5{symbolInner(xUV)};
    const string arg6{symbolInner(V)};
    const string arg7{symbolInner(U)};
    const string arg8{fmt::format("|ax:set.in.range {0}|", symbolInner(xUV))};
    const std::string script = fmt::format(script_pattern, arg0, arg1, arg2,
                                           arg3, arg4, arg5, arg6, arg7, arg8);
    const PreRequisites requisites{Factory::SetMembership(xUV)};
    result =
        make(BConstruct::Expression::Range::m_cache, U, V, script, requisites);
  }
  return result;
}

}  // namespace BConstruct
