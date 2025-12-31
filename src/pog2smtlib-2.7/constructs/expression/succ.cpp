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
#include "succ.h"

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

static constexpr std::string_view SCRIPT = R"((declare-const {0} {1})
(assert (!
  (forall ((x {3}))
      (=
        ({2} x {0})
        (= (snd x) (+ (fst x) 1))
      )
  )
  :named |ax:int.succ|))
)";

namespace Expression {

std::shared_ptr<Succ> Succ::m_cache;

Succ::Succ(const std::string &script, const PreRequisites &requisites)
    : Uniform(script, requisites, "succ") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Succ() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Succ::m_cache);
  if (!result) {
    const auto xZZ = BType::PROD(BType::INT, BType::INT);
    const string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::Visitor::EConstant::Successor),
        /*1*/ symbol(BType::POW(xZZ)),
        /*2*/
        smtSymbol(Pred::ComparisonOp::Membership, xZZ),
        /*3*/ symbol(xZZ));
    const PreRequisites requisites{Factory::SetMembership(xZZ)};
    result = make(BConstruct::Expression::Succ::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
