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
#include "emptyseq.h"

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

static constexpr std::string_view SCRIPT =
    R"((declare-const |seq.empty {0}| {1})
(assert (!
  (= |seq.empty {0}| {2})
  :named |ax:seq.empty.def {0}|))
)";

namespace Expression {

MapUnaryBType<EmptySeq> EmptySeq::m_cache;

EmptySeq::EmptySeq(const BType& T, const std::string& script,
                   set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "[]") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::EmptySeq(const BType& T) {

  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::EmptySeq::m_cache, T);
  if (!result) {
    const auto ZxT = BType::PROD(BType::INT, T);
    const auto PZxT = BType::POW(ZxT);
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ symbolInner(T),
                    /*1*/ symbol(PZxT),
                    /*2*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, ZxT));
    set<shared_ptr<Abstract>> requisites = {Factory::EmptySet(ZxT)};

    result =
        make(BConstruct::Expression::EmptySeq::m_cache, T, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
