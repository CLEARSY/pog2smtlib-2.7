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
#include "realdivision.h"

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
  (forall ((a {1}) (b {1}))
    (and
      (=> (and (<= 0 a) (< 0 b))
        (= ({0} a b) (/ a b)))
      (=> (and (<= 0 a) (< b 0))
        (= ({0} a b) (- (/ a (- b)))))
      (=> (and (< a 0) (< 0 b))
        (= ({0} a b) (- (/ (- a) b))))
      (=> (and (<= a 0) (< b 0))
        (= ({0} a b) (/ a b)))))
  :named |ax.real.div :1|))
)";

namespace Expression {

std::shared_ptr<RealDivision> RealDivision::m_cache;

RealDivision::RealDivision(const std::string &script,
                           set<shared_ptr<Abstract>> &requisites)
    : Uniform(script, requisites, "/r") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::RealDivision() {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::RealDivision::m_cache);
  if (!result) {
    const string script = fmt::format(
        SCRIPT, smtSymbol(Expr::BinaryOp::RDivision), symbol(BType::REAL));
    set<shared_ptr<Abstract>> requisites{Factory::Type(BType::REAL)};
    result =
        make(BConstruct::Expression::RealDivision::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
