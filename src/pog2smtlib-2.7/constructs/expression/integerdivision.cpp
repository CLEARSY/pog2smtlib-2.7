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
#include "integerdivision.h"

#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "../type/type.h"
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
        (= ({0} a b) (div a b)))
      (=> (and (<= 0 a) (< b 0))
        (= ({0} a b) (- (div a (- b)))))
      (=> (and (< a 0) (< 0 b))
        (= ({0} a b) (- (div (- a) b))))
      (=> (and (<= a 0) (< b 0))
        (= ({0} a b) (div a b)))))
  :named |ax.int.div :1|))
  )";

namespace Expression {

std::shared_ptr<IntegerDivision> IntegerDivision::m_cache;

IntegerDivision::IntegerDivision(const std::string &script,
                                 const PreRequisites &requisites)
    : Uniform(script, requisites, "/i") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::IntegerDivision() {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::IntegerDivision::m_cache);
  if (!result) {
    const string script = fmt::format(
        SCRIPT, smtSymbol(Expr::BinaryOp::IDivision), symbol(BType::INT));
    const PreRequisites requisites{Factory::Type(BType::INT)};
    result = make(BConstruct::Expression::IntegerDivision::m_cache, script,
                  requisites);
  }
  return result;
}

};  // namespace BConstruct
