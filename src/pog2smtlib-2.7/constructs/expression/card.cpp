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
#include "card.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) Cardinals)
(assert (!
  (forall ((s {1}))
    (or (= ({0} s) Infinite)
        (exists ((f {2}))
          ({3} f (|bijections {4} {5}| s ({6} 1 (Value ({0} s))))))))
  :named |ax.card.definition {4}|))
)";

namespace Expression {

MapUnaryBType<Card> Card::m_cache;

Card::Card(const BType& T, const string& script,
           set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "card") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::Card(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Card::m_cache, T);
  if (!result) {
    const auto PT = BType::POW(T);
    const auto TxZ = BType::PROD(T, BType::INT);
    const auto PTxZ = BType::POW(TxZ);
    const string script =
        fmt::format(SCRIPT,
                    /*0*/ smtSymbol(Expr::UnaryOp::Cardinality, T),
                    /*1*/ symbol(PT),
                    /*2*/ symbol(PTxZ),
                    /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PTxZ),
                    /*4*/ symbolInner(T),
                    /*5*/ symbolInner(BType::INT),
                    /*6*/ smtSymbol(Expr::BinaryOp::Interval));
    set<shared_ptr<Abstract>> requisites{
        Factory::SetMembership(TxZ), Factory::Bijection(T, BType::INT),
        Factory::Interval(), Factory::Cardinals()};
    result = make(BConstruct::Expression::Card::m_cache, T, script, requisites);
  }
  return result;
}
};  // namespace BConstruct
