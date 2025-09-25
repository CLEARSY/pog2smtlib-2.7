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
#include "identity.h"

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

static constexpr std::string_view SCRIPT = R"((declare-fun {0} ({1}) {3})
(assert (!
  (forall ((X {1}))
    (= ({0} X)
       ({2}
         (lambda ((x {6}))
           (and ({5} (fst x) X) (= (fst x) (snd x)))))))
  :named |def.id {4}|))
)";

namespace Expression {

MapUnaryBType<Identity> Identity::m_cache;

Identity::Identity(const BType& T, const string& script,
                   set<shared_ptr<Abstract>>& requisites)
    : UnaryBType(T, script, requisites, "id") {}

};  // namespace Expression

std::shared_ptr<Abstract> Factory::Identity(const BType& T) {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Expression::Identity::m_cache, T);
  if (!result) {
    const auto TxT = BType::PROD(T, T);
    const auto PT = BType::POW(T);
    const auto PTxT = BType::POW(TxT);
    const string script =
        fmt::format(SCRIPT, /*0*/ smtSymbol(Expr::UnaryOp::Identity, T),
                    /*1*/ symbol(PT),
                    /*2*/ smtSymbol(Expr::NaryOp::Set, TxT),
                    /*3*/ symbol(PTxT),
                    /*4*/ symbolInner(T),
                    /*5*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                    /*6*/ symbol(TxT));
    set<shared_ptr<Abstract>> requisites{Factory::SetMembership(T),
                                         Factory::Set(TxT)};
    result =
        make(BConstruct::Expression::Identity::m_cache, T, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
