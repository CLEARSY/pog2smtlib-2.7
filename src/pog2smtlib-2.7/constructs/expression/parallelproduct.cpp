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
#include "parallelproduct.h"

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
  (forall ((R1 {1}) (R2 {2}) (p {4}))
    (= ({5} p ({0} R1 R2))
       (and
         ({6} (maplet (fst (fst p)) (fst (snd p))) R1)
         ({7} (maplet (snd (fst p)) (snd (snd p))) R2)
       )
    )
  )
  :named |ax.set.in.parallelproduct {8} {9} {10} {11}|))
)";
/*
R1: P(T x U) , R2: P(V x W) -> P ((T x V) x (U x W))
{1}: P(T x U) , {2}: P(V x W) -> {3}: P ((T x V) x (U x W))
{4}: (T x V) x (U x W)
{5}: set.in (T x V) x (U x W)
{6}: set.in (T x U)
{7}: set.in (V x W)
*/

namespace Expression {

MapQuadrupleBType<Parallel_Product> Parallel_Product::m_cache;

Parallel_Product::Parallel_Product(const BType &T, const BType &U,
                                   const BType &V, const BType &W,
                                   const string &script,
                                   const PreRequisites &requisites)
    : QuaternaryBType(T, U, V, W, script, requisites, "∥") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Parallel_Product(const BType &T, const BType &U,
                                               const BType &V, const BType &W) {
  shared_ptr<Abstract> result =
      find(BConstruct::Expression::Parallel_Product::m_cache, T, U, V, W);
  if (!result) {
    const auto xTU = BType::PROD(T, U);
    const auto PxTU = BType::POW(xTU);
    const auto xVW = BType::PROD(V, W);
    const auto PxVW = BType::POW(xVW);
    const auto xTV = BType::PROD(T, V);
    const auto xUW = BType::PROD(U, W);
    const auto xxTVxUW = BType::PROD(xTV, xUW);
    const auto PxxTVxUW = BType::POW(xxTVxUW);

    /*
    {1}: P(T x U)
    {2}: P(V x W)
    {3}: P ((T x V) x (U x W))
    {4}: (T x V) x (U x W)
    {5}: set.in (T x V) x (U x W)
    {6}: set.in (T x U)
    {7}: set.in (V x W)
    */
    const std::string script = fmt::format(
        SCRIPT, /*0*/ smtSymbol(Expr::BinaryOp::Parallel_Product, T, U, V, W),
        /*1*/ symbol(PxTU),
        /*2*/ symbol(PxVW),
        /*3*/ symbol(PxxTVxUW),
        /*4*/ symbol(xxTVxUW),
        /*5*/ smtSymbol(Pred::ComparisonOp::Membership, xxTVxUW),
        /*6*/ smtSymbol(Pred::ComparisonOp::Membership, xTU),
        /*7*/ smtSymbol(Pred::ComparisonOp::Membership, xVW),
        /*8*/ symbolInner(T),
        /*9*/ symbolInner(U),
        /*10*/ symbolInner(V),
        /*11*/ symbolInner(W));
    BConstruct::PreRequisites requisites = {Factory::SetMembership(xxTVxUW),
                                            Factory::SetMembership(xTU),
                                            Factory::SetMembership(xVW)};
    result = make(BConstruct::Expression::Parallel_Product::m_cache, T, U, V, W,
                  script, requisites);
  }
  return result;
}

};  // namespace BConstruct
