#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {2}) {3})
(assert (!
  (forall ((r {1}) (s {2}) (p {4}))
    (= ({5} p ({0} r s))
       (exists ((y {6}))
         (and
           ({7} (maplet (fst p) y) r)
           ({8} (maplet y (snd p)) s)))))
  :named |ax.set.in.relcomp {9}|))
)";

Composition::Composition(const BType &T, const BType &U, const BType &V)
    : TernaryBType(T, U, V) {
  const auto PT = BType::POW(T);
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto TxU = BType::PROD(T, U);
  const auto PTxU = BType::POW(TxU);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  const auto TxV = BType::PROD(T, V);
  const auto PTxV = BType::POW(TxV);
  const auto TxUxV = BType::PROD(TxU, V);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Composition, T, U, V),
                         /*1*/ symbol(PTxU),
                         /*2*/ symbol(PUxV),
                         /*3*/ symbol(PTxV),
                         /*4*/ symbol(TxV),
                         /*5*/ smtSymbol(Pred::ComparisonOp::Membership, TxV),
                         /*6*/ symbol(U),
                         /*7*/ smtSymbol(Pred::ComparisonOp::Membership, TxU),
                         /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*9*/ symbolInner(TxUxV));
  m_label = ";";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxU),
       std::make_shared<BConstruct::Predicate::SetMembership>(TxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(UxV)});
  m_debug_string =
      fmt::format(";_<{},{},{}>", T.to_string(), U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
