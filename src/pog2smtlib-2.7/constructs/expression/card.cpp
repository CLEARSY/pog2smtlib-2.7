#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) Cardinals)
(assert (!
  (forall ((s {1}))
    (or (= ({0} s) Infinite)
        (exists ((f {2}))
          ({3} f (|bijections {4} {5}| s ({6} 1 (Value ({0} s))))))))
  :named |ax.card.definition {4}|))
)";

Card::Card(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto TxZ = BType::PROD(T, BType::INT);
  const auto PTxZ = BType::POW(TxZ);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Cardinality, T),
                         /*1*/ symbol(PT),
                         /*2*/ symbol(PTxZ),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PTxZ),
                         /*4*/ symbolInner(T),
                         /*5*/ symbolInner(BType::INT),
                         /*6*/ smtSymbol(Expr::BinaryOp::Interval));
  m_label = "card";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxZ),
       std::make_shared<BConstruct::Expression::Bijection>(T, BType::INT),
       std::make_shared<BConstruct::Expression::Interval>(),
       std::make_shared<BConstruct::Expression::Cardinals>()});
  m_debug_string = fmt::format("card_{}", T.to_string());
}

};  // namespace BConstruct::Expression
