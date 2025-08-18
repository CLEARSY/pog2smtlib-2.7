#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) {1})
(assert (!
  (forall ((R {1})(p {2}))
    (= ({3} p ({0} R))
       (exists ((n {4}))
         (and (<= 1 n)
              ({3} p ({5} R n))))))
  :named |ax.closure1 {6}|))
)";

Closure1::Closure1(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Transitive_Closure, T),
                         /*1*/ symbol(PTxT),
                         /*2*/ symbol(TxT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, TxT),
                         /*4*/ symbol(BType::INT),
                         /*5*/ smtSymbol(Expr::BinaryOp::Iteration, T),
                         /*6*/ symbolInner(T));
  m_label = "closure1";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxT),
       std::make_shared<BConstruct::Expression::Iteration>(T)});
  m_debug_string = fmt::format("closure1_{}", T.to_string());
}

};  // namespace BConstruct::Expression
