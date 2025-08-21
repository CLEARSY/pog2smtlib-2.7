#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) |{1}|)
(assert (!
  (= 0 ({0} {3}))
  :named |ax.sigma.empty|))
(assert (!
  (forall ((s {2}))
    (forall ((e |{1}|))
      (= ({4} e s)
        (= ({0} s)
          (+ e
             ({0}
               ({5}
                 (lambda ((x |{1}|)) (and ({4} x s) (not (= x e)))))))))))
  :named |ax.sigma.incr|))
)";

GeneralizedSum::GeneralizedSum() {
  const auto PZ = BType::POW(BType::INT);
  m_script = fmt::format(
      SCRIPT,
      /*0*/ smtSymbol(Expr::QuantifiedOp::ISum),
      /*1*/ symbolInner(BType::INT),
      /*2*/ symbol(PZ),
      /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::INT),
      /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
      /*5*/ smtSymbol(Expr::NaryOp::Set, BType::INT));
  m_label = "Σ";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT),
       std::make_shared<BConstruct::Expression::Set>(BType::INT),
       std::make_shared<BConstruct::Expression::EmptySet>(BType::INT)});
  m_debug_string = "Σ";
}

};  // namespace BConstruct::Expression
