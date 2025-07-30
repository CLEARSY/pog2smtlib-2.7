#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) {2})
(assert (!
  (forall ((E {1})(s {3}))
    (= ({4} s ({0} E))
       (and ({4} s ({5} E))
            ({4} s (|surjections {6} {7}| {8} E)))))
  :named |ax.iseq1 {6}|))
)";

Perm::Perm(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  const auto PPZxT = BType::POW(PZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Permutations, T),
                         /*1*/ symbol(PT),
                         /*2*/ symbol(PPZxT),
                         /*3*/ symbol(PZxT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, PZxT),
                         /*5*/ smtSymbol(Expr::UnaryOp::Injective_Sequences, T),
                         /*6*/ symbolInner(BType::INT),
                         /*7*/ symbolInner(T),
                         /*8*/ smtSymbol(Expr::Visitor::EConstant::NATURAL1));
  m_label = "perm";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Injective_Seq>(T),
       std::make_shared<BConstruct::Predicate::SetMembership>(PZxT),
       std::make_shared<BConstruct::Expression::Natural1>(),
       std::make_shared<BConstruct::Expression::Surjection>(BType::INT, T)});
  m_debug_string = fmt::format("perm_{}", T.to_string());
}

};  // namespace BConstruct::Expression
