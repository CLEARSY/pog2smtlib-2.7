#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-const {0} {2})
(assert (!
  (forall ((e {1})) (= ({3} e {0}) (<= 1 e)))
  :named |ax.set.in.NATURAL1|))
)";

Natural1::Natural1() {
  m_script = fmt::format(
      SCRIPT, /*0*/ smtSymbol(Expr::Visitor::EConstant::NATURAL1),
      /*1*/ symbol(BType::INT), /*2*/ symbol(BType::POW(BType::INT)),
      /*3*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT));
  m_label = "NATURAL1";
  m_prerequisites.insert(
      std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT));
  m_debug_string = "NATURAL1";
}
};  // namespace BConstruct::Expression
