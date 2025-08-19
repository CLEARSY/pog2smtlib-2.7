#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) {1})
(assert (!
  (forall ((s {2}))
    (=> (not (= s {3})) ({4} ({0} s) s)))
  :named |ax.min.is.member|))
 (assert (!
   (forall ((s {2}))
     (forall ((e {1}))
        (=> ({4} e s) (<= ({0} s) e))))
  :named |ax.min.is.ge|))
)";

Min::Min() {
  m_script = fmt::format(
      SCRIPT,
      /*0*/ smtSymbol(Expr::UnaryOp::IMinimum),
      /*1*/ symbol(BType::INT),
      /*2*/ symbol(BType::POW(BType::INT)),
      /*3*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, BType::INT),
      /*4*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT));
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT),
       std::make_shared<BConstruct::Expression::EmptySet>(BType::INT)});
  m_label = "min";
  m_debug_string = "min";
}
};  // namespace BConstruct::Expression
