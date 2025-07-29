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
    (forall ((f {1})(x {2}))
        ({4} (maplet x ({0} f x)) f))
    :named |ax.fun.eval {5}|))
)";

Evaluation::Evaluation(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT, 
                         /*0*/ smtSymbol(Expr::BinaryOp::Application, U, V),
                         /*1*/ symbol(PUxV),
                         /*2*/ symbol(U),
                         /*3*/ symbol(V),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*5*/ symbolInner(UxV));
  m_label = "eval";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV)});
  m_debug_string = fmt::format("eval_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
