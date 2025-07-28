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
    (forall ((e |{1}|)) (= (|set.in {1}| e |{0}|) (and (<= |MININT| e) (<= e |MAXINT|))))
    :named |ax.set.in.INT|))
)";

Int::Int() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::Visitor::EConstant::INT),
                         BType::INT, symbol(BType::POW(BType::INT)));
  m_label = "INT";
  m_prerequisites.insert({
      std::make_shared<Predicate::SetMembership>(BType::INT),
      std::make_shared<BConstruct::Expression::Maxint>(),
      std::make_shared<BConstruct::Expression::Minint>()
    }
  );
  m_debug_string = "INT";
}
};  // namespace BConstruct::Expression