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
    (forall ((e {1})) (= (|set.in {3}| e {0}) (<= 0 e)))
    :named |ax.set.in.NATURAL|))
)";

Natural::Natural() {
  m_script = fmt::format(
      SCRIPT, /*0*/ smtSymbol(Expr::Visitor::EConstant::NATURAL),
      /*1*/ symbol(BType::INT), /*2*/ symbol(BType::POW(BType::INT)),
      /*3*/ symbolInner(BType::INT));
  m_label = "NATURAL";
  m_prerequisites.insert(
      std::make_shared<Predicate::SetMembership>(BType::INT));
  m_debug_string = "NATURAL";
}
};  // namespace BConstruct::Expression
