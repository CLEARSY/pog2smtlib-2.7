#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-fun {0} ((x {1})) {2} (to_real x))
)";

ToReal::ToReal() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::UnaryOp::Real),
                         symbol(BType::INT), symbol(BType::REAL));
  m_label = "to_real";
  m_debug_string = "to_real";
}
};  // namespace BConstruct::Expression
