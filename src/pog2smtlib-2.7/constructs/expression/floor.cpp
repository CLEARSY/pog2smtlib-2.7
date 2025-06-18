#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-fun {0} ((x {1})) {2} (to_int x))
)";

Floor::Floor() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::UnaryOp::Floor),
                         symbol(BType::REAL), symbol(BType::INT));
  m_label = "floor";
  m_debug_string = "floor";
}
};  // namespace BConstruct::Expression
