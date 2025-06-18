#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-fun {0} ((x {1})) {2} (+ 1 (to_int x)))
)";

Ceiling::Ceiling() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::UnaryOp::Ceiling),
                         symbol(BType::REAL), symbol(BType::INT));
  m_label = "ceiling";
  m_debug_string = "ceiling";
}
};  // namespace BConstruct::Expression
