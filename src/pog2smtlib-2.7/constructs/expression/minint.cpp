#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-const {0} {1} {2})
)";

Minint::Minint() {
  std::string smtLiteral;
  if (Parameters::MININT.at(0) == '-') {
    smtLiteral = fmt::format(
        "(- {})", Parameters::MININT.substr(1, Parameters::MININT.size() - 1));
  } else {
    smtLiteral = Parameters::MININT;
  }

  m_script = fmt::format(SCRIPT, smtSymbol(Expr::Visitor::EConstant::MinInt),
                         symbol(BType::INT), smtLiteral);
  m_label = "MININT";
  m_debug_string = "MININT";
}
};  // namespace BConstruct::Expression
