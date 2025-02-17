#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-const |MAXINT| {0} {1})
)";

Maxint::Maxint() {
  m_script = fmt::format(SCRIPT, symbol(BType::INT), Parameters::MAXINT);
  m_label = "MAXINT";
  m_debug_string = "MAXINT";
}

};  // namespace BConstruct::Expression