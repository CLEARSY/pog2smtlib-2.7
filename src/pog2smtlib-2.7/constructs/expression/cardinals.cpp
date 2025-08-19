#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-datatype Cardinals ( ( Infinite ) ( Finite ( Value Int ) )))
)";

Cardinals::Cardinals() {
  m_script = fmt::format(SCRIPT);
  m_label = "cardinals";
  m_debug_string = "cardinals";
}
};  // namespace BConstruct::Expression
