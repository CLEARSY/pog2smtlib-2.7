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

Maplet::Maplet() {
  m_script = "";
  m_prerequisites.insert(
      std::make_shared<BConstruct::Type::CartesianProduct>());
  m_label = "|->";
  m_debug_string = "|->";
}
};  // namespace BConstruct::Expression
