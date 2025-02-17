#include <fmt/core.h>

#include <string>
#include <string_view>

#include "../../btype-symbols.h"
#include "btype.h"

namespace BConstruct::Expression {
inline constexpr std::string_view SET_UNIVERSE_SCRIPT = R"(
(declare-const {0} {3})
(assert (!
  (forall ((e {1})) (|set.in {2}| e {0}))
  :named |ax.set.in.{0}|))
)";

inline std::string universeScript(const std::string name, const BType& type) {
  // BType ptype = BType::POW(type);
  return fmt::format(SET_UNIVERSE_SCRIPT, name, symbol(type), symbolInner(type),
                     symbol(BType::POW(type)));
}
};  // namespace BConstruct::Expression