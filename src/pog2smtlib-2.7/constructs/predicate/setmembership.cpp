#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "btype.h"
#include "pred.h"
namespace BConstruct::Predicate {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {2}) Bool)
)";

SetMembership::SetMembership(const BType &t) : UnaryBType(t) {
  const BType pt = BType::POW(t);
  const std::string op = smtSymbol(Pred::ComparisonOp::Membership, t);
  m_script = fmt::format(SCRIPT, op, symbol(t), symbol(pt));
  m_prerequisites.insert(std::make_shared<BConstruct::Type::Type>(pt));
  m_label = ":";
  m_debug_string = fmt::format(":_<{}>", t.to_string());
}

};  // namespace BConstruct::Predicate
