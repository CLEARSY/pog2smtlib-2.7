#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) {2})
(assert (!
  (forall ((s {1}))
    ({3} (maplet 1 ({0} s)) s))
  :named |ax.first.definition {4}|))
)";

First::First(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::First, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ symbol(T),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*4*/ symbolInner(T));
  m_label = "first";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(ZxT)});
  m_debug_string = fmt::format("first_{}", T.to_string());
}

};  // namespace BConstruct::Expression
