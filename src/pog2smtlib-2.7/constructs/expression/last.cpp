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
    ({3} (maplet ({4} s) ({0} s)) s))
  :named |ax.last.definition {5}|))
)";

Last::Last(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Last, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ symbol(T),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*4*/ smtSymbol(Expr::UnaryOp::Size, T),
                         /*5*/ symbolInner(T));
  m_label = "last";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
       std::make_shared<BConstruct::Expression::Size>(T)});
  m_debug_string = fmt::format("last_{}", T.to_string());
}

};  // namespace BConstruct::Expression
