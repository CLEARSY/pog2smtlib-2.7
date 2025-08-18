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
    (= ({0} s) (Value ({3} s))))
  :named |ax.size.definition {4}|))
)";

Size::Size(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Size, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ symbol(BType::INT),
                         /*3*/ smtSymbol(Expr::UnaryOp::Cardinality, ZxT),
                         /*4*/ symbolInner(T));
  m_label = "size";
  m_prerequisites.insert({std::make_shared<BConstruct::Expression::Card>(ZxT)});
  m_debug_string = fmt::format("size_{}", T.to_string());
}

};  // namespace BConstruct::Expression
