#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-fun {0} ((s {1})) {1} ({2} s 1)
)";

Tail::Tail(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Tail, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ smtSymbol(Expr::BinaryOp::Tail_Restriction, T));
  m_label = "tail";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Restrict_At_Tail>(T)});
  m_debug_string = fmt::format("tail_{}", T.to_string());
}

};  // namespace BConstruct::Expression
