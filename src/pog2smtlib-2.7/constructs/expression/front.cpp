#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-fun {0} ((s {1})) {1} ({2} s (- ({3} s) 1)))
)";

Front::Front(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Front, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ smtSymbol(Expr::BinaryOp::Head_Restriction, T),
                         /*3*/ smtSymbol(Expr::UnaryOp::Size, T));
  m_label = "front";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Size>(T),
       std::make_shared<BConstruct::Expression::Restrict_In_Front>(T)});
  m_debug_string = fmt::format("front_{}", T.to_string());
}

};  // namespace BConstruct::Expression
