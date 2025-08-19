#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-const |seq.empty {0}| {1})
(assert (!
  (= |seq.empty {0}| {2})
  :named |ax:seq.empty.def {0}|))
)";

EmptySeq::EmptySeq(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ symbolInner(T),
                  /*1*/ symbol(PZxT),
                  /*2*/ smtSymbol(Expr::Visitor::EConstant::EmptySet, ZxT));
  m_label = "[]";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::EmptySet>(ZxT)});
  m_debug_string = fmt::format("[]_{}", T.to_string());
}

};  // namespace BConstruct::Expression
