#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-const {0} {2})
 (assert (!
 (forall ((e {1})) (= (|set.in {3}| e {0}) (and (<= 0 e) (<= e {4}))))
 :named |ax.set.in.NAT|))
)";

Nat::Nat() {
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::Visitor::EConstant::NAT),
                         /*1*/ symbol(BType::INT),
                         /*2*/ symbol(BType::POW(BType::INT)),
                         /*3*/ symbolInner(BType::INT),
                         /*4*/ smtSymbol(Expr::Visitor::EConstant::MaxInt));
  m_label = "NAT";
  m_prerequisites.insert(
      {std::make_shared<Predicate::SetMembership>(BType::INT),
       std::make_shared<BConstruct::Expression::Maxint>()});
  m_debug_string = "NAT";
}
};  // namespace BConstruct::Expression
