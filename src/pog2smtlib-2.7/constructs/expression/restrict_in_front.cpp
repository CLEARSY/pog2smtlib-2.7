#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2} {1}) {2})
(assert (!
  (forall ((s {2})(x {1})(p {3}))
    (= ({4} p ({0} s x))
       (and ({5} (fst p) ({6} 1 x))
            ({4} p s))))
  :named |ax.restrict.front.def {7}|))
)";

Restrict_In_Front::Restrict_In_Front(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Head_Restriction, T),
                  /*1*/ symbol(T),
                  /*2*/ symbol(PZxT),
                  /*3*/ symbol(ZxT),
                  /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
                  /*6*/ smtSymbol(Expr::BinaryOp::Interval),
                  /*7*/ symbolInner(T));
  m_label = "↑";
  m_prerequisites.insert({
      std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
      std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT),
      std::make_shared<BConstruct::Expression::Interval>(),
  });
  m_debug_string = fmt::format("↑_{}", T.to_string());
}

};  // namespace BConstruct::Expression
