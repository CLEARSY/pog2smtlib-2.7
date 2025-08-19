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
       (and ({5} (fst p) ({6} 1 (- ({7} s) x)))
            ({4} (maplet (+ x (fst p)) (snd p)) s))))
  :named |ax.restrict.tail.def {8}|))
)";

Restrict_At_Tail::Restrict_At_Tail(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Tail_Restriction, T),
                  /*1*/ symbol(BType::INT),
                  /*2*/ symbol(PZxT),
                  /*3*/ symbol(ZxT),
                  /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT),
                  /*6*/ smtSymbol(Expr::BinaryOp::Interval),
                  /*7*/ smtSymbol(Expr::UnaryOp::Size, T),
                  /*8*/ symbolInner(T));
  m_label = "↓";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
       std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT),
       std::make_shared<BConstruct::Expression::Interval>(),
       std::make_shared<BConstruct::Expression::Size>(T)});
  m_debug_string = fmt::format("↓_{}", T.to_string());
}

};  // namespace BConstruct::Expression
