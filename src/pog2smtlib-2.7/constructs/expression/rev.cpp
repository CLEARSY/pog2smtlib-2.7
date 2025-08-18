#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) {1})
(assert (!
  (forall ((s {1})(p {2}))
    (= ({3} p ({0} s))
       ({3} (maplet (- (+ 1 ({4} s)) (fst p)) (snd p)) s)))
  :named |ax.set.in.rev {5}|))
)";

Rev::Rev(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Reverse, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ symbol(ZxT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*4*/ smtSymbol(Expr::UnaryOp::Size, T),
                         /*5*/ symbolInner(T));
  m_label = "rev";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
       std::make_shared<BConstruct::Expression::Size>(T)});
  m_debug_string = fmt::format("rev_{}", T.to_string());
}

};  // namespace BConstruct::Expression
