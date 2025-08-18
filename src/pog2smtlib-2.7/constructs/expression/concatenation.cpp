#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {1}) {1})
(assert (!
  (forall ((s1 {1})(s2 {1})(p {2}))
    (= ({3} p ({0} s1 s2))
       (or ({3} p s1)
           ({3} (maplet (- (fst p) ({4} s1)) (snd p)) s2))))
  :named |ax.conc.definition {5}|
))
)";

Concatenation::Concatenation(const BType &T)
    : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT, 
                         /*0*/ smtSymbol(Expr::BinaryOp::Concatenation, T),
                         /*1*/ symbol(PZxT),
                         /*2*/ symbol(ZxT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*4*/ smtSymbol(Expr::UnaryOp::Size, T),
                         /*5*/ symbolInner(T));
  m_label = "^";
  m_prerequisites.insert({
       std::make_shared<BConstruct::Predicate::SetMembership>(T),
       std::make_shared<BConstruct::Expression::Size>(T),
    });
  m_debug_string = fmt::format("^_{}", T.to_string());
}

};  // namespace BConstruct::Expression
