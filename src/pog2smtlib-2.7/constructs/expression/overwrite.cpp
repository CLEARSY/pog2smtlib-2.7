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
  (forall ((r1 {1}) (r2 {1}))
    (forall ((x {2}))
      (= ({3} x ({0} r1 r2))
         (or (and ({3} x r1)
                  (not ({4} (fst x) ({5} r1))))
             ({3} x r2)))))
  :named |ax:set.in.overwrite {6}|))
)";

Overwrite::Overwrite(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Surcharge, U, V),
                         /*1*/ symbol(PUxV),
                         /*2*/ symbol(UxV),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                         /*5*/ smtSymbol(Expr::UnaryOp::Domain, U, V),
                         /*6*/ symbolInner(UxV));
  m_label = "<+";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(U),
       std::make_shared<BConstruct::Expression::Domain>(U, V)});
  m_debug_string = fmt::format("<+_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression