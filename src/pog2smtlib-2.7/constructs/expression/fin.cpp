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
  (forall ((s {1}) (t {1}))
    (= ({3} s ({0} t))
       (and
         ({3} s ({4} t))
         (not (= ({5} s) Infinite)))))
  :named |ax.finite sub-sets {6}|))
)";

Fin::Fin(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto PPT = BType::POW(PT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Finite_Subsets, T),
                         /*1*/ symbol(PT),
                         /*2*/ symbol(PPT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                         /*4*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                         /*5*/ smtSymbol(Expr::UnaryOp::Cardinality, T),
                         /*6*/ symbolInner(T));
  m_label = "FIN";
  m_prerequisites.insert({std::make_shared<BConstruct::Expression::PowerSet>(T),
                          std::make_shared<BConstruct::Expression::Card>(T)});
  m_debug_string = fmt::format("FIN_{}", T.to_string());
}

};  // namespace BConstruct::Expression
