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
  (forall ((R {1})(p {2}))
    (= ({3} p ({0} R))
       (or (= (fst p) (snd p))
           ({3} p ({0} R)))))
  :named |ax.closure {4}|))
)";

Closure::Closure(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Closure, T),
                         /*1*/ symbol(PTxT),
                         /*2*/ symbol(TxT),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, TxT),
                         /*4*/ symbolInner(T));
  m_label = "closure";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(TxT)});
  m_debug_string = fmt::format("closure_{}", T.to_string());
}

};  // namespace BConstruct::Expression
