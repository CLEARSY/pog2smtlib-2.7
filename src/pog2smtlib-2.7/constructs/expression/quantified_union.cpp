#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} (|? {1}| (-> {2} {3})) {3})
(assert (!
  (forall ((P |? {1}|)(E (-> {2} {3}))(x {5}))
    (= ({4} x ({0} P E))
       (exists ((e {2})) (and (P e) ({4} x (E e))))))
  :named |ax.set.in.quantified.union {6}|))
)";

Quantified_Union::Quantified_Union(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::QuantifiedOp::Union, U, V),
                         /*1*/ symbolInner(U),
                         /*2*/ symbol(U),
                         /*3*/ symbol(PV),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                         /*5*/ symbol(V),
                         /*6*/ symbolInner(UxV));
  m_label = "UNION";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(V),
       std::make_shared<BConstruct::Expression::Set>(U)});
  m_debug_string = fmt::format("UNION_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
