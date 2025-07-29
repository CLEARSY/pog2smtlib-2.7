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
  (forall ((f {1})(p {3}))
    (= ({4} p ({0} f))
    (and (exists ((p2 {5})) (and ({6} p2 f) (= (fst p) (fst p2))
         ({7} (snd p) (snd p2)))))))
    :named |ax.rel {8}|))
)";

Transformed_Into_Relation::Transformed_Into_Relation(const BType &U,
                                                     const BType &V)
    : BinaryBType(U, V) {
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto UxPV = BType::PROD(U, PV);
  const auto PUxPV = BType::POW(UxPV);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Rel, U, V),
                         /*1*/ symbol(PUxPV),
                         /*2*/ symbol(PUxV),
                         /*3*/ symbol(UxV),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*5*/ symbol(UxPV),
                         /*6*/ smtSymbol(Pred::ComparisonOp::Membership, UxPV),
                         /*7*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                         /*8*/ symbolInner(UxV));
  m_label = "rel";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(UxPV),
       std::make_shared<BConstruct::Predicate::SetMembership>(V)});
  m_debug_string = fmt::format("rel_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
