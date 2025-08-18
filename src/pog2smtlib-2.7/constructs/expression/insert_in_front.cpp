#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {2}) {2})
(assert (!
  (forall ((x {1})(s {2})(p {3}))
    (= ({4} p ({0} x s))
       (or (= p (maplet 1 x))
           ({4} (maplet (- (fst p) 1) (snd p)) s))))
  :named |ax.insert.front.def {5}|))
)";

Insert_In_Front::Insert_In_Front(const BType &T) : UnaryBType(T) {
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::BinaryOp::Head_Insertion, T),
                         /*1*/ symbol(T),
                         /*2*/ symbol(PZxT),
                         /*3*/ symbol(ZxT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, ZxT),
                         /*5*/ symbolInner(T));
  m_label = "→";
  m_prerequisites.insert({
      std::make_shared<BConstruct::Predicate::SetMembership>(ZxT),
  });
  m_debug_string = fmt::format("→_{}", T.to_string());
}

};  // namespace BConstruct::Expression
