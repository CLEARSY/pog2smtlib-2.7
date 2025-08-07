#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(define-sort |? {0}| () (-> {1} Bool))
(declare-const {2} (-> |? {0}| {3}))
(assert (!
  (forall ((p |? {0}|))
    (forall ((x {1}))
      (= ({4} x ({2} p))
         (p x))))
  :named |ax:set.in.intent {0}|))
)";

Set::Set(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  m_script = fmt::format(SCRIPT,
                         /*0*/ symbolInner(T),
                         /*1*/ symbol(T),
                         /*2*/ smtSymbol(Expr::NaryOp::Set, T),
                         /*3*/ symbol(PT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, T));
  m_label = "?";
  m_prerequisites.insert(
      std::make_shared<BConstruct::Predicate::SetMembership>(T));
  m_debug_string = fmt::format("?_{}", T.to_string());
}

};  // namespace BConstruct::Expression
