#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1}) {3})
(assert (!
  (forall ((X {1}))
    (= ({0} X)
       ({2}
         (lambda ((x {6}))
           (and ({5} (fst x) X) (= (fst x) (snd x)))))))
  :named |def.id {4}|))
)";

Identity::Identity(const BType &T) : UnaryBType(T) {
  const auto TxT = BType::PROD(T, T);
  const auto PT = BType::POW(T);
  const auto PTxT = BType::POW(TxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Identity, T),
                         /*1*/ symbol(PT),
                         /*2*/ smtSymbol(Expr::NaryOp::Set, TxT),
                         /*3*/ symbol(PTxT),
                         /*4*/ symbolInner(T),
                         /*5*/ smtSymbol(Pred::ComparisonOp::Membership, T),
                         /*6*/ symbol(TxT));
  m_label = "id";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(T),
       std::make_shared<BConstruct::Expression::Set>(TxT)});
  m_debug_string = fmt::format("id_<{}>", T.to_string());
}

};  // namespace BConstruct::Expression
