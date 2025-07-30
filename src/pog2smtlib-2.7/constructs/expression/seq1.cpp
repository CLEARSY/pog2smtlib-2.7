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
  (forall ((E {1})(s {3}))
    (= ({4} s ({0} E))
       (and ({4} s ({5} E)) (not (= s |seq.empty {6}|)))))
  :named |ax.seq1 {6}|))
)";

Seq1::Seq1(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto ZxT = BType::PROD(BType::INT, T);
  const auto PZxT = BType::POW(ZxT);
  const auto PPZxT = BType::POW(PZxT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Non_Empty_Sequences, T),
                         /*1*/ symbol(PT),
                         /*2*/ symbol(PPZxT),
                         /*3*/ symbol(PZxT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, PZxT),
                         /*5*/ smtSymbol(Expr::UnaryOp::Sequences, T),
                         /*6*/ symbolInner(T));
  m_label = "seq1";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::Seq>(T),
       std::make_shared<BConstruct::Predicate::SetMembership>(PZxT),
       std::make_shared<BConstruct::Expression::EmptySeq>(T)});
  m_debug_string = fmt::format("seq1_{}", T.to_string());
}

};  // namespace BConstruct::Expression
