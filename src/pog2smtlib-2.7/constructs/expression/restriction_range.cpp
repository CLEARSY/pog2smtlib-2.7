#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {2}) {1})
(assert (!
  (forall ((r {1}) (e {2}))
    (forall ((x {3}))
      (= ({4} x ({0} r e))
         (and ({4} x r) ({5} (snd x) e)))))
  :named |ax:set.in.restrict.ran {6}|))
)";

Restriction_Range::Restriction_Range(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Range_Restriction, U, V),
                  /*1*/ symbol(PUxV),
                  /*2*/ symbol(PV),
                  /*3*/ symbol(UxV),
                  /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, V),
                  /*6*/ symbolInner(UxV));
  m_label = "▷";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(V)});
  m_debug_string = fmt::format("▷_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression