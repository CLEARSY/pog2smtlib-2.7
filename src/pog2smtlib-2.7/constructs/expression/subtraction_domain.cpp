#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2} {1}) {1})
(assert (!
  (forall ((r {1}) (e {2}))
    (forall ((x {3}))
      (= ({4} x ({0} e r))
        (and ({4} x r) (not ({5} (fst x) e))))))
  :named |ax:set.in.subtract.dom {6}|))
)";

Subtraction_Domain::Subtraction_Domain(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Domain_Subtraction, U, V),
                  /*1*/ symbol(PUxV),
                  /*2*/ symbol(PU),
                  /*3*/ symbol(UxV),
                  /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                  /*5*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                  /*6*/ symbolInner(UxV));
  m_label = "<<|";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(U)});
  m_debug_string = fmt::format("<<|_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression