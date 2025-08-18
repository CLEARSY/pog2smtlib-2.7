#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun |surjections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}))
    (forall ((f {5}))
      (= ({6} f (|surjections {0} {1}| X Y))
         (= ({7} f) Y)
      )))
  :named |ax:set.in.surjections {8}|))
)";

Surjection::Surjection(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  const auto PPUxV = BType::POW(PUxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ symbolInner(U),
                         /*1*/ symbolInner(V),
                         /*2*/ symbol(PU),
                         /*3*/ symbol(PV),
                         /*4*/ symbol(PPUxV),
                         /*5*/ symbol(PUxV),
                         /*6*/ smtSymbol(Pred::ComparisonOp::Membership, PUxV),
                         /*7*/ smtSymbol(Expr::UnaryOp::Range, U, V),
                         /*8*/ symbolInner(UxV));
  m_label = "surj";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(PUxV),
       std::make_shared<BConstruct::Predicate::Equality>(PU),
       std::make_shared<BConstruct::Expression::Range>(U, V)});
  m_debug_string = fmt::format("surj_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression