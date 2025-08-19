#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun |injections {0} {1}| ({2} {3}) {4})
(assert (!
  (forall ((X {2}) (Y {3}) (f {5}))
     (= ({6} f (|injections {0} {1}| X Y))
        (forall ((p1 {7}) (p2 {7}))
          (=> (and ({8} p1 f) ({8} p2 f) (= (snd p1) (snd p2)))
              (= (fst p1) (fst p2))))))
  :named |ax:set.in.injections {9}|))
)";

Injection::Injection(const BType &U, const BType &V) : BinaryBType(U, V) {
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
                         /*7*/ symbol(UxV),
                         /*8*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*9*/ symbolInner(UxV));
  m_label = "inj";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(PUxV),
       std::make_shared<BConstruct::Predicate::Equality>(U),
       std::make_shared<BConstruct::Predicate::Equality>(V)});
  m_debug_string = fmt::format("inj_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
