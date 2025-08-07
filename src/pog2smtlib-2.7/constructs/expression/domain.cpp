#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) {1})
(assert (!
  (forall ((r {2}) (e |{6}|))
    (= ({3} e ({0} r))
       (exists ((y |{7}|)) ({4} (maplet e y) r))))
  :named |ax:set.in.domain {5}|))
)";

Domain::Domain(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Domain, U, V),
                         /*1*/ symbol(PU),
                         /*2*/ symbol(PUxV),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, U),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Membership, UxV),
                         /*5*/ symbolInner(UxV),
                         /*6*/ symbolInner(U),
                         /*7*/ symbolInner(V));
  m_label = "dom";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(UxV),
       std::make_shared<BConstruct::Predicate::SetMembership>(U)});
  m_debug_string = fmt::format("dom_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression