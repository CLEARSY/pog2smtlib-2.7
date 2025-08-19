#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({2}) {3})
(assert (!
  (forall ((s {2}) (t {2}))
    (=
      ({1} s ({0} t))
      ({4} s t)))
  :named |ax.sub-sets {5}|))
)";

PowerSet::PowerSet(const BType &T) : UnaryBType(T) {
  const auto PT = BType::POW(T);
  const auto PPT = BType::POW(PT);
  m_script = fmt::format(SCRIPT,
                         /*0*/ smtSymbol(Expr::UnaryOp::Subsets, T),
                         /*1*/ smtSymbol(Pred::ComparisonOp::Membership, PT),
                         /*2*/ symbol(PT),
                         /*3*/ symbol(PPT),
                         /*4*/ smtSymbol(Pred::ComparisonOp::Subset, T),
                         /*5*/ symbolInner(T));
  m_label = "POW";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(PT),
       std::make_shared<BConstruct::Predicate::Inclusion>(T)});
  m_debug_string = fmt::format("POW_{}", T.to_string());
}

};  // namespace BConstruct::Expression
