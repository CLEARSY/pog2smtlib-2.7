#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Predicate {

static constexpr std::string_view SCRIPT =
    R"((declare-fun {0} ({1} {1}) Bool)
(assert (!
    (forall ((s {1}) (t {1}))
      (=
        ({0} s t)
        (forall ((e |{2}|)) (=> ({3} e s) ({3} e t)))
      )
    )
    :named |ax.set.subseteq {2}|))
)";

Inclusion::Inclusion(const BType &t) : UnaryBType(t) {
  const BType pt = BType::POW(t);
  m_script =
      fmt::format(SCRIPT, smtSymbol(Pred::ComparisonOp::Subset, t), symbol(pt),
                  symbolInner(t), smtSymbol(Pred::ComparisonOp::Membership, t));
  m_prerequisites.insert(std::make_shared<SetMembership>(t));
  m_label = "<:";
  m_debug_string = fmt::format("<:_<{}>", t.to_string());
}

};  // namespace BConstruct::Predicate
