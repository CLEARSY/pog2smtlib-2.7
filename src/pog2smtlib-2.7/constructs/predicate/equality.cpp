#include <fmt/core.h>

#include <string>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "btype.h"

namespace BConstruct::Predicate {

static constexpr std::string_view SCRIPT = R"(
(assert (!
  (forall ((s {1}) (t {1}))
    (=
      (= s t)
      (forall ((e |{0}|)) (= (|set.in {0}| e s) (|set.in {0}| e t)))
    )
  )
  :named |ax.set.eq {0}|))
)";

Equality::Equality(const BType &t) : UnaryBType(t) {
  if (t.getKind() == BType::Kind::PowerType) {
    const BType &u = t.toPowerType().content;
    m_script = fmt::format(SCRIPT, symbolInner(u), symbol(t));
    m_prerequisites.insert(std::make_shared<SetMembership>(u));
  }
  m_label = "=";
  m_debug_string = fmt::format("=_<{}>", t.to_string());
}

};  // namespace BConstruct::Predicate