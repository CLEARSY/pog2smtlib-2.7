 #include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {1}) {2})
 (assert (!
    (forall ((l {1}) (u {1}) (e {1}))
        (= ({3} e ({0} l u))
            (and (<= l e) (<= e u))))
    :named |ax.set.in.interval|))
)";

Interval::Interval() {
  const auto PZ = BType::POW(BType::INT);
  m_script = fmt::format(SCRIPT, 
                         /*0*/ smtSymbol(Expr::BinaryOp::Interval),
                         /*1*/ symbol(BType::INT),
                         /*2*/ symbol(PZ),
                         /*3*/ smtSymbol(Pred::ComparisonOp::Membership, BType::INT));
  m_label = "..";
  m_prerequisites.insert(
        std::make_shared<BConstruct::Predicate::SetMembership>(BType::INT)
    );
  m_debug_string = fmt::format("..");
}

};  // namespace BConstruct::Expression                                     
