#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {1}) {1})
(assert (!
  (forall ((a {1}) (b {1}))
    (and
      (=> (and (<= 0 a) (< 0 b))
        (= ({0} a b) (/ a b)))
      (=> (and (<= 0 a) (< b 0))
        (= ({0} a b) (- (/ a (- b)))))
      (=> (and (< a 0) (< 0 b))
        (= ({0} a b) (- (/ (- a) b))))
      (=> (and (<= a 0) (< b 0))
        (= ({0} a b) (/ a b)))))
  :named |ax.int.div :1|))
  )";

IntegerDivision::IntegerDivision() {
  m_script = fmt::format(SCRIPT, smtSymbol(Expr::BinaryOp::IDivision),
                         symbol(BType::INT));
  m_label = "/i";
  m_debug_string = "/i";
}
};  // namespace BConstruct::Expression
