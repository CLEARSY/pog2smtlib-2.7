#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "../../translate-token.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun {0} ({1} {2}) {4})
(assert (!
  (forall ((X {1}) (Y {2}))
    (= ({0} X Y)
       ({3} ({5} X Y))))
    :named |def.relations {6}|))
)";

Relation::Relation(const BType &U, const BType &V) : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  const auto PPUxV = BType::POW(PUxV);
  m_script =
      fmt::format(SCRIPT,
                  /*0*/ smtSymbol(Expr::BinaryOp::Relations, U, V),
                  /*1*/ symbol(PU),
                  /*2*/ symbol(PV),
                  /*3*/ smtSymbol(Expr::UnaryOp::Subsets, UxV),
                  /*4*/ symbol(PPUxV),
                  /*5*/ smtSymbol(Expr::BinaryOp::Cartesian_Product, U, V),
                  /*6*/ symbolInner(UxV));
  m_label = "<->";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Expression::CartesianProduct>(U, V),
       std::make_shared<BConstruct::Expression::PowerSet>(UxV)});
  m_debug_string = fmt::format("<->_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
