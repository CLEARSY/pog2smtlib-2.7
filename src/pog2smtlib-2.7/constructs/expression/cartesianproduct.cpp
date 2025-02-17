#include <fmt/core.h>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../parameters.h"
#include "btype.h"

namespace BConstruct::Expression {

static constexpr std::string_view SCRIPT = R"(
(declare-fun |set.product {0} {2}| ({1} {3}) ({5})))
(assert (!
  (forall ((s1 {1}) (s2 {3}))
    (forall ((p {4}))
      (= (|set.in {4}| p (|set.product {0} {2}| s1 s2))
         (and (|set.in {0}| (fst p) s1) (|set.in {2}| (snd p) s2)))))
  :named |ax.set.in.product.1 {0}|))
(assert (!
  (forall ((s1 {1}) (s2 {3}))
    (forall ((x1 {0}) (x2 {2}))
      (= (|set.in {4}| (maplet x1 x2) (|set.product {0} {2}| s1 s2))
         (and (|set.in {0}| x1 s1) (|set.in {2}| x2 s2)))))
      :named |ax.set.in.product.2 {0}|))
)";

CartesianProduct::CartesianProduct(const BType &U, const BType &V)
    : BinaryBType(U, V) {
  const auto PU = BType::POW(U);
  const auto PV = BType::POW(V);
  const auto UxV = BType::PROD(U, V);
  const auto PUxV = BType::POW(UxV);
  m_script = fmt::format(SCRIPT, symbolInner(U), symbol(PU), symbolInner(V),
                         symbol(PV), symbolInner(UxV), symbol(PUxV));
  m_label = "*";
  m_prerequisites.insert(
      {std::make_shared<BConstruct::Predicate::SetMembership>(U),
       std::make_shared<BConstruct::Predicate::SetMembership>(V),
       std::make_shared<BConstruct::Predicate::SetMembership>(UxV)});
  m_debug_string = fmt::format("*_<{},{}>", U.to_string(), V.to_string());
}

};  // namespace BConstruct::Expression
