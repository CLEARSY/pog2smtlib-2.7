#include "../../bconstruct.h"
#include "universe.h"

namespace BConstruct::Expression {

Integer::Integer() {
  m_script = universeScript("INTEGER", BType::INT);
  m_label = "INTEGER";
  m_prerequisites.insert(
      std::make_shared<Predicate::SetMembership>(BType::INT));
  m_debug_string = "INTEGER";
}

};  // namespace BConstruct::Expression
