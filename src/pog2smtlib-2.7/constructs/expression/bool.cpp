#include "../../bconstruct.h"
#include "universe.h"

namespace BConstruct::Expression {

Bool::Bool() {
  m_script = universeScript("BOOL", BType::BOOL);
  m_label = "BOOL";
  m_debug_string = "BOOL";
}

};  // namespace BConstruct::Expression