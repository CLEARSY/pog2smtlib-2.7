#include "../../bconstruct.h"
#include "universe.h"

namespace BConstruct::Expression {

Real::Real() {
  m_script = universeScript("REAL", BType::REAL);
  m_label = "REAL";
  m_debug_string = "REAL";
}

};  // namespace BConstruct::Expression