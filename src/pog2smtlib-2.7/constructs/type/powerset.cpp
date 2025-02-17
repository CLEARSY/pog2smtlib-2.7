#include "../../bconstruct.h"

namespace BConstruct::Type {

PowerSet::PowerSet() {
  m_script = "(declare-sort P 1)\n";
  m_label = "POW";
  m_debug_string = "PowerSet";
}

};  // namespace BConstruct::Type
