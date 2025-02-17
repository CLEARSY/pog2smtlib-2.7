#include "../../bconstruct.h"

namespace BConstruct::Type {

CartesianProduct::CartesianProduct() {
  m_script =
      "(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))\n";
  m_label = "*";
  m_debug_string = "CartesianProduct";
}

};  // namespace BConstruct::Type
