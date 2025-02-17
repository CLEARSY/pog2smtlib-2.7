#include <fmt/core.h>

#include <string>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../signature.h"
#include "btype.h"
#include "pred.h"

namespace BConstruct::Expression {

Data::Data(const struct ::Data &data)
    : enable_shared_from_this<BConstruct::Expression::Data>(),
      BConstruct::Uniform(),
      m_type(data.m_type),
      m_name(data.to_string()) {
  m_debug_string = fmt::format("Data<{}>", data.to_string());
  m_label = m_name;

  m_script = fmt::format("(declare-const {0} {1})\n", m_name, symbol(m_type));
}

};  // namespace BConstruct::Expression
