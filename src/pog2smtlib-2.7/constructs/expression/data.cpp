/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2025
  pog2smtlib-2.7 is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/
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
  m_prerequisites.insert(std::make_shared<BConstruct::Type::Type>(m_type));
  m_debug_string = fmt::format("Data<{}>", data.to_string());
  m_label = m_name;

  m_script = fmt::format("(declare-const {0} {1})\n", m_name, symbol(m_type));
}

};  // namespace BConstruct::Expression
