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
