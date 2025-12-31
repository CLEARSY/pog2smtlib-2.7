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

#include "../../bconstruct.h"

namespace BConstruct::Expression {

class Partial_Function : public BinaryBType {
 public:
  explicit Partial_Function(const BType &, const BType &,
                            const std::string &script,
                            const PreRequisites &requisites);
  virtual ~Partial_Function() = default;

 private:
  friend class BConstruct::Factory;
  static MapBinaryBType<Partial_Function> m_cache;
};

};  // namespace BConstruct::Expression
