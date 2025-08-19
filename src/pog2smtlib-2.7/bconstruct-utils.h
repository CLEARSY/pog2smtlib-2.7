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
#ifndef BCONSTRUCT_HASH_H
#define BCONSTRUCT_HASH_H

#include <cstddef>
#include <memory>

#include "bconstruct.h"

namespace BConstruct {

struct PtrHash {
  std::size_t operator()(const std::shared_ptr<BConstruct::Abstract> &t) const {
    return t->hash();
  }
};

struct PtrCompare {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const {
    return *a < *b;
  }
};

struct PtrEqual {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const {
    return *a == *b;
  }
};

};  // namespace BConstruct

#endif  // BCONSTRUCT_HASH_H
