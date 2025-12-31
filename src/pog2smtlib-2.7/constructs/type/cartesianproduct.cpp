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
#include "cartesianproduct.h"

#include "../../bconstruct.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

namespace Type {

shared_ptr<CartesianProduct> CartesianProduct::m_cache;

CartesianProduct::CartesianProduct(const string& script,
                                   const PreRequisites& requisites)
    : Uniform(script, requisites, "*") {}

CartesianProduct::CartesianProduct() {
  m_script =
      "(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))\n";
  m_label = "*";
  m_debug_string = "CartesianProduct";
}

};  // namespace Type

shared_ptr<Abstract> Factory::CartesianProduct() {
  std::shared_ptr<Abstract> result =
      find(BConstruct::Type::CartesianProduct::m_cache);
  if (!result) {
    const string script =
        "(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))\n";
    const PreRequisites requisites{};
    result =
        make(BConstruct::Type::CartesianProduct::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
