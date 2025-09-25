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
#include "bool.h"

#include "../../bconstruct.h"
#include "universe.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {
namespace Expression {

std::shared_ptr<Bool> Bool::m_cache;

Bool::Bool(const std::string &script, set<shared_ptr<Abstract>> &requisites)
    : Uniform(script, requisites, "BOOL") {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Bool() {
  shared_ptr<Abstract> result = find(BConstruct::Expression::Bool::m_cache);
  if (!result) {
    const string script = Expression::universeScript("BOOL", BType::BOOL);
    set<shared_ptr<Abstract>> requisites{Factory::SetMembership(BType::BOOL)};
    result = make(BConstruct::Expression::Bool::m_cache, script, requisites);
  }
  return result;
}

};  // namespace BConstruct
