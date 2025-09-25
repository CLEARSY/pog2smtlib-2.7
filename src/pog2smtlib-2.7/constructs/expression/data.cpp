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
#include "data.h"

#include <fmt/core.h>

#include <string>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../signature.h"
#include "../type/type.h"
#include "btype.h"
#include "pred.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;
namespace BConstruct {

static constexpr std::string_view SCRIPT = "(declare-const {0} {1})\n";

namespace Expression {

MapData Data::m_cache;

Data::Data(const struct ::Data &data, const string &script,
           set<shared_ptr<Abstract>> &requisites)
    : enable_shared_from_this<Data>(),
      BConstruct::Uniform(script, requisites,
                          fmt::format("_data<{}>", data.to_string())),
      m_type(*data.m_type),
      m_name(data.to_string()) {}

};  // namespace Expression

shared_ptr<Abstract> Factory::Data(const struct Data &data) {
  shared_ptr<const struct Data> pt = make_shared<const struct Data>(data);
  auto it = BConstruct::Expression::Data::m_cache.find(pt);
  if (it != BConstruct::Expression::Data::m_cache.end()) {
    return it->second;
  }
  const BType &type{data.type()};
  const string script = fmt::format(SCRIPT, data.to_string(), symbol(type));
  set<shared_ptr<Abstract>> requisites{Factory::Type(type)};
  auto construct =
      make_shared<BConstruct::Expression::Data>(data, script, requisites);
  BConstruct::Expression::Data::m_cache[pt] = construct;
  index(construct);
  return construct;
}

};  // namespace BConstruct
