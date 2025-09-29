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

struct DataHash {
  size_t operator()(const std::shared_ptr<const struct Data> &dt) const {
    return dt->m_name->hash_combine(0);
  }
};

struct DataEqual {
  bool operator()(const std::shared_ptr<const struct Data> &lhs,
                  const std::shared_ptr<const struct Data> &rhs) const {
    constexpr bool debug_me = false;
    const bool result =
        lhs->to_string() == rhs->to_string() && *lhs->m_type == *rhs->m_type;
    if (debug_me) {
      std::cerr << fmt::format("DataEqual({0}: {2}, {1}: {3}) == {4}",
                               lhs->to_string(), rhs->to_string(),
                               lhs->m_type->to_string(),
                               rhs->m_type->to_string(), result)
                << std::endl;
    }
    return result;
  }
};

using MapData =
    std::unordered_map<std::shared_ptr<const struct Data>,
                       std::shared_ptr<BConstruct::Expression::Data>, DataHash,
                       DataEqual>;

namespace BConstruct::Expression {

class Data : public std::enable_shared_from_this<Data>, public Uniform {
 public:
  explicit Data(const struct ::Data &dt, const std::string &,
                std::set<std::shared_ptr<Abstract>> &);
  virtual ~Data() = default;

  Data &operator=(const Data &) = delete;
  Data(Data &&) = delete;

  const BType &type() const { return m_type; }

 private:
  const BType &m_type;
  const std::string m_name;

 private:
  friend class BConstruct::Factory;
  static MapData m_cache;
};

};  // namespace BConstruct::Expression
