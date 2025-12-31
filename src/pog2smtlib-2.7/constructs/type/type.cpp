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
#include "type.h"

#include <fmt/core.h>

#include <iostream>
#include <string>

#include "../../bconstruct.h"
#include "../../btype-symbols.h"
#include "../../signature.h"
#include "../../translate-token.h"
#include "btype.h"
#include "cartesianproduct.h"
#include "powerset.h"
#include "pred.h"

using std::make_shared;
using std::set;
using std::shared_ptr;
using std::string;

namespace BConstruct {

namespace Type {

MapUnaryBType<Type> Type::m_cache;

Type::Type(const BType &T, const std::string &script,
           const PreRequisites &requisites)
    : UnaryBType(T, script, requisites, "_type") {}
};  // namespace Type

shared_ptr<Abstract> Factory::Type(const BType &T) {
  shared_ptr<Abstract> result = find(BConstruct::Type::Type::m_cache, T);
  if (!result) {
    std::string script = "";
    PreRequisites requisites = {};

    auto enumeratedValues = [](const std::vector<std::string> &values) {
      std::string result;
      for (size_t i = 0; i < values.size(); ++i) {
        result.push_back('(');
        result.append(values.at(i));
        result.push_back(')');
      }
      return result;
    };

    auto structValues =
        [](const std::vector<std::pair<std::string, BType>> &fds) {
          std::string result;
          for (size_t i = 0; i < fds.size(); ++i) {
            result.append(fmt::format("({0} {1})",
                                      smtSymbolRecField(fds[i].first),
                                      symbol(fds[i].second)));
          }
          return result;
        };

    switch (T.getKind()) {
      case BType::Kind::INTEGER:
        script = fmt::format("(define-sort {0} () Int)\n", symbol(T));
        break;
      case BType::Kind::BOOLEAN:
        script = fmt::format("(define-sort {0} () Bool)\n", symbol(T));
        break;
      case BType::Kind::FLOAT:
        throw std::runtime_error("No support for FLOAT data type");
        break;
      case BType::Kind::REAL:
        script = fmt::format("(define-sort {0} () Real)\n", symbol(T));
        break;
      case BType::Kind::STRING:
        script = fmt::format("(define-sort {0} () String)\n", symbol(T));
        break;
      case BType::Kind::ProductType: {
        const BType &U{T.toProductType().lhs};
        const BType &V{T.toProductType().rhs};
        script = fmt::format("(define-sort {0} () (C {1} {2}))\n", symbol(T),
                             symbol(U), symbol(V));
        requisites.insert(Factory::CartesianProduct());
        requisites.insert(Factory::Type(U));
        requisites.insert(Factory::Type(V));
        break;
      }
      case BType::Kind::PowerType: {
        const BType &U{T.toPowerType().content};
        script =
            fmt::format("(define-sort {0} () (P {1}))\n", symbol(T), symbol(U));
        requisites.insert(Factory::PowerSet());
        requisites.insert(Factory::Type(U));
        break;
      }
      case BType::Kind::AbstractSet:
        script = fmt::format("(declare-sort {0} 0)\n", symbol(T));
        break;
      case BType::Kind::EnumeratedSet:
        script =
            fmt::format("(declare-datatype {0} ({1}))\n", symbol(T),
                        enumeratedValues(T.toEnumeratedSetType().getContent()));
        break;
      case BType::Kind::Struct:
        script = fmt::format("(declare-datatype {0} (({1} {2})))\n", symbol(T),
                             symbolRecord(T),
                             structValues(T.toRecordType().m_fields));
        for (const auto &fd : T.toRecordType().m_fields) {
          requisites.insert(Factory::Type(fd.second));
        }
        break;
    }
    result = make<BConstruct::Type::Type>(BConstruct::Type::Type::m_cache, T,
                                          script, requisites);
  }
  return result;
}

};  // namespace BConstruct
