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

namespace BConstruct::Type {

Type::Type(const BType &type) : UnaryBType(type) {
  m_debug_string = fmt::format("Type<{}>", type.to_string());
  m_label = "Type";
  // auxiliary function to build string for list of enumerated type elements
  auto enumeratedValues = [](const std::vector<std::string> &values) {
    std::string result;
    for (size_t i = 0; i < values.size(); ++i) {
      result += " ";
      result += values.at(i);
    }
    return result;
  };

  auto structValues =
      [](const std::vector<std::pair<std::string, BType>> &fds) {
        std::string result;
        for (size_t i = 0; i < fds.size(); ++i) {
          if (i == fds.size() - 1) {
            result += "(";
            result += fds[i].first;
            result += " ";
            result += fds[i].second.to_string();
            result += ")";
          } else {
            result += "(";
            result += fds[i].first;
            result += " ";
            result += symbolInner(fds[i].second);
            result += ") ";
          }
        }
        return result;
      };

  switch (type.getKind()) {
    case BType::Kind::INTEGER:
      m_script = fmt::format("(define-sort {0} () Int)\n", symbol(type));
      break;
    case BType::Kind::BOOLEAN:
      m_script = fmt::format("(define-sort {0} () Bool)\n", symbol(type));
      break;
    case BType::Kind::FLOAT:
      throw std::runtime_error("No support for FLOAT data type");
      break;
    case BType::Kind::REAL:
      m_script = fmt::format("(define-sort {0} () Real)\n", symbol(type));
      break;
    case BType::Kind::STRING:
      m_script = fmt::format("(define-sort {0} () String)\n", symbol(type));
      break;
    case BType::Kind::ProductType: {
      const BType &typel{type.toProductType().lhs};
      const BType &typer{type.toProductType().rhs};
      m_script = fmt::format("(define-sort {0} () (C {1} {2}))\n", symbol(type),
                             symbol(typel), symbol(typer));
      m_prerequisites.insert(std::make_shared<CartesianProduct>());
      m_prerequisites.insert(std::make_shared<Type>(typel));
      m_prerequisites.insert(std::make_shared<Type>(typer));
      break;
    }
    case BType::Kind::PowerType: {
      const BType &typee{type.toPowerType().content};
      m_script = fmt::format("(define-sort {0} () (P {1}))\n", symbol(type),
                             symbol(typee));
      m_prerequisites.insert(std::make_shared<PowerSet>());
      m_prerequisites.insert(std::make_shared<Type>(typee));
      break;
    }
    case BType::Kind::AbstractSet:
      m_script = fmt::format("(define-sort {0} 0))\n", symbol(type));
      break;
    case BType::Kind::EnumeratedSet:
      m_script = fmt::format(
          "(declare-datatype {0} ({1})))\n", symbol(type),
          enumeratedValues(type.toEnumeratedSetType().getContent()));
      break;
    case BType::Kind::Struct:
      m_script = fmt::format("(declare-datatype {0} ((|record {1}| {2})))\n",
                             symbol(type), symbolInner(type),
                             structValues(type.toRecordType().m_fields));
      for (const auto &fd : type.toRecordType().m_fields) {
        m_prerequisites.insert(std::make_shared<Type>(fd.second));
      }
      break;
  }
}

};  // namespace BConstruct::Type
