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
      throw std::runtime_error("Struct type not supported");
      break;
  }
}

};  // namespace BConstruct::Type
