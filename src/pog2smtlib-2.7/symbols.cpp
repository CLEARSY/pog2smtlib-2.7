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
#include "symbols.h"

#include <map>
#include <string>

/** @desc maps each constant operators to the string used to build symbols */
static const std::map<Expr::Visitor::EConstant, std::string> ConstantDict = {
    {Expr::Visitor::EConstant::MaxInt, "MAXINT"},
    {Expr::Visitor::EConstant::MinInt, "MININT"},
    {Expr::Visitor::EConstant::INTEGER, "INTEGER"},
    {Expr::Visitor::EConstant::NATURAL, "NATURAL"},
    {Expr::Visitor::EConstant::NATURAL1, "NATURAL1"},
    {Expr::Visitor::EConstant::INT, "INT"},
    {Expr::Visitor::EConstant::NAT, "NAT"},
    {Expr::Visitor::EConstant::NAT1, "NAT1"},
    {Expr::Visitor::EConstant::STRING, "STRING"},
    {Expr::Visitor::EConstant::BOOL, "BOOL"},
    {Expr::Visitor::EConstant::REAL, "REAL"},
    {Expr::Visitor::EConstant::FLOAT, "FLOAT"},
    {Expr::Visitor::EConstant::TRUE, "TRUE"},
    {Expr::Visitor::EConstant::FALSE, "FALSE"},
    {Expr::Visitor::EConstant::EmptySet, "{}"},
    {Expr::Visitor::EConstant::Successor, "succ"},
    {Expr::Visitor::EConstant::Predecessor, "pred"},
};

auto fmt::formatter<BOperator>::format(BOperator op, format_context &ctx) const
    -> format_context::iterator {
  std::string_view name = "unknown operator";
  if (std::holds_alternative<Pred::ComparisonOp>(op)) {
    name = Pred::to_string(std::get<Pred::ComparisonOp>(op));
  } else if (std::holds_alternative<Expr::UnaryOp>(op)) {
    name = Expr::to_string(std::get<Expr::UnaryOp>(op));
  } else if (std::holds_alternative<Expr::BinaryOp>(op)) {
    name = Expr::to_string(std::get<Expr::BinaryOp>(op));
  } else if (std::holds_alternative<Expr::TernaryOp>(op)) {
    name = Expr::to_string(std::get<Expr::TernaryOp>(op));
  } else if (std::holds_alternative<Expr::NaryOp>(op)) {
    name = Expr::to_string(std::get<Expr::NaryOp>(op));
  } else if (std::holds_alternative<Expr::Visitor::EConstant>(op)) {
    name = ConstantDict.at(std::get<Expr::Visitor::EConstant>(op));
  } else if (std::holds_alternative<Expr::EKind>(op)) {
    if (std::get<Expr::EKind>(op) == Expr::EKind::QuantifiedSet) {
      name = "?";
    }
  }
  return formatter<string_view>::format(name, ctx);
}

std::string to_string(BOperator op) {
  if (std::holds_alternative<Pred::ComparisonOp>(op)) {
    return Pred::to_string(std::get<Pred::ComparisonOp>(op));
  } else if (std::holds_alternative<Expr::UnaryOp>(op)) {
    return Expr::to_string(std::get<Expr::UnaryOp>(op));
  } else if (std::holds_alternative<Expr::BinaryOp>(op)) {
    return Expr::to_string(std::get<Expr::BinaryOp>(op));
  } else if (std::holds_alternative<Expr::TernaryOp>(op)) {
    return Expr::to_string(std::get<Expr::TernaryOp>(op));
  } else if (std::holds_alternative<Expr::NaryOp>(op)) {
    return Expr::to_string(std::get<Expr::NaryOp>(op));
  } else if (std::holds_alternative<Expr::Visitor::EConstant>(op)) {
    return ConstantDict.at(std::get<Expr::Visitor::EConstant>(op));
  } else if (std::holds_alternative<Expr::EKind>(op)) {
    if (std::get<Expr::EKind>(op) == Expr::EKind::QuantifiedSet) {
      return "?";
    } else {
      return std::string("unknown operator");
    }
  }
  return std::string("unknown operator");
}

/** @brief A visitor to build the string representation of a B type */
class TypeSymbolVisitor : public BType::Visitor {
 public:
  TypeSymbolVisitor() : m_result() {}
  const std::string &getResult() const { return m_result; }

  virtual void visitINTEGER() override;
  virtual void visitBOOLEAN() override;
  virtual void visitFLOAT() override;
  virtual void visitREAL() override;
  virtual void visitSTRING() override;
  virtual void visitAbstractSet(const BType::AbstractSet &ty) override;
  virtual void visitEnumeratedSet(const BType::EnumeratedSet &ty) override;
  virtual void visitProductType(const BType &lhs, const BType &rhs) override;
  virtual void visitPowerType(const BType &ty) override;
  virtual void visitRecordType(
      const std::vector<std::pair<std::string, BType>> &fields) override;

 private:
  std::string m_result;
};

void TypeSymbolVisitor::visitINTEGER() { m_result = "Z"; }

void TypeSymbolVisitor::visitBOOLEAN() { m_result = "BOOL"; }

void TypeSymbolVisitor::visitFLOAT() { m_result = "FLOAT"; }

void TypeSymbolVisitor::visitREAL() { m_result = "REAL"; }

void TypeSymbolVisitor::visitSTRING() { m_result = "STRING"; }

void TypeSymbolVisitor::visitAbstractSet(const BType::AbstractSet &type) {
  m_result = type.name;
}

void TypeSymbolVisitor::visitEnumeratedSet(const BType::EnumeratedSet &type) {
  m_result = type.getName();
}

void TypeSymbolVisitor::visitProductType(const BType &lhs, const BType &rhs) {
  std::string result;
  result.push_back('(');
  lhs.accept(*this);
  result.append(std::move(m_result));
  result.append(" * ");
  rhs.accept(*this);
  result.append(std::move(m_result));
  result.push_back(')');
  m_result = std::move(result);
}

void TypeSymbolVisitor::visitPowerType(const BType &type) {
  std::string result;
  result.append("POW ");
  type.accept(*this);
  result.append(std::move(m_result));
  m_result = std::move(result);
}

using structId_t = std::string;

static std::map<std::set<std::string>, structId_t> structIdMap;

void TypeSymbolVisitor::visitRecordType(
    const std::vector<std::pair<std::string, BType>> &fields) {
  m_result.clear();
  std::set<std::string> names;
  for (const auto &field : fields) {
    names.insert(field.first);
  }
  auto it = structIdMap.find(names);
  if (it != structIdMap.end()) {
    m_result = it->second;
  } else {
    structId_t id = "struct " + std::to_string(structIdMap.size());
    structIdMap[names] = id;
    m_result = structIdMap[names];
  }
}

auto fmt::formatter<BType>::format(BType type, format_context &ctx) const
    -> format_context::iterator {
  TypeSymbolVisitor visitor;
  type.accept(visitor);
  const std::string &name = visitor.getResult();
  return formatter<string_view>::format(name, ctx);
}
