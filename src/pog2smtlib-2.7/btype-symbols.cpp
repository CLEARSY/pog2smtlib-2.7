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
#include "btype-symbols.h"

#include <fmt/core.h>

#include <exception>

#include "btype.h"

class BTypeSymbolVisitor : public BType::Visitor {
 public:
  virtual void visitINTEGER() override;
  virtual void visitBOOLEAN() override;
  virtual void visitFLOAT() override;
  virtual void visitREAL() override;
  virtual void visitSTRING() override;
  virtual void visitProductType(const BType &lhs, const BType &rhs) override;
  virtual void visitPowerType(const BType &ty) override;
  virtual void visitRecordType(
      const std::vector<std::pair<std::string, BType>> &fields) override;
  virtual void visitAbstractSet(const BType::AbstractSet &) override;
  virtual void visitEnumeratedSet(const BType::EnumeratedSet &) override;

  std::string m_symbol;

 private:
  static const std::string INTEGER;
  static const std::string BOOLEAN;
  static const std::string FLOAT;
  static const std::string REAL;
  static const std::string STRING;
  static const std::string POW;
  static const std::string PRODUCT;
  static const std::string STRUCT;
};

const std::string BTypeSymbolVisitor::INTEGER{"Z"};
const std::string BTypeSymbolVisitor::BOOLEAN{"BOOL"};
const std::string BTypeSymbolVisitor::FLOAT{"FLOAT"};
const std::string BTypeSymbolVisitor::REAL{"REAL"};
const std::string BTypeSymbolVisitor::STRING{"STRING"};
const std::string BTypeSymbolVisitor::POW{"POW"};
const std::string BTypeSymbolVisitor::PRODUCT{"x"};
const std::string BTypeSymbolVisitor::STRUCT{"struct"};

static BTypeSymbolVisitor visitor;

void BTypeSymbolVisitor::visitINTEGER() { m_symbol += INTEGER; }
void BTypeSymbolVisitor::visitBOOLEAN() { m_symbol += BOOLEAN; }
void BTypeSymbolVisitor::visitREAL() { m_symbol += REAL; }
void BTypeSymbolVisitor::visitSTRING() { m_symbol += STRING; }
void BTypeSymbolVisitor::visitFLOAT() { m_symbol += FLOAT; }
void BTypeSymbolVisitor::visitProductType(const BType &lhs, const BType &rhs) {
  m_symbol += "(";
  lhs.accept(*this);
  m_symbol += " " + PRODUCT + " ";
  rhs.accept(*this);
  m_symbol += ")";
}
void BTypeSymbolVisitor::visitPowerType(const BType &ty) {
  m_symbol += POW + " ";
  ty.accept(*this);
}
void BTypeSymbolVisitor::visitRecordType(
    const std::vector<std::pair<std::string, BType>> &fds) {
  m_symbol += STRUCT + "(";
  bool first = true;
  for (auto &fd : fds) {
    if (!first) {
      m_symbol.append(", ");
    } else {
      first = false;
    }
    m_symbol.append(fd.first);
    m_symbol.append(" : ");
    fd.second.accept(*this);
  }
  m_symbol.append(")");
}
void BTypeSymbolVisitor::visitAbstractSet(const BType::AbstractSet &t) {
  m_symbol += t.getName();
}
void BTypeSymbolVisitor::visitEnumeratedSet(const BType::EnumeratedSet &t) {
  m_symbol += t.getName();
}

std::string symbol(const BType &btype) {
  std::string result;
  result = fmt::format("|{}|", symbolInner(btype));
  return result;
}

std::string symbolInner(const BType &btype) {
  std::string result;
  BTypeSymbolVisitor visitor;
  visitor.m_symbol.clear();
  btype.accept(visitor);
  result = std::move(visitor.m_symbol);
  return result;
}