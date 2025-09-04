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
#include "pure-typing.h"

#include "expr.h"
#include "pred.h"

class PureTypeExpression : public Expr::Visitor {
 private:
  bool m_result;

 public:
  PureTypeExpression() : m_result{false} {};

  void reset() { m_result = false; }
  bool get() const { return m_result; }

  virtual void visitConstant(const BType &, const std::vector<std::string> &,
                             EConstant c) {
    m_result = (c == Expr::Visitor::EConstant::INTEGER ||
                c == Expr::Visitor::EConstant::BOOL ||
                c == Expr::Visitor::EConstant::STRING ||
                c == Expr::Visitor::EConstant::REAL ||
                c == Expr::Visitor::EConstant::FLOAT);
  }
  virtual void visitIdent(const BType &type, const std::vector<std::string> &,
                          const VarName &b) {
    if (type.getKind() == BType::Kind::PowerType) {
      const auto &etype = type.toPowerType().content;
      if (etype.getKind() == BType::Kind::AbstractSet) {
        m_result = b.prefix() == etype.toAbstractSetType().getName();
      } else if (etype.getKind() == BType::Kind::EnumeratedSet) {
        m_result = b.prefix() == etype.toEnumeratedSetType().getName();
      } else {
        m_result = false;
      }
    }
  }
  virtual void visitIntegerLiteral(const BType &,
                                   const std::vector<std::string> &,
                                   const std::string &) {
    m_result = false;
  }
  virtual void visitStringLiteral(const BType &,
                                  const std::vector<std::string> &,
                                  const std::string &) {
    m_result = false;
  }
  virtual void visitRealLiteral(const BType &, const std::vector<std::string> &,
                                const Expr::Decimal &) {
    m_result = false;
  }
  virtual void visitUnaryExpression(const BType &,
                                    const std::vector<std::string> &,
                                    Expr::UnaryOp op, const Expr &e) {
    if (op == Expr::UnaryOp::Subsets) {
      e.accept(*this);
    } else {
      m_result = false;
    }
  }
  virtual void visitBinaryExpression(const BType &,
                                     const std::vector<std::string> &,
                                     Expr::BinaryOp op, const Expr &lhs,
                                     const Expr &rhs) {
    if (op == Expr::BinaryOp::Cartesian_Product) {
      lhs.accept(*this);
      if (m_result) {
        rhs.accept(*this);
      }
    } else {
      m_result = false;
    }
  }
  virtual void visitTernaryExpression(const BType &,
                                      const std::vector<std::string> &,
                                      Expr::TernaryOp, const Expr &,
                                      const Expr &, const Expr &) {
    m_result = false;
  }
  virtual void visitNaryExpression(const BType &,
                                   const std::vector<std::string> &,
                                   Expr::NaryOp, const std::vector<Expr> &) {
    m_result = false;
  }
  virtual void visitBooleanExpression(const BType &,
                                      const std::vector<std::string> &,
                                      const Pred &) {
    m_result = false;
  }
  virtual void visitRecord(const BType &, const std::vector<std::string> &,
                           const std::vector<std::pair<std::string, Expr>> &) {
    m_result = false;
  }
  virtual void visitStruct(const BType &, const std::vector<std::string> &,
                           const std::vector<std::pair<std::string, Expr>> &) {
    m_result = false;
  }
  virtual void visitQuantifiedExpr(const BType &,
                                   const std::vector<std::string> &,
                                   Expr::QuantifiedOp,
                                   const std::vector<TypedVar>, const Pred &,
                                   const Expr &) {
    m_result = false;
  }
  virtual void visitQuantifiedSet(const BType &,
                                  const std::vector<std::string> &,
                                  const std::vector<TypedVar>, const Pred &) {
    m_result = false;
  }
  virtual void visitRecordUpdate(const BType &,
                                 const std::vector<std::string> &, const Expr &,
                                 const std::string &, const Expr &) {
    m_result = false;
  }
  virtual void visitRecordAccess(const BType &,
                                 const std::vector<std::string> &, const Expr &,
                                 const std::string &) {
    m_result = false;
  }
};

class PureTypingVisitor : public Pred::Visitor {
 private:
  bool m_result;
  PureTypeExpression m_exprVisitor;

 public:
  PureTypingVisitor() : m_result(false), m_exprVisitor() {}
  bool get() const { return m_result; }

  void visitImplication([[maybe_unused]] const Pred &, const Pred &) {
    m_result = false;
  };
  void visitEquivalence(const Pred &, const Pred &) { m_result = false; };
  void visitExprComparison(Pred::ComparisonOp op, const Expr &lhs,
                           const Expr &rhs) {
    if (op == Pred::ComparisonOp::Membership ||
        op == Pred::ComparisonOp::Subset) {
      if (lhs.getTag() == Expr::EKind::Id) {
        m_exprVisitor.reset();
        rhs.accept(m_exprVisitor);
        m_result = m_exprVisitor.get();
      } else {
        m_result = false;
      }
    } else {
      m_result = false;
    }
  };

  void visitNegation(const Pred &) { m_result = false; };
  void visitConjunction(const std::vector<Pred> &vec) {
    for (auto &p : vec) {
      p.accept(*this);
      if (m_result == false) break;
    }
  };

  void visitDisjunction(const std::vector<Pred> &) { m_result = false; };
  void visitForall(const std::vector<TypedVar> &, const Pred &) {
    m_result = false;
  };
  void visitExists(const std::vector<TypedVar> &, const Pred &) {};
  void visitTrue() { m_result = false; };
  void visitFalse() { m_result = false; };
};

bool pureTypingPredicate(const Pred &p) {
  PureTypingVisitor visitor;
  p.accept(visitor);
  return visitor.get();
}
