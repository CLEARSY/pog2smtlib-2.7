/*
  This file is part of pog2smtlib-2.7.
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

#include "translate-predicate.h"

#include <fmt/core.h>

#include <unordered_map>
#include <vector>

#include "btype-symbols.h"
#include "cc-compatibility.h"
#include "expr.h"
#include "pred.h"
#include "pure-typing.h"
#include "symbols.h"
#include "translate-token.h"
#include "type-utils.h"

using std::string;
using std::string_view;
using std::vector;

class SmtTranslatorVisitor : public Pred::Visitor, public Expr::Visitor {
 public:
  SmtTranslatorVisitor() = default;
  ~SmtTranslatorVisitor() = default;
  void reset();
  std::string get();

  virtual void visitImplication(const Pred &lhs, const Pred &rhs) override;
  virtual void visitEquivalence(const Pred &lhs, const Pred &rhs) override;
  virtual void visitNegation(const Pred &p) override;
  virtual void visitConjunction(const std::vector<Pred> &vec) override;
  virtual void visitDisjunction(const std::vector<Pred> &vec) override;
  virtual void visitForall(const std::vector<TypedVar> &vars,
                           const Pred &p) override;
  virtual void visitExists(const std::vector<TypedVar> &vars,
                           const Pred &p) override;
  virtual void visitTrue() override;
  virtual void visitFalse() override;
  virtual void visitExprComparison(Pred::ComparisonOp op, const Expr &lhs,
                                   const Expr &rhs) override;
  virtual void visitConstant(const BType &type,
                             const std::vector<std::string> &bxmlTag,
                             EConstant c) override;
  virtual void visitIdent(const BType &type,
                          const std::vector<std::string> &bxmlTag,
                          const VarName &b) override;
  virtual void visitIntegerLiteral(const BType &type,
                                   const std::vector<std::string> &bxmlTag,
                                   const std::string &i) override;
  virtual void visitStringLiteral(const BType &type,
                                  const std::vector<std::string> &bxmlTag,
                                  const std::string &b) override;
  virtual void visitRealLiteral(const BType &type,
                                const std::vector<std::string> &bxmlTag,
                                const Expr::Decimal &d) override;
  virtual void visitUnaryExpression(const BType &type,
                                    const std::vector<std::string> &bxmlTag,
                                    Expr::UnaryOp op, const Expr &e) override;
  virtual void visitBinaryExpression(const BType &type,
                                     const std::vector<std::string> &bxmlTag,
                                     Expr::BinaryOp op, const Expr &lhs,
                                     const Expr &rhs) override;
  virtual void visitTernaryExpression(const BType &type,
                                      const std::vector<std::string> &bxmlTag,
                                      Expr::TernaryOp op, const Expr &fst,
                                      const Expr &snd,
                                      const Expr &thd) override;
  virtual void visitNaryExpression(const BType &type,
                                   const std::vector<std::string> &bxmlTag,
                                   Expr::NaryOp op,
                                   const std::vector<Expr> &vec) override;
  virtual void visitBooleanExpression(const BType &type,
                                      const std::vector<std::string> &bxmlTag,
                                      const Pred &p) override;
  virtual void visitRecord(
      const BType &type, const std::vector<std::string> &bxmlTag,
      const std::vector<std::pair<std::string, Expr>> &fds) override;
  virtual void visitStruct(
      const BType &type, const std::vector<std::string> &bxmlTag,
      const std::vector<std::pair<std::string, Expr>> &fds) override;
  virtual void visitQuantifiedExpr(const BType &type,
                                   const std::vector<std::string> &bxmlTag,
                                   Expr::QuantifiedOp op,
                                   const std::vector<TypedVar> vars,
                                   const Pred &cond, const Expr &body) override;
  virtual void visitQuantifiedSet(const BType &type,
                                  const std::vector<std::string> &bxmlTag,
                                  const std::vector<TypedVar> vars,
                                  const Pred &cond) override;
  virtual void visitRecordUpdate(const BType &type,
                                 const std::vector<std::string> &bxmlTag,
                                 const Expr &rec, const std::string &label,
                                 const Expr &value) override;
  virtual void visitRecordAccess(const BType &type,
                                 const std::vector<std::string> &bxmlTag,
                                 const Expr &rec,
                                 const std::string &label) override;
  class Exception : public std::exception {
   public:
    Exception(const std::string &message) : m_msg(message) {}
    virtual const char *what() const noexcept override { return m_msg.c_str(); }

   private:
    std::string m_msg;
  };  // end class Exception

 private:
  size_t m_indent;
  string m_translation;
  static constexpr const char *MSG_NOT_SUPPORTED =
      "POG to SMT syntax transformation: application of {} operator is not "
      "supported";

  inline void visitBinaryPred(const string_view op, const Pred &lhs,
                              const Pred &rhs) {
    m_translation.append(fmt::format("{:{}}({}\n", "", m_indent * 2, op));
    m_indent += 1;
    lhs.accept(*this);
    m_translation.append("\n");
    rhs.accept(*this);
    m_translation.append(")");
    m_indent -= 1;
  }
  inline void visitNaryPred(const string_view op, const vector<Pred> &vec) {
    m_translation.append(fmt::format("{:{}}({}\n", "", m_indent * 2, op));
    m_indent += 1;
    std::size_t child = 1;
    for (const auto &pred : vec) {
      pred.accept(*this);
      if (child < vec.size())
        m_translation.append("\n");
      else
        m_translation.append(")");
    }
    if (child < vec.size()) m_translation.append(")");
    m_indent -= 1;
  }
};

static SmtTranslatorVisitor translator;

string translate(const Pred &pred) {
  translator.reset();
  pred.accept(translator);
  return translator.get();
}

void SmtTranslatorVisitor::reset() {
  m_indent = 0;
  m_translation.clear();
}

string SmtTranslatorVisitor::get() { return std::move(m_translation); }

void SmtTranslatorVisitor::visitImplication(const Pred &lhs, const Pred &rhs) {
  visitBinaryPred(smtSymbol(Pred::PKind::Implication), lhs, rhs);
}

void SmtTranslatorVisitor::visitEquivalence(const Pred &lhs, const Pred &rhs) {
  visitBinaryPred(smtSymbol(Pred::PKind::Equivalence), lhs, rhs);
}

void SmtTranslatorVisitor::visitNegation(const Pred &p) {
  m_translation.append(fmt::format("{:{}}({} ", "", m_indent * 2,
                                   smtSymbol(Pred::PKind::Negation)));
  p.accept(*this);
  m_translation.append(")");
}

void SmtTranslatorVisitor::visitConjunction(const vector<Pred> &vec) {
  visitNaryPred(smtSymbol(Pred::PKind::Conjunction), vec);
}
void SmtTranslatorVisitor::visitDisjunction(const vector<Pred> &vec) {
  visitNaryPred(smtSymbol(Pred::PKind::Disjunction), vec);
}

void SmtTranslatorVisitor::visitForall(const std::vector<TypedVar> &vars,
                                       const Pred &p) {
  m_translation.append("(forall (");
  for (auto &v : vars) {
    m_translation.append("(");
    m_translation.append(v.name.show());
    m_translation.append(" ");
    m_translation.append(symbol(v.type));
    m_translation.append(")");
  }
  m_translation.push_back(')');
  m_translation.append(" ");
  p.accept(*this);
  m_translation.push_back(')');
}
void SmtTranslatorVisitor::visitExists(const std::vector<TypedVar> &vars,
                                       const Pred &p) {
  m_translation.append("(exists (");
  for (auto &v : vars) {
    m_translation.append("(");
    m_translation.append(v.name.show());
    m_translation.append(" ");
    m_translation.append(symbol(v.type));
    m_translation.append(")");
  }
  m_translation.push_back(')');
  m_translation.append(" ");
  p.accept(*this);
  m_translation.push_back(')');
}

void SmtTranslatorVisitor::visitTrue() {
  m_translation.append(smtSymbol(Pred::PKind::True));
}
void SmtTranslatorVisitor::visitFalse() {
  m_translation.append(smtSymbol(Pred::PKind::False));
}

void SmtTranslatorVisitor::visitExprComparison(Pred::ComparisonOp op,
                                               const Expr &lhs,
                                               const Expr &rhs) {
  string smtOp;
  switch (op) {
    case Pred::ComparisonOp::Membership:
      smtOp = smtSymbol(op, lhs.getType());
      break;
    case Pred::ComparisonOp::Subset:
    case Pred::ComparisonOp::Strict_Subset:
      smtOp = smtSymbol(op, elementType(lhs.getType()));
      break;
    default:
      smtOp = smtSymbol(op);
      break;
  }
  m_translation.push_back('(');
  m_translation.append(smtOp);
  m_translation.push_back(' ');
  lhs.accept(*this);
  m_translation.push_back(' ');
  rhs.accept(*this);
  m_translation.push_back(')');
}

void SmtTranslatorVisitor::visitConstant(const BType &type,
                                         const std::vector<std::string> &,
                                         EConstant c) {
  switch (c) {
    case EConstant::EmptySet:
      m_translation.append(smtSymbol(c, type.toPowerType().content));
      break;
    default:
      m_translation.append(smtSymbol(c, type));
      break;
  }
}

void SmtTranslatorVisitor::visitIdent(const BType &,
                                      const std::vector<std::string> &,
                                      const VarName &b) {
  m_translation.append(b.prefix());
  switch (b.kind()) {
    case VarName::Kind::NoSuffix:
      break;
    case VarName::Kind::WithSuffix:
      m_translation.append(std::to_string(b.suffix()));
      break;
    default:
      assert(false);
      break;
  }
}

void SmtTranslatorVisitor::visitIntegerLiteral(const BType &,
                                               const std::vector<std::string> &,
                                               const std::string &i) {
  m_translation.append(i);
}

void SmtTranslatorVisitor::visitStringLiteral(const BType &,
                                              const std::vector<std::string> &,
                                              const std::string &b) {
  m_translation.append("\"" + b + "\"");
}
void SmtTranslatorVisitor::visitRealLiteral(const BType &,
                                            const std::vector<std::string> &,
                                            const Expr::Decimal &d) {
  m_translation.append(d.integerPart + "." + d.fractionalPart);
}
void SmtTranslatorVisitor::visitUnaryExpression(
    const BType &type, const std::vector<std::string> &, Expr::UnaryOp op,
    const Expr &e) {
  switch (op) {
    /* 5.3 Arithmetical Expressions */
    case Expr::UnaryOp::Real:
    case Expr::UnaryOp::Floor:
    case Expr::UnaryOp::Ceiling: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.4 Arithmetical Expressions (continued) */
    case Expr::UnaryOp::IMaximum:
    case Expr::UnaryOp::IMinimum:
    case Expr::UnaryOp::RMaximum:
    case Expr::UnaryOp::RMinimum: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    case Expr::UnaryOp::Cardinality: {
      m_translation.push_back('(');
      m_translation.append("Value");
      m_translation.push_back(' ');
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, elementType(e.getType())));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      m_translation.push_back(')');
      break;
    }

    /* 5.7 Set List Expressions */
    case Expr::UnaryOp::Subsets:
    case Expr::UnaryOp::Non_Empty_Subsets:
    case Expr::UnaryOp::Finite_Subsets:
    case Expr::UnaryOp::Non_Empty_Finite_Subsets: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toPowerType().content));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.8 Set List Expressions */
    case Expr::UnaryOp::Union:
    case Expr::UnaryOp::Intersection: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, type.toPowerType().content));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.11 Expressions of Relations */
    case Expr::UnaryOp::Identity: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, elementType(e.getType())));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }
    case Expr::UnaryOp::Inverse: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(e.getType()).toProductType().lhs,
                    elementType(e.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.12 Expressions of Relations */
    case Expr::UnaryOp::Closure:
    case Expr::UnaryOp::Transitive_Closure: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(e.getType()).toProductType().lhs));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.13 Expressions of Relations */
    case Expr::UnaryOp::Domain:
    case Expr::UnaryOp::Range: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(e.getType()).toProductType().lhs,
                    elementType(e.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.16 Expressions of Functions */
    case Expr::UnaryOp::Fnc: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().lhs,
                    ((type.toPowerType().content).toProductType().rhs)
                        .toPowerType()
                        .content));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }
    case Expr::UnaryOp::Rel: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(e.getType()).toProductType().lhs,
                    (elementType(e.getType()).toProductType().rhs)
                        .toPowerType()
                        .content));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.17 Set of Sequences */
    case Expr::UnaryOp::Sequences:
    case Expr::UnaryOp::Non_Empty_Sequences:
    case Expr::UnaryOp::Injective_Sequences:
    case Expr::UnaryOp::Non_Empty_Injective_Sequences:
    case Expr::UnaryOp::Permutations: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, elementType(e.getType())));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.18 Expressions of Sequences */
    case Expr::UnaryOp::Size:
    case Expr::UnaryOp::First:
    case Expr::UnaryOp::Last:
    case Expr::UnaryOp::Front:
    case Expr::UnaryOp::Tail:
    case Expr::UnaryOp::Reverse: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(e.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.19 Expressions of Sequences */
    case Expr::UnaryOp::Concatenation: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().rhs));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }

    default:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
  }
}

void SmtTranslatorVisitor::visitBinaryExpression(
    const BType &type, const std::vector<std::string> &, Expr::BinaryOp op,
    const Expr &lhs, const Expr &rhs) {
  switch (op) {
    /* 5.3 Arithmetical Expressions I */
    case Expr::BinaryOp::IAddition:
    case Expr::BinaryOp::RAddition:
    case Expr::BinaryOp::ISubtraction:
    case Expr::BinaryOp::RSubtraction:
    case Expr::BinaryOp::IMultiplication:
    case Expr::BinaryOp::RMultiplication:
    case Expr::BinaryOp::IDivision:
    case Expr::BinaryOp::RDivision:
    case Expr::BinaryOp::Modulo:
    case Expr::BinaryOp::IExponentiation:
    case Expr::BinaryOp::RExponentiation:

    /* 5.5 Expression of Couples */
    case Expr::BinaryOp::Mapplet: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.7 Set List Expressions */
    case Expr::BinaryOp::Interval: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

      /* 5.8 Set List Expressions (continued) */

    case Expr::BinaryOp::Set_Difference:
    case Expr::BinaryOp::Union:
    case Expr::BinaryOp::Intersection: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, type.toPowerType().content));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    case Expr::BinaryOp::Cartesian_Product: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, elementType(lhs.getType()),
                                     elementType(rhs.getType())));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.10 Set of Relations */
    case Expr::BinaryOp::Relations: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op,
                    ((type.toPowerType().content).toPowerType().content)
                        .toProductType()
                        .lhs,
                    ((type.toPowerType().content).toPowerType().content)
                        .toProductType()
                        .rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.11 Expressions of Relations */
    case Expr::BinaryOp::First_Projection:
    case Expr::BinaryOp::Second_Projection: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, elementType(lhs.getType()),
                                     elementType(rhs.getType())));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }
    case Expr::BinaryOp::Composition:
    case Expr::BinaryOp::Direct_Product: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(lhs.getType()).toProductType().lhs,
                    elementType(lhs.getType()).toProductType().rhs,
                    elementType(rhs.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }
    case Expr::BinaryOp::Parallel_Product: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(
          op,
          (type.toPowerType().content).toProductType().lhs.toProductType().lhs,
          (type.toPowerType().content).toProductType().lhs.toProductType().rhs,
          (type.toPowerType().content).toProductType().rhs.toProductType().lhs,
          (type.toPowerType().content)
              .toProductType()
              .rhs.toProductType()
              .rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }
    /* 5.12 Expressions of Relations */
    case Expr::BinaryOp::Iteration: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().lhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.13 Expressions of Relations */
    case Expr::BinaryOp::Image: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(lhs.getType()).toProductType().lhs,
                    elementType(lhs.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.14 Expressions of Relations */
    case Expr::BinaryOp::Domain_Restriction:
    case Expr::BinaryOp::Domain_Subtraction:
    case Expr::BinaryOp::Range_Restriction:
    case Expr::BinaryOp::Range_Subtraction:
    case Expr::BinaryOp::Surcharge: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().lhs,
                    (type.toPowerType().content).toProductType().rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.15 Sets of Functions */
    case Expr::BinaryOp::Total_Functions:
    case Expr::BinaryOp::Partial_Functions:
    case Expr::BinaryOp::Partial_Injections:
    case Expr::BinaryOp::Total_Injections:
    case Expr::BinaryOp::Partial_Surjections:
    case Expr::BinaryOp::Total_Surjections:
    case Expr::BinaryOp::Total_Bijections: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op,
                    ((type.toPowerType().content).toPowerType().content)
                        .toProductType()
                        .lhs,
                    ((type.toPowerType().content).toPowerType().content)
                        .toProductType()
                        .rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.16 Expressions of Functions */
    case Expr::BinaryOp::Application: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, elementType(lhs.getType()).toProductType().lhs,
                    elementType(lhs.getType()).toProductType().rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* 5.19 Expressions of Sequences */
    case Expr::BinaryOp::Concatenation:
    case Expr::BinaryOp::Head_Insertion:
    case Expr::BinaryOp::Tail_Insertion:
    case Expr::BinaryOp::Head_Restriction:
    case Expr::BinaryOp::Tail_Restriction: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().rhs));
      m_translation.push_back(' ');
      lhs.accept(*this);
      m_translation.push_back(' ');
      rhs.accept(*this);
      m_translation.push_back(')');
      break;
    }

    /* todo */
    case Expr::BinaryOp::Partial_Bijections:
    case Expr::BinaryOp::FAddition:
    case Expr::BinaryOp::FSubtraction:
    case Expr::BinaryOp::FMultiplication:
    case Expr::BinaryOp::FDivision:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
      return;
    case Expr::BinaryOp::Const:
    case Expr::BinaryOp::Rank:
    case Expr::BinaryOp::Father:
    case Expr::BinaryOp::Subtree:
    case Expr::BinaryOp::Arity:
      throw std::runtime_error(
          fmt::format("{}:{} Construct not supported (deprecated)", FILE_NAME,
                      LINE_NUMBER));
      return;
  }
}
void SmtTranslatorVisitor::visitTernaryExpression(
    const BType &, const std::vector<std::string> &, Expr::TernaryOp,
    const Expr &, const Expr &, const Expr &) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitNaryExpression(
    const BType &type, const std::vector<std::string> &, Expr::NaryOp op,
    [[maybe_unused]] const std::vector<Expr> &vec) {
  switch (op) {
    /* 5.7 Set List Expressions */
    case Expr::NaryOp::Set: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, type.toPowerType().content));
      m_translation.append(" (lambda (");

      m_translation.push_back('(');
      m_translation.push_back('x');
      m_translation.push_back(' ');
      m_translation.append(symbol(type.toPowerType().content));
      m_translation.push_back(')');
      m_translation.push_back(')');
      m_translation.push_back(' ');

      if (vec.size() > 1) {
        m_translation.append("(or ");
      }
      for (const Expr &v : vec) {
        m_translation.append("(= x ");
        v.accept(*this);
        m_translation.push_back(')');
      }
      if (vec.size() > 1) {
        m_translation.push_back(')');
      }

      m_translation.push_back(')');
      m_translation.push_back(')');
      break;
    }
    case Expr::NaryOp::Sequence: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, type.toPowerType().content));
      m_translation.append(" (lambda (");

      m_translation.push_back('(');
      m_translation.push_back('x');
      m_translation.push_back(' ');
      m_translation.append(symbol(type.toPowerType().content));
      m_translation.push_back(')');
      m_translation.push_back(')');
      m_translation.push_back(' ');

      int i = 1;

      if (vec.size() > 1) {
        m_translation.append("(or ");
      }
      for (const Expr &v : vec) {
        m_translation.append("(= x (maplet ");
        m_translation.append(std::to_string(i));
        m_translation.push_back(' ');
        v.accept(*this);
        m_translation.push_back(')');
        m_translation.push_back(')');
        i++;
      }
      if (vec.size() > 1) {
        m_translation.push_back(')');
      }
      m_translation.push_back(')');
      m_translation.push_back(')');
      break;
    }
    default:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
      return;
  }
}
void SmtTranslatorVisitor::visitBooleanExpression(
    const BType &, const std::vector<std::string> &, const Pred &) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitRecord(
    const BType &type, const std::vector<std::string> &,
    const std::vector<std::pair<std::string, Expr>> &fds) {
  m_translation.push_back('(');
  m_translation.append("|record ");
  m_translation.append(symbolInner(type));
  m_translation.append("| ");
  bool first = true;
  for (const auto &fd : fds) {
    if (first) {
      first = false;
    } else {
      m_translation.append(" ");
    }
    fd.second.accept(*this);
  }
  m_translation.push_back(')');
}
void SmtTranslatorVisitor::visitStruct(
    const BType &type, const std::vector<std::string> &,
    const std::vector<std::pair<std::string, Expr>> &fds) {
  m_translation.push_back('(');
  m_translation.append(
      smtSymbol(Expr::EKind::Struct, type.toPowerType().content));
  m_translation.append(" (lambda (");

  m_translation.push_back('(');
  m_translation.push_back('x');
  m_translation.push_back(' ');
  m_translation.append(symbol(type.toPowerType().content));
  m_translation.push_back(')');
  m_translation.push_back(')');
  m_translation.push_back(' ');

  if (fds.size() > 1) {
    m_translation.append("(and ");
  }
  for (const auto &fd : fds) {
    m_translation.append("(");
    m_translation.append(
        smtSymbol(Pred::ComparisonOp::Membership,
                  (fd.second.getType()).toPowerType().content));
    m_translation.append(" (");
    m_translation.append(fd.first);
    m_translation.append(" x) ");
    fd.second.accept(*this);
    m_translation.push_back(')');
  }
  if (fds.size() > 1) {
    m_translation.push_back(')');
  }

  m_translation.push_back(')');
  m_translation.push_back(')');
}
void SmtTranslatorVisitor::visitQuantifiedExpr(
    const BType &type, const std::vector<std::string> &, Expr::QuantifiedOp op,
    const std::vector<TypedVar> vars, const Pred &cond, const Expr &body) {
  switch (op) {
    case Expr::QuantifiedOp::Lambda: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op, (type.toPowerType().content).toProductType().lhs,
                    (type.toPowerType().content).toProductType().rhs));

      m_translation.append(" (lambda ((c ");
      m_translation.append(
          symbol((type.toPowerType().content).toProductType().lhs));
      m_translation.append(")) ");
      Pred condCopy = cond.copy();
      std::map<VarName, VarName> map;
      for (size_t i = 0; i < vars.size(); ++i) {
        std::string access = "c";
        for (size_t j = 0; j < vars.size() - i - 1; ++j) {
          access = "(fst " + access + ")";
        }
        access = (i == 0) ? access : "(snd " + access + ")";
        map.insert({vars[i].name, VarName::makeVarWithoutSuffix(access)});
      }
      condCopy.alpha(map);
      condCopy.accept(*this);
      m_translation.push_back(')');
      m_translation.push_back(' ');

      m_translation.append(" (lambda ((c ");
      m_translation.append(
          symbol((type.toPowerType().content).toProductType().lhs));
      m_translation.append(")) ");
      Expr bodyCopy = body.copy();
      bodyCopy.alpha(map);
      bodyCopy.accept(*this);
      m_translation.push_back(')');

      m_translation.push_back(')');
      break;
    }
    case Expr::QuantifiedOp::Union:
    case Expr::QuantifiedOp::Intersection: {
      BType tp = vars[0].type;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, vars[i].type);
      }
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op, tp, type.toPowerType().content));

      m_translation.append(" (lambda ((c ");
      m_translation.append(symbol(tp));
      m_translation.append(")) ");
      Pred condCopy = cond.copy();
      std::map<VarName, VarName> map;
      for (size_t i = 0; i < vars.size(); ++i) {
        std::string access = "c";
        for (size_t j = 0; j < vars.size() - i - 1; ++j) {
          access = "(fst " + access + ")";
        }
        access = (i == 0) ? access : "(snd " + access + ")";
        map.insert({vars[i].name, VarName::makeVarWithoutSuffix(access)});
      }
      condCopy.alpha(map);
      condCopy.accept(*this);
      m_translation.push_back(')');
      m_translation.push_back(' ');

      m_translation.append(" (lambda ((c ");
      m_translation.append(symbol(tp));
      m_translation.append(")) ");
      Expr bodyCopy = body.copy();
      bodyCopy.alpha(map);
      bodyCopy.accept(*this);
      m_translation.push_back(')');

      m_translation.push_back(')');
      break;
    }
    case Expr::QuantifiedOp::ISum:
    case Expr::QuantifiedOp::IProduct: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');

      m_translation.push_back('(');
      m_translation.append(smtSymbol(Expr::NaryOp::Set, BType::INT));
      m_translation.append(" (lambda ((c ");
      m_translation.append(symbol(BType::INT));
      m_translation.append(")) ");

      BType tp = BType::INT;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, BType::INT);
      }

      Pred condCopy = cond.copy();
      Expr bodyCopy = body.copy();
      std::map<VarName, VarName> map;
      for (size_t i = 0; i < vars.size(); ++i) {
        std::string access = "y";
        for (size_t j = 0; j < vars.size() - i - 1; ++j) {
          access = "(fst " + access + ")";
        }
        if (i != 0) {
          access = "(snd " + access + ")";
        }
        map.insert({vars[i].name, VarName::makeVarWithoutSuffix(access)});
      }
      condCopy.alpha(map);
      bodyCopy.alpha(map);

      m_translation.append("(exists ((y ");
      m_translation.append(symbol(tp));
      m_translation.append(")) ");

      m_translation.append("(and ");
      condCopy.accept(*this);
      m_translation.append(" (= c ");
      bodyCopy.accept(*this);
      m_translation.append(")))");

      m_translation.append(")");
      m_translation.append(")");
      m_translation.append(")");
      break;
    }
    case Expr::QuantifiedOp::RSum:
    case Expr::QuantifiedOp::RProduct: {
      m_translation.push_back('(');
      m_translation.append(smtSymbol(op));
      m_translation.push_back(' ');

      m_translation.push_back('(');
      m_translation.append(smtSymbol(Expr::NaryOp::Set, BType::REAL));
      m_translation.append(" (lambda ((c ");
      m_translation.append(symbol(BType::REAL));
      m_translation.append(")) ");

      BType tp = BType::REAL;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, BType::REAL);
      }

      Pred condCopy = cond.copy();
      Expr bodyCopy = body.copy();
      std::map<VarName, VarName> map;
      for (size_t i = 0; i < vars.size(); ++i) {
        std::string access = "y";
        for (size_t j = 0; j < vars.size() - i - 1; ++j) {
          access = "(fst " + access + ")";
        }
        if (i != 0) {
          access = "(snd " + access + ")";
        }
        map.insert({vars[i].name, VarName::makeVarWithoutSuffix(access)});
      }
      condCopy.alpha(map);
      bodyCopy.alpha(map);

      m_translation.append("(exists ((y ");
      m_translation.append(symbol(tp));
      m_translation.append(")) ");

      m_translation.append("(and ");
      condCopy.accept(*this);
      m_translation.append(" (= c ");
      bodyCopy.accept(*this);
      m_translation.append(")))");

      m_translation.append(")");
      m_translation.append(")");
      m_translation.append(")");
      break;
    }
    default:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
      return;
  }
}
void SmtTranslatorVisitor::visitQuantifiedSet(const BType &type,
                                              const std::vector<std::string> &,
                                              const std::vector<TypedVar> vars,
                                              const Pred &cond) {
  m_translation.push_back('(');
  m_translation.append(
      smtSymbol(Expr::NaryOp::Set, type.toPowerType().content));
  m_translation.append(" (lambda ((x ");
  m_translation.append(symbol(type.toPowerType().content));
  m_translation.append(")) ");
  Pred condCopy = cond.copy();
  std::map<VarName, VarName> map;
  for (size_t i = 0; i < vars.size(); ++i) {
    std::string access = "x";
    for (size_t j = 0; j < vars.size() - i - 1; ++j) {
      access = "(fst " + access + ")";
    }
    access = (i == 0) ? access : "(snd " + access + ")";
    map.insert({vars[i].name, VarName::makeVarWithoutSuffix(access)});
  }
  condCopy.alpha(map);
  condCopy.accept(*this);
  m_translation.push_back(')');
  m_translation.push_back(')');
}
void SmtTranslatorVisitor::visitRecordUpdate(const BType &,
                                             const std::vector<std::string> &,
                                             const Expr &, const std::string &,
                                             const Expr &) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitRecordAccess(const BType &,
                                             const std::vector<std::string> &,
                                             const Expr &rec,
                                             const std::string &label) {
  m_translation.push_back('(');
  m_translation.append(label);
  m_translation.append(" ");
  rec.accept(*this);
  m_translation.push_back(')');
}
