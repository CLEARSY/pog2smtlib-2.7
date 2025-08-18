/*
  This file is part of pog2smtlib27.
  Copyright © CLEARSY 2025
  pog2smtlib27 is free software: you can redistribute it and/or modify
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

void SmtTranslatorVisitor::visitForall(
    [[maybe_unused]] const std::vector<TypedVar> &vars,
    [[maybe_unused]] const Pred &p) {
  // TODO
}
void SmtTranslatorVisitor::visitExists(
    [[maybe_unused]] const std::vector<TypedVar> &vars,
    [[maybe_unused]] const Pred &p) {
  // TODO
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

void SmtTranslatorVisitor::visitConstant(
    const BType &type, [[maybe_unused]] const std::vector<std::string> &bxmlTag,
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

void SmtTranslatorVisitor::visitIdent(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
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

void SmtTranslatorVisitor::visitIntegerLiteral(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    const std::string &i) {
  m_translation.append(i);
}

void SmtTranslatorVisitor::visitStringLiteral(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const std::string &b) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitRealLiteral(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const Expr::Decimal &d) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitUnaryExpression(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] Expr::UnaryOp op, [[maybe_unused]] const Expr &e) {
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
    case Expr::UnaryOp::IMinimum: {
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
      m_translation.append(
          smtSymbol(op,
                    elementType(e.getType())));
      m_translation.push_back(' ');
      e.accept(*this);
      m_translation.push_back(')');
      break;
    }
    case Expr::UnaryOp::Inverse: {
      m_translation.push_back('(');
      m_translation.append(
          smtSymbol(op,
                    elementType(e.getType()).toProductType().lhs,
                    elementType(e.getType()).toProductType().rhs));
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

    default:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
  }
}

void SmtTranslatorVisitor::visitBinaryExpression(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] Expr::BinaryOp op, [[maybe_unused]] const Expr &lhs,
    [[maybe_unused]] const Expr &rhs) {
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
      m_translation.append(
          smtSymbol(op,
                    elementType(lhs.getType()),
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
          smtSymbol(op,
                    elementType(lhs.getType()).toProductType().lhs,
                    elementType(lhs.getType()).toProductType().rhs,
                    elementType(rhs.getType()).toProductType().rhs));
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

    /* todo */
    case Expr::BinaryOp::Head_Insertion:
    case Expr::BinaryOp::Head_Restriction:
    case Expr::BinaryOp::Surcharge:
    case Expr::BinaryOp::Tail_Insertion:
    case Expr::BinaryOp::Domain_Subtraction:
    case Expr::BinaryOp::Domain_Restriction:
    case Expr::BinaryOp::Partial_Bijections:
    case Expr::BinaryOp::Parallel_Product:
    case Expr::BinaryOp::Tail_Restriction:
    case Expr::BinaryOp::Concatenation:
    case Expr::BinaryOp::Modulo:
    case Expr::BinaryOp::Range_Restriction:
    case Expr::BinaryOp::Range_Subtraction:
    case Expr::BinaryOp::IExponentiation:
    case Expr::BinaryOp::RExponentiation:
    case Expr::BinaryOp::FAddition:
    case Expr::BinaryOp::FSubtraction:
    case Expr::BinaryOp::FMultiplication:
    case Expr::BinaryOp::FDivision:
    case Expr::BinaryOp::Iteration:
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
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] Expr::TernaryOp op, [[maybe_unused]] const Expr &fst,
    [[maybe_unused]] const Expr &snd, [[maybe_unused]] const Expr &thd) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitNaryExpression(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] Expr::NaryOp op,
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

      m_translation.append("(or ");
      for (const Expr &v : vec) {
        m_translation.append("(= x ");
        v.accept(*this);
        m_translation.push_back(')');
      }
      m_translation.push_back(')');

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

      int i = 0;

      m_translation.append("(or ");
      for (const Expr &v : vec) {
        m_translation.append("(= x (maplet ");
        m_translation.append(std::to_string(i));
        m_translation.push_back(' ');
        v.accept(*this);
        m_translation.push_back(')');
        m_translation.push_back(')');
        i++;
      }
      m_translation.push_back(')');

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
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const Pred &p) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitRecord(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const std::vector<std::pair<std::string, Expr>> &fds) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitStruct(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const std::vector<std::pair<std::string, Expr>> &fds) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitQuantifiedExpr(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] Expr::QuantifiedOp op,
    [[maybe_unused]] const std::vector<TypedVar> vars,
    [[maybe_unused]] const Pred &cond, [[maybe_unused]] const Expr &body) {
  switch (op) {
    case Expr::QuantifiedOp::Lambda:
    case Expr::QuantifiedOp::ISum:
    case Expr::QuantifiedOp::IProduct:
    case Expr::QuantifiedOp::Union:
    case Expr::QuantifiedOp::Intersection:
    case Expr::QuantifiedOp::RSum:
    case Expr::QuantifiedOp::RProduct:
      throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                           FILE_NAME, LINE_NUMBER));
      return;
  }
}
void SmtTranslatorVisitor::visitQuantifiedSet(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const std::vector<TypedVar> vars,
    [[maybe_unused]] const Pred &cond) {
  m_translation.push_back('(');
  m_translation.append(
      smtSymbol(Expr::NaryOp::Set, type.toPowerType().content));
  m_translation.append(" (lambda (");

  // Étape 1 : Récupérer les différentes types produits
  std::vector<BType> types;
  BType current = type.toPowerType().content;

  for (size_t i = 0; i < vars.size(); ++i) {
    if (i < vars.size() - 1) {
      types.push_back(current.toProductType().rhs);
      current = current.toProductType().lhs;
    } else {
      types.push_back(current);  // le dernier (tout à gauche)
    }
  }

  // Étape 2 : Générer les variables avec leur type, dans le bon ordre
  for (size_t i = 0; i < vars.size(); ++i) {
    m_translation.push_back('(');
    m_translation.append(vars[i].name.show());
    m_translation.push_back(' ');
    m_translation.append(symbol(types[vars.size() - 1 - i]));
    m_translation.push_back(')');
  }

  m_translation.push_back(')');
  m_translation.push_back(' ');

  cond.accept(*this);

  m_translation.push_back(')');
  m_translation.push_back(')');
  m_translation.push_back(')');
}
void SmtTranslatorVisitor::visitRecordUpdate(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const Expr &rec, [[maybe_unused]] const std::string &label,
    [[maybe_unused]] const Expr &value) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
void SmtTranslatorVisitor::visitRecordAccess(
    [[maybe_unused]] const BType &type,
    [[maybe_unused]] const std::vector<std::string> &bxmlTag,
    [[maybe_unused]] const Expr &rec,
    [[maybe_unused]] const std::string &label) {
  throw std::runtime_error(fmt::format("{}:{} Construct not covered (todo)",
                                       FILE_NAME, LINE_NUMBER));
}
