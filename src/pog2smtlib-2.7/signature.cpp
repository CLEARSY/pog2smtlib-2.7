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
#include "signature.h"

#include <fmt/format.h>

#include <iostream>
#include <source_location>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>

using std::string;
using std::unordered_set;
using std::vector;

#include "predDesc.h"
#include "special-cases.h"
#include "type-utils.h"

static std::string toString(const Signature &sig);
class GetSignatureVisitor : public Pred::Visitor, public Expr::Visitor {
 public:
  GetSignatureVisitor() {}
  ~GetSignatureVisitor() = default;
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
  Signature getSignature() const { return m_signature; }

  class Exception : public std::exception {
   public:
    Exception(const std::string &message) : m_msg(message) {}
    virtual const char *what() const noexcept override { return m_msg.c_str(); }

   private:
    std::string m_msg;
  };  // end class Exception

 private:
  void visitPredicatePureTypingGuard(const Pred &pred);
  void visitBinaryPred(const Pred &lhs, const Pred &rhs);
  void visitUnaryPred(const Pred &p);
  void visitNaryPred(const std::vector<Pred> &vec);
  void visitNullaryPred();

  Signature m_signature;  // the signature resulting from the last call to a
  // visit function
  using bindings_t = vector<unordered_set<string>>;
  bindings_t m_bindings;
  void bindings_push(const vector<TypedVar> &vars);
  void bindings_pop();
  bool bindings_contains(const TypedVar &var);
  bool bindings_contains(const string &symbol);
  [[maybe_unused]] static string toString(const bindings_t &bindings);

  static constexpr const char *MSG_BAD_TYPE =
      "Signature computation: application of {} operator is not typed as "
      "expected";
  static constexpr const char *MSG_NOT_SUPPORTED =
      "Signature computation: application of {} operator is not supported";

  const BType &elementOfPowerType(const BOperator &op, const BType &power);
  const BType &lhsOfProductType(const BOperator &op, const BType &product);
  const BType &rhsOfProductType(const BOperator &op, const BType &product);
};

/** @brief Overloads formatter to use the fmt library for BType values */
template <typename T>
struct fmt::formatter<std::shared_ptr<T>> : formatter<string_view> {
  auto format(std::shared_ptr<T> ptr, format_context &ctx) const
      -> format_context::iterator {
    return fmt::formatter<T>().formatter<T>::format(*ptr, ctx);
  }
};

namespace std {
template <> struct hash<BType> {
  std::size_t operator()(const BType &b) const noexcept {
    return b.hash_combine(0);
  }
};
}  // namespace std
size_t MonomorphizedOperator::opHash() const {
  if (!m_hash_valid) {
    size_t m_hash = 0;
    m_hash ^= std::hash<BOperator>{}(m_operator) + 0x9e3779b9;

    for (const auto &type_ptr : m_types) {
      if (type_ptr) {  // Check for null pointers.
        m_hash ^= std::hash<BType>{}(*type_ptr) + 0x9e3779b9 + (m_hash << 6) +
                  (m_hash >> 2);
      }
    }
    m_hash_valid = true;
  }
  return m_hash;
}

std::string MonomorphizedOperator::to_string() const {
  if (m_string.empty()) {
    if (m_types.empty()) {
      m_string = fmt::format("{}", m_operator);
    } else {
      std::vector<std::string> args;
      for (const auto &type : m_types) {
        args.push_back(type->to_string());
      }
      m_string = fmt::format("{}<{}>", m_operator, fmt::join(args, " "));
    }
  }
  return m_string;
}

std::string Data::to_string() const { return m_name->show(); }

const BType &Data::type() const { return *m_type; }

Signature &operator+=(Signature &lhs, const Signature &rhs) {
  lhs.m_operators.insert(rhs.m_operators.begin(), rhs.m_operators.end());
  lhs.m_data.insert(rhs.m_data.begin(), rhs.m_data.end());
  lhs.m_types.insert(rhs.m_types.begin(), rhs.m_types.end());
  return lhs;
}

Signature &operator-=(Signature &lhs, const Signature &rhs) {
  for (const auto &elem : rhs.m_operators) {
    lhs.m_operators.erase(elem);
  }
  for (const auto &elem : rhs.m_data) {
    lhs.m_data.erase(elem);
  }
  for (const auto &elem : rhs.m_types) {
    lhs.m_types.erase(elem);
  }
  return lhs;
}

static void SignatureReset(Signature &target) {
  target.m_operators.clear();
  target.m_data.clear();
  target.m_types.clear();
}

/**
 * @brief Moves the contents of one Signature object into another.
 *
 * This function efficiently transfers the data from the `source` Signature
 * object to the `target` Signature object. After the move, the `source`
 * object is left in a valid but unspecified state, typically empty. This is
 * similar to a move constructor or move assignment operator.
 *
 * @param target The Signature object to which the data will be moved.
 * @param source The Signature object from which the data will be moved.  The
 * source object will be modified and should be considered to be in a valid
 * but unspecified state after the move.
 */
static void SignatureMoveInto(Signature &target, Signature &source) {
  target.m_operators.insert(std::make_move_iterator(source.m_operators.begin()),
                            std::make_move_iterator(source.m_operators.end()));
  target.m_data.insert(std::make_move_iterator(source.m_data.begin()),
                       std::make_move_iterator(source.m_data.end()));
  target.m_types.insert(std::make_move_iterator(source.m_types.begin()),
                        std::make_move_iterator(source.m_types.end()));
  SignatureReset(source);
}

void GetSignatureVisitor::visitPredicatePureTypingGuard(const Pred &pred) {
  pred.accept(*this);
  if (pred.isPureTypingPredicate()) {
    m_signature.m_operators.clear();
  }
}

void GetSignatureVisitor::visitBinaryPred(const Pred &lhs, const Pred &rhs) {
  SignatureReset(m_signature);
  Signature sig;
  visitPredicatePureTypingGuard(lhs);
  SignatureMoveInto(sig, m_signature);
  visitPredicatePureTypingGuard(rhs);
  SignatureMoveInto(sig, m_signature);
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitUnaryPred(const Pred &p) {
  SignatureReset(m_signature);
  visitPredicatePureTypingGuard(p);
}

void GetSignatureVisitor::visitNaryPred(const std::vector<Pred> &vec) {
  SignatureReset(m_signature);
  Signature sig;
  for (const Pred &p : vec) {
    visitPredicatePureTypingGuard(p);
    SignatureMoveInto(sig, m_signature);
  }
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitNullaryPred() { SignatureReset(m_signature); }

void GetSignatureVisitor::visitImplication(const Pred &lhs, const Pred &rhs) {
  visitBinaryPred(lhs, rhs);
}

void GetSignatureVisitor::visitEquivalence(const Pred &lhs, const Pred &rhs) {
  visitBinaryPred(lhs, rhs);
}

void GetSignatureVisitor::visitNegation(const Pred &p) { visitUnaryPred(p); }

void GetSignatureVisitor::visitConjunction(const std::vector<Pred> &vec) {
  visitNaryPred(vec);
}

void GetSignatureVisitor::visitDisjunction(const std::vector<Pred> &vec) {
  visitNaryPred(vec);
}

void GetSignatureVisitor::visitForall(const std::vector<TypedVar> &vars,
                                      const Pred &p) {
  bindings_push(vars);
  p.accept(*this);
  bindings_pop();
}

void GetSignatureVisitor::visitExists(const std::vector<TypedVar> &vars,
                                      const Pred &p) {
  bindings_push(vars);
  p.accept(*this);
  bindings_pop();
}

void GetSignatureVisitor::visitTrue() { visitNullaryPred(); }

void GetSignatureVisitor::visitFalse() { visitNullaryPred(); }

void GetSignatureVisitor::visitExprComparison(Pred::ComparisonOp op,
                                              const Expr &lhs,
                                              const Expr &rhs) {
  Signature sig;
  SignatureReset(m_signature);
  lhs.accept(*this);
  SignatureMoveInto(sig, m_signature);
  rhs.accept(*this);
  SignatureMoveInto(sig, m_signature);
  /*
  The arguments of a comparison operator are either of the same type or
  the comparison operator is the membership operator and the type of the
  right-hand side is a set of the type of the left-hand side. The
  corresponding monomorphized operator only retains the type of the left-hand
  side.
  */
  switch (op) {
    case Pred::ComparisonOp::Membership:
      sig.m_operators.emplace(
          MonomorphizedOperator{op, std::make_shared<BType>(lhs.getType())});
      break;
    case Pred::ComparisonOp::Subset:
    case Pred::ComparisonOp::Strict_Subset:
      sig.m_operators.emplace(MonomorphizedOperator{
          op, std::make_shared<BType>(elementType(lhs.getType()))});
      break;
    case Pred::ComparisonOp::Equality:
      if (lhs.getType().getKind() == BType::Kind::PowerType) {
        sig.m_operators.emplace(
            MonomorphizedOperator{op, std::make_shared<BType>(lhs.getType())});
      }
      break;
      /*
        enum class ComparisonOp {
          Ige, Igt, Ilt, Ile,
          Fge, Fgt, Flt, Fle,
          Rle, Rlt, Rge, Rgt
        };
      */
    default:
      break;
  }
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitConstant(const BType &type,
                                        const std::vector<std::string> &,
                                        Expr::Visitor::EConstant c) {
  SignatureReset(m_signature);
  switch (c) {
    case Expr::Visitor::EConstant::BOOL:
      m_signature.m_operators.emplace(MonomorphizedOperator{c});
      m_signature.m_types.insert(std::make_shared<BType>(BType::BOOL));
      break;
    case Expr::Visitor::EConstant::MaxInt:
    case Expr::Visitor::EConstant::MinInt:
    case Expr::Visitor::EConstant::INTEGER:
    case Expr::Visitor::EConstant::NATURAL:
    case Expr::Visitor::EConstant::NATURAL1:
    case Expr::Visitor::EConstant::INT:
    case Expr::Visitor::EConstant::NAT:
    case Expr::Visitor::EConstant::NAT1:
    case Expr::Visitor::EConstant::STRING:
    case Expr::Visitor::EConstant::REAL:
    case Expr::Visitor::EConstant::FLOAT:
    case Expr::Visitor::EConstant::TRUE:
    case Expr::Visitor::EConstant::FALSE:
      m_signature.m_operators.emplace(MonomorphizedOperator{c});
      break;
    case Expr::Visitor::EConstant::EmptySet:
      if (type.getKind() != BType::Kind::PowerType) {
        throw Exception("Empty set constant must have a powerset type");
      }
      /*
      case Expr::Visitor::EConstant::EmptySeq:
        if (type.getKind() != BType::Kind::PowerType) {
          throw Exception("Empty set constant must have a powerset type");
        }
      */
      m_signature.m_operators.emplace(MonomorphizedOperator{
          c, std::make_shared<BType>(type.toPowerType().content)});
      break;
    case Expr::Visitor::EConstant::Successor:
    case Expr::Visitor::EConstant::Predecessor:
      m_signature.m_operators.emplace(MonomorphizedOperator{c});
      break;
  }
}

void GetSignatureVisitor::visitIdent(const BType &type,
                                     const std::vector<std::string> &,
                                     const VarName &b) {
  SignatureReset(m_signature);
  if (bindings_contains(b.show())) return;
  if (type.getKind() == BType::Kind::EnumeratedSet) {
    auto etype = type.toEnumeratedSetType();
    const std::string name = b.show();
    for (const auto &elem : etype.getContent()) {
      if (elem == name) {
        m_signature.m_types.insert(std::make_shared<BType>(type));
        return;
      }
    }
  }
  struct Data data{std::make_shared<VarName>(b),
                   std::make_shared<const BType>(type)};
  m_signature.m_data.emplace(data);
}

void GetSignatureVisitor::visitIntegerLiteral(const BType &,
                                              const std::vector<std::string> &,
                                              const std::string &) {
  SignatureReset(m_signature);
}

void GetSignatureVisitor::visitStringLiteral(const BType &,
                                             const std::vector<std::string> &,
                                             const std::string &) {
  SignatureReset(m_signature);
}

void GetSignatureVisitor::visitRealLiteral(const BType &,
                                           const std::vector<std::string> &,
                                           const Expr::Decimal &) {
  SignatureReset(m_signature);
}

void GetSignatureVisitor::visitUnaryExpression(const BType &,
                                               const std::vector<std::string> &,
                                               Expr::UnaryOp op,
                                               const Expr &e) {
  SignatureReset(m_signature);
  e.accept(*this);
  switch (op) {
    case Expr::UnaryOp::Cardinality:
    case Expr::UnaryOp::Subsets:
    case Expr::UnaryOp::Non_Empty_Subsets:
    case Expr::UnaryOp::Finite_Subsets:
    case Expr::UnaryOp::Non_Empty_Finite_Subsets:
    case Expr::UnaryOp::Sequences:
    case Expr::UnaryOp::Non_Empty_Sequences:
    case Expr::UnaryOp::Injective_Sequences:
    case Expr::UnaryOp::Non_Empty_Injective_Sequences:
    case Expr::UnaryOp::Permutations: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2)));
      break;
    }
    case Expr::UnaryOp::Domain:
    case Expr::UnaryOp::Range:
    case Expr::UnaryOp::Inverse:
    case Expr::UnaryOp::Fnc: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype4)));
      break;
    }
    case Expr::UnaryOp::Identity: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2)));
      break;
    }
    case Expr::UnaryOp::Rel: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      const auto &etype5 = elementOfPowerType(op, etype4);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype5)));
      break;
    }
    case Expr::UnaryOp::Union:
    case Expr::UnaryOp::Intersection: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = elementOfPowerType(op, etype2);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3)));
      break;
    }
    case Expr::UnaryOp::Size:
    case Expr::UnaryOp::First:
    case Expr::UnaryOp::Last:
    case Expr::UnaryOp::Tail:
    case Expr::UnaryOp::Front:
    case Expr::UnaryOp::Reverse: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = rhsOfProductType(op, etype2);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3)));
      break;
    }
    case Expr::UnaryOp::Closure:
    case Expr::UnaryOp::Transitive_Closure: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3)));
      break;
    }
    case Expr::UnaryOp::Concatenation: {
      const auto &etype1 = e.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = rhsOfProductType(op, etype2);
      const auto &etype4 = elementOfPowerType(op, etype3);
      const auto &etype5 = rhsOfProductType(op, etype4);
      m_signature.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype5)));
      break;
    }
    case Expr::UnaryOp::IMinimum:
    case Expr::UnaryOp::IMaximum:
    case Expr::UnaryOp::RMinimum:
    case Expr::UnaryOp::RMaximum:
    case Expr::UnaryOp::IMinus:
    case Expr::UnaryOp::RMinus:
    case Expr::UnaryOp::Real:
    case Expr::UnaryOp::Floor:
    case Expr::UnaryOp::Ceiling: {
      m_signature.m_operators.emplace(MonomorphizedOperator(op));
      break;
    }
    case Expr::UnaryOp::Tree:
    case Expr::UnaryOp::Btree:
    case Expr::UnaryOp::Top:
    case Expr::UnaryOp::Sons:
    case Expr::UnaryOp::Prefix:
    case Expr::UnaryOp::Postfix:
    case Expr::UnaryOp::Sizet:
    case Expr::UnaryOp::Mirror:
    case Expr::UnaryOp::Left:
    case Expr::UnaryOp::Right:
    case Expr::UnaryOp::Infix:
    case Expr::UnaryOp::Bin: {
      throw Exception(fmt::format(MSG_NOT_SUPPORTED, Expr::to_string(op)));
      break;
    }
  }
}

void GetSignatureVisitor::visitBinaryExpression(
    const BType &type, const std::vector<std::string> &, Expr::BinaryOp op,
    const Expr &lhs, const Expr &rhs) {
  SignatureReset(m_signature);
  Signature sig;

  // Special case for application of successor or predecessor
  if (isApplicationPredOrSucc(op, lhs, rhs)) {
    rhs.accept(*this);
    SignatureMoveInto(sig, m_signature);
    return;
  }

  lhs.accept(*this);
  SignatureMoveInto(sig, m_signature);
  rhs.accept(*this);
  SignatureMoveInto(sig, m_signature);
  switch (op) {
      /* Set_Difference, Intersection, */
    case Expr::BinaryOp::Set_Difference:
    case Expr::BinaryOp::Intersection:
    case Expr::BinaryOp::Union: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2)));
      break;
    }
      /* Mapplet */
    case Expr::BinaryOp::Mapplet: {
      sig.m_operators.emplace(MonomorphizedOperator(op));
      break;
    }
    /*
    Cartesian_Product, Partial_Functions, Partial_Surjections,
    Total_Functions, Total_Surjections, Partial_Injections, Total_Injections,
    Partial_Bijections, Total_Bijections, Relations,
    */
    case Expr::BinaryOp::Cartesian_Product:
    case Expr::BinaryOp::Partial_Functions:
    case Expr::BinaryOp::Partial_Surjections:
    case Expr::BinaryOp::Total_Functions:
    case Expr::BinaryOp::Total_Surjections:
    case Expr::BinaryOp::Partial_Injections:
    case Expr::BinaryOp::Total_Injections:
    case Expr::BinaryOp::Partial_Bijections:
    case Expr::BinaryOp::Total_Bijections:
    case Expr::BinaryOp::Relations: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = rhs.getType();
      const auto &etype4 = elementOfPowerType(op, etype3);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2),
                                std::make_shared<BType>(etype4)));
      break;
    }
    /*
    Interval,
    IAddition, ISubtraction, IMultiplication, IDivision,
    IExponentiation, RAddition, RSubtraction, RMultiplication, RDivision,
    RExponentiation, FAddition, FSubtraction, FMultiplication, FDivision,
    Modulo,
    */
    case Expr::BinaryOp::Interval:
    case Expr::BinaryOp::IAddition:
    case Expr::BinaryOp::ISubtraction:
    case Expr::BinaryOp::IMultiplication:
    case Expr::BinaryOp::IDivision:
    case Expr::BinaryOp::IExponentiation:
    case Expr::BinaryOp::FAddition:
    case Expr::BinaryOp::FSubtraction:
    case Expr::BinaryOp::FMultiplication:
    case Expr::BinaryOp::FDivision:
    case Expr::BinaryOp::Modulo:
    case Expr::BinaryOp::RAddition:
    case Expr::BinaryOp::RSubtraction:
    case Expr::BinaryOp::RMultiplication:
    case Expr::BinaryOp::RDivision:
    case Expr::BinaryOp::RExponentiation: {
      sig.m_operators.emplace(MonomorphizedOperator(op));
      break;
    }
    /*
    Head_Insertion,
    Tail_Insertion,
    Head_Restriction,
    Tail_Restriction,
    */
    case Expr::BinaryOp::Head_Insertion: {
      const auto &etype1 = lhs.getType();
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype1)));
      break;
    }
    case Expr::BinaryOp::Tail_Insertion: {
      const auto &etype1 = rhs.getType();
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype1)));
      break;
    }
    case Expr::BinaryOp::Head_Restriction:
    case Expr::BinaryOp::Tail_Restriction: {
      const auto &etype1 = elementOfPowerType(op, type);
      const auto &etype2 = rhsOfProductType(op, etype1);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2)));
      break;
    }
    /*
    Composition,
    Direct_Product */
    case Expr::BinaryOp::Composition:
    case Expr::BinaryOp::Direct_Product: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      const auto &etype5 = rhs.getType();
      const auto &etype6 = elementOfPowerType(op, etype5);
      const auto &etype7 = rhsOfProductType(op, etype6);
      sig.m_operators.emplace(MonomorphizedOperator(
          op, std::make_shared<BType>(etype3), std::make_shared<BType>(etype4),
          std::make_shared<BType>(etype7)));
      break;
    }
    /*     Surcharge, ,
     */
    case Expr::BinaryOp::Surcharge: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype4)));
      break;
    }
    /*     Domain_Subtraction, Domain_Restriction,
     */
    case Expr::BinaryOp::Domain_Subtraction:
    case Expr::BinaryOp::Domain_Restriction: {
      const auto &etype1 = rhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype4)));
      break;
    }
    /* Parallel_Product */
    case Expr::BinaryOp::Parallel_Product: {
      // R1: P(T x U) , R2: P(V x W) -> P ((T x V) x (U x W))
      const auto &xxTVxUW = elementOfPowerType(op, type);
      const auto &xTV = lhsOfProductType(op, xxTVxUW);
      const auto &xUW = rhsOfProductType(op, xxTVxUW);
      const auto &T = lhsOfProductType(op, xTV);
      const auto &V = rhsOfProductType(op, xTV);
      const auto &U = lhsOfProductType(op, xUW);
      const auto &W = rhsOfProductType(op, xUW);
      sig.m_operators.emplace(MonomorphizedOperator(
          op, std::make_shared<BType>(T), std::make_shared<BType>(U),
          std::make_shared<BType>(V), std::make_shared<BType>(W)));
      break;
    }
    /* Concatenation */
    case Expr::BinaryOp::Concatenation: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = rhsOfProductType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3)));
      break;
    }
    /* Range_Restriction, Range_Subtraction, Image, Application */
    case Expr::BinaryOp::Range_Restriction:
    case Expr::BinaryOp::Range_Subtraction:
    case Expr::BinaryOp::Image:
    case Expr::BinaryOp::Application: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      const auto &etype4 = rhsOfProductType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype4)));
      break;
    }
    /* Iteration */
    case Expr::BinaryOp::Iteration: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = elementOfPowerType(op, etype1);
      const auto &etype3 = lhsOfProductType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3)));
      break;
    }
    /* First_Projection, Second_Projection */
    case Expr::BinaryOp::First_Projection:
    case Expr::BinaryOp::Second_Projection: {
      const auto &etype1 = lhs.getType();
      const auto &etype2 = rhs.getType();
      const auto &etype3 = elementOfPowerType(op, etype1);
      const auto &etype4 = elementOfPowerType(op, etype2);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype3),
                                std::make_shared<BType>(etype4)));
      break;
    }
    /* Const, Rank, Father, Subtree, Arity */
    case Expr::BinaryOp::Const:
    case Expr::BinaryOp::Rank:
    case Expr::BinaryOp::Father:
    case Expr::BinaryOp::Subtree:
    case Expr::BinaryOp::Arity: {
      throw Exception(fmt::format(MSG_NOT_SUPPORTED, Expr::to_string(op)));
      break;
    }
  }
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitTernaryExpression(
    const BType &, const std::vector<std::string> &, Expr::TernaryOp op,
    const Expr &, const Expr &, const Expr &) {
  throw Exception(fmt::format(MSG_NOT_SUPPORTED, Expr::to_string(op)));
}

void GetSignatureVisitor::visitNaryExpression(const BType &type,
                                              const std::vector<std::string> &,
                                              Expr::NaryOp op,
                                              const std::vector<Expr> &vec) {
  SignatureReset(m_signature);
  Signature sig;
  for (const Expr &e : vec) {
    e.accept(*this);
    SignatureMoveInto(sig, m_signature);
  }
  switch (op) {
    case Expr::NaryOp::Sequence: {
      const auto &etype1 = elementOfPowerType(op, type);
      const auto &etype2 = rhsOfProductType(op, etype1);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2)));
      break;
    }
    case Expr::NaryOp::Set: {
      const auto &etype1 = elementOfPowerType(op, type);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype1)));
      break;
    }
    default:
      break;
  }
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitBooleanExpression(
    const BType &, const std::vector<std::string> &, const Pred &p) {
  SignatureReset(m_signature);
  p.accept(*this);
}

void GetSignatureVisitor::visitRecord(
    const BType &type, const std::vector<std::string> &,
    const std::vector<std::pair<std::string, Expr>> &fds) {
  SignatureReset(m_signature);
  Signature sig;
  for (const auto &fd : fds) {
    fd.second.accept(*this);
    SignatureMoveInto(sig, m_signature);
  }
  sig.m_types.insert(std::make_shared<BType>(type));
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitStruct(
    const BType &type, const std::vector<std::string> &,
    const std::vector<std::pair<std::string, Expr>> &fds) {
  SignatureReset(m_signature);
  Signature sig;
  for (const auto &fd : fds) {
    fd.second.accept(*this);
    SignatureMoveInto(sig, m_signature);
  }
  const auto &etype1 = elementOfPowerType(Expr::EKind::Struct, type);
  sig.m_operators.emplace(MonomorphizedOperator(
      Expr::EKind::Struct, std::make_shared<BType>(etype1)));
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitQuantifiedExpr(
    const BType &type, const std::vector<std::string> &, Expr::QuantifiedOp op,
    const std::vector<TypedVar> vars, const Pred &cond, const Expr &body) {
  SignatureReset(m_signature);
  Signature sig;
  bindings_push(vars);
  cond.accept(*this);
  SignatureMoveInto(sig, m_signature);
  body.accept(*this);
  SignatureMoveInto(sig, m_signature);
  bindings_pop();
  switch (op) {
    case Expr::QuantifiedOp::Lambda: {
      const auto &etype1 = elementOfPowerType(op, type);
      const auto &etype2 = lhsOfProductType(op, etype1);
      const auto &etype3 = rhsOfProductType(op, etype1);
      sig.m_operators.emplace(
          MonomorphizedOperator(op, std::make_shared<BType>(etype2),
                                std::make_shared<BType>(etype3)));
      break;
    }
    case Expr::QuantifiedOp::Union:
    case Expr::QuantifiedOp::Intersection: {
      BType tp = vars[0].type;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, vars[i].type);
      }
      const auto &etype1 = elementOfPowerType(op, type);
      sig.m_operators.emplace(MonomorphizedOperator(
          op, std::make_shared<BType>(tp), std::make_shared<BType>(etype1)));
      break;
    }
    case Expr::QuantifiedOp::ISum:
    case Expr::QuantifiedOp::IProduct: {
      BType tp = BType::INT;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, BType::INT);
      }
      sig.m_operators.emplace(MonomorphizedOperator{
          Pred::ComparisonOp::Membership, std::make_shared<BType>(tp)});
      sig.m_operators.emplace(MonomorphizedOperator(op));
      break;
    }
    case Expr::QuantifiedOp::RSum:
    case Expr::QuantifiedOp::RProduct: {
      BType tp = BType::REAL;
      for (size_t i = 1; i < vars.size(); ++i) {
        tp = BType::PROD(tp, BType::REAL);
      }
      sig.m_operators.emplace(MonomorphizedOperator{
          Pred::ComparisonOp::Membership, std::make_shared<BType>(tp)});
      sig.m_operators.emplace(MonomorphizedOperator(op));
      break;
    }
    default:
      break;
  }
  m_signature = std::move(sig);
}

void GetSignatureVisitor::visitQuantifiedSet(const BType &type,
                                             const std::vector<std::string> &,
                                             const std::vector<TypedVar> vars,
                                             const Pred &cond) {
  SignatureReset(m_signature);
  bindings_push(vars);
  cond.accept(*this);
  const auto &etype = elementOfPowerType(Expr::EKind::QuantifiedSet, type);
  m_signature.m_operators.emplace(MonomorphizedOperator{
      Expr::EKind::QuantifiedSet, std::make_shared<BType>(etype)});
  bindings_pop();
}

void GetSignatureVisitor::visitRecordUpdate(const BType &,
                                            const std::vector<std::string> &,
                                            const Expr &, const std::string &,
                                            const Expr &) {}

void GetSignatureVisitor::visitRecordAccess(const BType &,
                                            const std::vector<std::string> &,
                                            const Expr &rec,
                                            const std::string &) {
  SignatureReset(m_signature);
  Signature sig;
  rec.accept(*this);
  SignatureMoveInto(sig, m_signature);
  sig.m_types.insert(std::make_shared<BType>(rec.getType()));
  m_signature = std::move(sig);
}

Signature predicateSignature(const Pred &pred) {
  GetSignatureVisitor visitor;
  Signature result;
  /*
  Assuming
  > COLOR = { red, black }
  then, consider the following predicates
  > c0 : COLOR &            // P
  > c1 : COLOR - { red }    // Q
  P is a pure typing predicate, whereas Q is not.
  What are the declarations that are needed for the encoding of each of these
  in SMT ? For P, one expects

  >  (declare-datatype |COLOR| ((red)(black)))
  >  (declare-const c0 |COLOR|)

  For Q, one expects

  > (declare-datatype |COLOR| ((red)(black)))
  > (declare-const c1 |COLOR|)
  > (declare-sort P 1)
  > (declare-sort |POW COLOR| (P |COLOR|))
  > (declare-const |COLOR| |POW COLOR|)
  > ...

  The case of pure typing predicates may be treated differently so that the
  generated SMT does not contain useless commands.
  */
  if (pred.isPureTypingPredicate()) {
    const Pred::ExprComparison &typingPredicate = pred.toExprComparison();
    const auto &lhs = typingPredicate.lhs;
    lhs.accept(visitor);
    result = visitor.getSignature();
    /*
    For the typing predicate
    > c0, c1 : BOOL * BOOL
    the maplet operator appears in the signature of the left hand side.
    It may be removed from the result.
    */
    result.m_operators.clear();
  } else {
    pred.accept(visitor);
    result = visitor.getSignature();
  }
  return result;
}

const BType &GetSignatureVisitor::elementOfPowerType(const BOperator &op,
                                                     const BType &power) {
  if (power.getKind() != BType::Kind::PowerType) {
    throw Exception(fmt::format(MSG_BAD_TYPE, op));
  }
  return power.toPowerType().content;
};

const BType &GetSignatureVisitor::lhsOfProductType(const BOperator &op,
                                                   const BType &product) {
  if (product.getKind() != BType::Kind::ProductType) {
    throw Exception(fmt::format(MSG_BAD_TYPE, op));
  }
  return product.toProductType().lhs;
};

const BType &GetSignatureVisitor::rhsOfProductType(const BOperator &op,
                                                   const BType &product) {
  if (product.getKind() != BType::Kind::ProductType) {
    throw Exception(fmt::format(MSG_BAD_TYPE, op));
  }
  return product.toProductType().rhs;
};

[[maybe_unused]] std::string toString(const Signature &sig) {
  std::vector<std::string> ty_strs;
  std::vector<std::string> op_strs;
  std::vector<std::string> dt_strs;
  for (const auto &ty : sig.m_types) {
    ty_strs.push_back(ty->to_string());
  }
  for (const auto &op : sig.m_operators) {
    op_strs.push_back(op.to_string());
  }
  for (const auto &dt : sig.m_data) {
    dt_strs.push_back(dt.to_string());
  }
  return fmt::format("[{} | {} | {}]", fmt::join(ty_strs, ", "),
                     fmt::join(op_strs, ", "), fmt::join(dt_strs, ", "));
}

bool operator==(const std::vector<std::shared_ptr<BType>> &lhs,
                const std::vector<std::shared_ptr<BType>> &rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (size_t i = 0; i < lhs.size(); ++i) {
    if (*lhs[i] != *rhs[i]) {
      return false;
    }
  }
  return true;
}

std::string Signature::to_string() const {
  std::vector<std::string> ty_strs;
  std::vector<std::string> op_strs;
  std::vector<std::string> dt_strs;
  for (const auto &ty : m_types) {
    ty_strs.push_back(ty->to_string());
  }
  for (const auto &op : m_operators) {
    op_strs.push_back(op.to_string());
  }
  for (const auto &dt : m_data) {
    dt_strs.push_back(dt.to_string());
  }
  return fmt::format("[{} | {} | {}]", fmt::join(ty_strs, ", "),
                     fmt::join(op_strs, ", "), fmt::join(dt_strs, ", "));
}

void GetSignatureVisitor::bindings_push(const std::vector<TypedVar> &vars) {
  unordered_set<string> bindings;
  for (auto v : vars) {
    bindings.insert(v.name.show());
  }
  m_bindings.push_back(bindings);
}

void GetSignatureVisitor::bindings_pop() { m_bindings.pop_back(); }

bool GetSignatureVisitor::bindings_contains(const string &str) {
  size_t i;
  for (i = m_bindings.size(); i != 0; --i) {
    const unordered_set<string> &names{m_bindings.at(i - 1)};
    if (names.find(str) != names.end()) {
      return true;
    }
  }
  return false;
}

bool GetSignatureVisitor::bindings_contains(const TypedVar &var) {
  return bindings_contains(var.name.show());
}

string GetSignatureVisitor::toString(const bindings_t &bindings) {
  vector<string> args1;
  for (const auto &us : bindings) {
    vector<string> args2;
    for (const auto &str : us) {
      args2.push_back(str);
    }
    args1.push_back(fmt::format("[{}]", fmt::join(args2, " ")));
  }
  return fmt::format("[{}]", fmt::join(args1, ""));
}