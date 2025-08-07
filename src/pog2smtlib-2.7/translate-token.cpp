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
#include "translate-token.h"

#include <fmt/core.h>

#include <exception>
#include <unordered_map>

#include "btype-symbols.h"
#include "cc-compatibility.h"

using std::string;
using std::string_view;

static std::unordered_map<Pred::PKind, std::string>
    predicateOperatorToStringMap = {
        {Pred::PKind::Implication, "=>"},  {Pred::PKind::Equivalence, "="},
        {Pred::PKind::Conjunction, "and"}, {Pred::PKind::Disjunction, "or"},
        {Pred::PKind::Forall, "forall"},   {Pred::PKind::Exists, "exists"},
        {Pred::PKind::Negation, "not"},    {Pred::PKind::True, "true"},
        {Pred::PKind::False, "false"},
        // Pred::PKind::ExprComparison:
};

string_view smtSymbol(Pred::PKind kind) {
  return predicateOperatorToStringMap[kind];
}

string smtSymbol(Pred::ComparisonOp op) {
  switch (op) {
    case Pred::ComparisonOp::Equality:
      return "=";
    case Pred::ComparisonOp::Ige:
    case Pred::ComparisonOp::Fge:
    case Pred::ComparisonOp::Rge:
      return ">=";
    case Pred::ComparisonOp::Igt:
    case Pred::ComparisonOp::Fgt:
    case Pred::ComparisonOp::Rgt:
      return ">";
    case Pred::ComparisonOp::Ilt:
    case Pred::ComparisonOp::Flt:
    case Pred::ComparisonOp::Rlt:
      return "<";
    case Pred::ComparisonOp::Ile:
    case Pred::ComparisonOp::Fle:
    case Pred::ComparisonOp::Rle:
      return "<=";
    default:
      return "smtSymbol(Pred::ComparisonOp)";
  }
}

string smtSymbol(Pred::ComparisonOp op, const BType& type) {
  switch (op) {
    case Pred::ComparisonOp::Membership:
      return fmt::format("|set.in {0}|", symbolInner(type));
    case Pred::ComparisonOp::Subset:
      return fmt::format("|set.subseteq {0}|", symbolInner(type));
    case Pred::ComparisonOp::Strict_Subset:
      return fmt::format("|set.subset {0}|", symbolInner(type));
    default:
      return "smtSymbol(Pred::ComparisonOp, const BType&)";
  }
}

static std::unordered_map<Expr::UnaryOp, std::string> unOpExprToStringMap = {
    /* 5.3 Arithmetical Expressions I */
    {Expr::UnaryOp::Real, "|int.real|"},
    {Expr::UnaryOp::Floor, "|real.floor|"},
    {Expr::UnaryOp::Ceiling, "|real.ceiling|"},

    /* 5.7 Set List Expressions */
    {Expr::UnaryOp::Subsets, "sub-sets"},
    {Expr::UnaryOp::Non_Empty_Subsets, "non empty sub-sets"},

    /* 5.13 Expressions of Relations */
    {Expr::UnaryOp::Domain, "rel.domain"},
    {Expr::UnaryOp::Range, "rel.range"}
};

std::string smtSymbol(Expr::UnaryOp op) {
  const auto itr = unOpExprToStringMap.find(op);
  if (itr == unOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  return itr->second;
}

std::string smtSymbol(Expr::UnaryOp op, const BType& t) {
  const auto itr = unOpExprToStringMap.find(op);
  if (itr == unOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  string& str = itr->second;
  return fmt::format("|{0} {1}|", str, symbolInner(t));
}

std::string smtSymbol(Expr::UnaryOp op, const BType& t1, const BType& t2) {
  const auto itr = unOpExprToStringMap.find(op);
  if (itr == unOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  string& str = itr->second;
  return fmt::format("|{0} {1} {2}|", str, symbolInner(t1), symbolInner(t2));
}


static std::unordered_map<Expr::BinaryOp, std::string> binOpExprToStringMap = {
    /* 5.3 Arithmetical Expressions I */
    {Expr::BinaryOp::IAddition, "+"},
    {Expr::BinaryOp::RAddition, "+"},
    {Expr::BinaryOp::ISubtraction, "-"},
    {Expr::BinaryOp::RSubtraction, "-"},
    {Expr::BinaryOp::IMultiplication, "*"},
    {Expr::BinaryOp::RMultiplication, "*"},
    {Expr::BinaryOp::IDivision, "|int.div|"},
    {Expr::BinaryOp::RDivision, "/"},

    /* 5.5 Expression of Couples */
    {Expr::BinaryOp::Mapplet, "maplet"},
    
    /* 5.7 Set List Expressions */
    {Expr::BinaryOp::Cartesian_Product, "set.product"},
    {Expr::BinaryOp::Interval, "|interval|"},

    /* 5.13 Expressions of Relations */
    {Expr::BinaryOp::Image, "rel.image"}
};

std::string smtSymbol(Expr::BinaryOp op) {
  const auto itr = binOpExprToStringMap.find(op);
  if (itr == binOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  return itr->second;
}

std::string smtSymbol(Expr::BinaryOp op, const BType& t1, const BType& t2) {
  const auto itr = binOpExprToStringMap.find(op);
  if (itr == binOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  string& str = itr->second;
  return fmt::format("|{0} {1} {2}|", str, symbolInner(t1), symbolInner(t2));
}

std::string smtSymbol(Expr::BinaryOp op, const BType& t1, const BType& t2, const BType& t3) {
  const auto itr = binOpExprToStringMap.find(op);
  if (itr == binOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  string& str = itr->second;
  return fmt::format("|{0} {1} {2} {3}|", str, symbolInner(t1), symbolInner(t2), symbolInner(t3));
}

static std::unordered_map<Expr::NaryOp, std::string> nOpExprToStringMap = {
    /* 5.7 Set List Expressions */
    {Expr::NaryOp::Set, "set.intent"}
};

string smtSymbol(Expr::NaryOp op, const BType& type) {
  const auto itr = nOpExprToStringMap.find(op);
  if (itr == nOpExprToStringMap.end()) {
    throw std::runtime_error(fmt::format("{}:{} unexpected operator {}",
                                         FILE_NAME, LINE_NUMBER,
                                         Expr::to_string(op)));
  }
  string& str = itr->second;
  return fmt::format("|{0} {1}|", str, symbolInner(type));
}

static std::unordered_map<Expr::Visitor::EConstant, std::string>
    constantToStringMap = {
        /* 5.2 Boolean Expressions */
        {Expr::Visitor::EConstant::TRUE, "true"},
        {Expr::Visitor::EConstant::FALSE, "false"},

        /* 5.3 Arithmetical Expressions I */
        {Expr::Visitor::EConstant::MaxInt, "MAXINT"},
        {Expr::Visitor::EConstant::MinInt, "MININT"},
        {Expr::Visitor::EConstant::Successor, "succ"},
        {Expr::Visitor::EConstant::Predecessor, "pred"},
        
        /* 5.6 Building Sets */
        {Expr::Visitor::EConstant::INTEGER, "INTEGER"},
        {Expr::Visitor::EConstant::NATURAL, "NATURAL"},
        {Expr::Visitor::EConstant::NATURAL1, "NATURAL1"},
        {Expr::Visitor::EConstant::INT, "INT"},
        {Expr::Visitor::EConstant::NAT, "NAT"},
        {Expr::Visitor::EConstant::NAT1, "NAT1"},
        {Expr::Visitor::EConstant::BOOL, "BOOL"},
        {Expr::Visitor::EConstant::STRING, "STRING"},
        {Expr::Visitor::EConstant::REAL, "REAL"},
        {Expr::Visitor::EConstant::FLOAT, "FLOAT"},
};

std::string smtSymbol(Expr::Visitor::EConstant c) {
  if (c == Expr::Visitor::EConstant::EmptySet) {
    throw std::runtime_error(fmt::format("{}:{} unexpected parameter value",
                                         FILE_NAME, LINE_NUMBER));
  }
  const auto itr = constantToStringMap.find(c);
  if (itr == constantToStringMap.end()) {
    throw std::runtime_error(
        fmt::format("{}:{} unexpected constant", FILE_NAME, LINE_NUMBER));
  }
  return itr->second;
}

std::string smtSymbol(Expr::Visitor::EConstant c, const BType& type) {
  if (c == Expr::Visitor::EConstant::EmptySet) {
    return fmt::format("|set.empty {0}|", symbolInner(type));
  } else {
    return smtSymbol(c);
  }
}

std::string smtSymbol(const VarName& token) {
  if (token.kind() == VarName::Kind::NoSuffix) {
    return token.prefix();
  } else if (token.kind() == VarName::Kind::WithSuffix) {
    return fmt::format("{}${}", token.prefix(), token.suffix());
  } else {
    throw std::runtime_error(
        fmt::format("{}:{} Invalid kind() return for VarName parameter ({})",
                    FILE_NAME, LINE_NUMBER, token.prefix()));
  }
}