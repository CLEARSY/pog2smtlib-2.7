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
#ifndef SYMBOLS_H
#define SYMBOLS_H

#include <fmt/format.h>

#include <functional>
#include <utility>
#include <variant>

#include "btype.h"
#include "expr.h"
#include "pred.h"

/**
 * @brief Represents an operator in the B2SMTLIB language.
 */
using BOperator =
    std::variant<Pred::ComparisonOp, Expr::UnaryOp, Expr::BinaryOp,
                 Expr::TernaryOp, Expr::NaryOp, Expr::QuantifiedOp,
                 Expr::Visitor::EConstant, Expr::EKind>;

namespace std {
template <> struct hash<BOperator> {
  size_t operator()(const BOperator& op) const {
    switch (op.index()) {
      case 0:
        return std::hash<Pred::ComparisonOp>{}(
            std::get<Pred::ComparisonOp>(op));
      case 1:
        return std::hash<Expr::UnaryOp>{}(std::get<Expr::UnaryOp>(op));
      case 2:
        return std::hash<Expr::BinaryOp>{}(std::get<Expr::BinaryOp>(op));
      case 3:
        return std::hash<Expr::TernaryOp>{}(std::get<Expr::TernaryOp>(op));
      case 4:
        return std::hash<Expr::NaryOp>{}(std::get<Expr::NaryOp>(op));
      case 5:
        return std::hash<Expr::QuantifiedOp>{}(
            std::get<Expr::QuantifiedOp>(op));
      case 6:
        return std::hash<Expr::Visitor::EConstant>{}(
            std::get<Expr::Visitor::EConstant>(op));
      default:
        return 0;  // unreachable
    }
  }
};
}  // namespace std

/** @brief Overloads formatter to use the fmt library for BOperator values */
template <> struct fmt::formatter<BOperator> : formatter<string_view> {
  auto format(BOperator op, format_context& ctx) const
      -> format_context::iterator;
};

/** @brief Overloads formatter to use the fmt library for BType values */
template <> struct fmt::formatter<BType> : formatter<string_view> {
  auto format(BType type, format_context& ctx) const
      -> format_context::iterator;
};

extern std::string to_string(const BOperator& op);

#endif  // SYMBOLS_H