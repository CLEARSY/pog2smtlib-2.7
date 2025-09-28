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
#ifndef TRANSLATE_OPERATOR_H
#define TRANSLATE_OPERATOR_H

#include <string>

#include "btype.h"
#include "expr.h"
#include "pred.h"

/**
 * smtSymbol yields the SMT symbol corresponding to a B operator, possibly
 * with a given type instantiation.
 */
extern std::string_view smtSymbol(Pred::PKind);
extern std::string smtSymbol(Pred::ComparisonOp);
extern std::string smtSymbol(Pred::ComparisonOp, const BType&);
extern std::string smtSymbol(Expr::EKind);
extern std::string smtSymbol(Expr::EKind, const BType&);
extern std::string smtSymbol(Expr::UnaryOp);
extern std::string smtSymbol(Expr::UnaryOp, const BType&);
extern std::string smtSymbol(Expr::UnaryOp, const BType&, const BType&);
extern std::string smtSymbol(Expr::BinaryOp);
extern std::string smtSymbol(Expr::BinaryOp, const BType&);
extern std::string smtSymbol(Expr::BinaryOp, const BType&, const BType&);
extern std::string smtSymbol(Expr::BinaryOp, const BType&, const BType&,
                             const BType&);
extern std::string smtSymbol(Expr::BinaryOp, const BType&, const BType&,
                             const BType&, const BType&);
extern std::string smtSymbol(Expr::TernaryOp);
extern std::string smtSymbol(Expr::NaryOp, const BType&);
extern std::string smtSymbol(Expr::QuantifiedOp);
extern std::string smtSymbol(Expr::QuantifiedOp, const BType&, const BType&);
extern std::string smtSymbol(Expr::Visitor::EConstant, const BType&);
extern std::string smtSymbol(Expr::Visitor::EConstant);
extern std::string smtSymbol(const VarName&);

/**
 * @brief mangles a record field name
 * @details In B, a field label may be homonymous to another symbol. Since the
 * encoding creates a symbol for the datatype accessor corresponding to this
 * field, we cannot use the field name for this symbol. This function returns
 * the SMT symbol created for this accessor.
 *
 */
extern std::string smtSymbolRecField(const std::string& label);

#endif  // TRANSLATE_OPERATOR_H
