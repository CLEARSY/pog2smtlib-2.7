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
extern std::string smtSymbol(Expr::UnaryOp);
extern std::string smtSymbol(Expr::UnaryOp, const BType&);
extern std::string smtSymbol(Expr::BinaryOp);
extern std::string smtSymbol(Expr::BinaryOp, const BType&);
extern std::string smtSymbol(Expr::BinaryOp, const BType&, const BType&);
extern std::string smtSymbol(Expr::TernaryOp);
extern std::string smtSymbol(Expr::NaryOp, const BType&);
extern std::string smtSymbol(Expr::QuantifiedOp);
extern std::string smtSymbol(Expr::Visitor::EConstant, const BType&);
extern std::string smtSymbol(const VarName&);

#endif  // TRANSLATE_OPERATOR_H
