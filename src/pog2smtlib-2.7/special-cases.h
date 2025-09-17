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
#ifndef SPECIAL_CASES_H
#define SPECIAL_CASES_H

#include "expr.h"
#include "exprDesc.h"

inline bool isApplication(Expr::BinaryOp op) {
  return op == Expr::BinaryOp::Application;
}

inline bool isSucc(const Expr &e) {
  return e.getTag() == Expr::EKind::Successor;
}

inline bool isPred(const Expr &e) {
  return e.getTag() == Expr::EKind::Predecessor;
}

inline bool isApplicationPredOrSucc(Expr::BinaryOp op, const Expr &lhs,
                                    const Expr &) {
  return isApplication(op) && (isSucc(lhs) || isPred(lhs));
}

#endif /* SPECIAL_CASES_H */