/******************************* CLEARSY **************************************
This file is part of pog2smtlib27

Copyright (C) 2025 CLEARSY (contact@clearsy.com)

pog2smtlib27 is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License version 3 as published by
the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/
#include "translate-signature.h"

#include <queue>
#include <stack>
#include <vector>

#include "bconstruct-utils.h"
#include "bconstruct.h"
#include "cc-compatibility.h"
#include "signature.h"
#include "symbols.h"

using std::make_shared;
using std::queue;
using std::shared_ptr;
using std::stack;
using std::unordered_set;
using std::vector;

using BConstructPtr = shared_ptr<BConstruct::Abstract>;

static constexpr bool debug_me = false;

static stack<BConstructPtr> sortConstructsAndPrerequisites(
    stack<BConstructPtr> &todo, const BConstruct::Context &context);

/** @brief creates a BConstruct instance if not already created
 * @param o a monomorphized operator
 * @param queue the queue of B constructs that will be processed
 * @param context the constructs that have already been translated
 * */
static void buildAndQueueConstruct(const MonomorphizedOperator &o,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &);
/** @brief creates a BConstruct instance if not already created
 * @param dt a B data (identifier) item
 * @param queue the queue of B constructs that will be processed
 * @param context the constructs that have already been translated
 * */
static void buildAndQueueConstruct(const struct Data &dt,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &);

std::string translate(const Signature &signature) {
  BConstruct::Context context;
  return translate(signature, context);
}

std::string translate(const Signature &signature,
                      BConstruct::Context &context) {
  stack<BConstructPtr> todo;
  stack<BConstructPtr> sequence;
  for (auto &o : signature.m_operators) {
    buildAndQueueConstruct(o, todo, context);
  }
  for (auto &dt : signature.m_data) {
    buildAndQueueConstruct(dt, todo, context);
  }

  sequence = sortConstructsAndPrerequisites(todo, context);

  std::string result;
  while (!sequence.empty()) {
    const auto construct = sequence.top();
    sequence.pop();
    if (context.find(construct) == context.end()) {
      if (debug_me) {
        std::cerr << fmt::format("{}:{} construct {}\n", FILE_NAME, LINE_NUMBER,
                                 construct->to_string());
      }
      result.append(construct->script());
      context.insert(construct);
    }
  }
  return result;
}

static stack<BConstructPtr> sortConstructsAndPrerequisites(
    stack<BConstructPtr> &init, const BConstruct::Context &context) {
  std::set<BConstructPtr, BConstruct::PtrCompare> all;
  std::function<void()> sortConstructsRec;
  std::unordered_map<BConstructPtr, int, BConstruct::PtrHash,
                     BConstruct::PtrEqual>
      in_degree;

  sortConstructsRec = [&]() {
    if (init.empty()) return;
    const auto construct = init.top();
    init.pop();
    if (all.find(construct) != all.end()) {
      // already sorted, proceed
      sortConstructsRec();
    } else {
      all.insert(construct);
      in_degree[construct] = 0;
      for (const auto &p : construct->prerequisites()) {
        if (debug_me) {
          std::cerr << fmt::format("{}:{}    prerequisite {}\n", FILE_NAME,
                                   LINE_NUMBER, p->to_string());
        }
        if (context.find(p) == context.end()) {
          init.push(p);
        }
      }
      sortConstructsRec();
    }
  };

  sortConstructsRec();

  for (const auto &construct : all) {
    for (const auto &pre : construct->prerequisites()) {
      in_degree[pre]++;
    }
  }

  std::queue<BConstructPtr> q;
  for (const auto &[construct, degree] : in_degree) {
    if (degree == 0) {
      q.push(construct);
    }
  }
  stack<BConstructPtr> sorted;
  while (!q.empty()) {
    BConstructPtr current = q.front();
    q.pop();
    sorted.push(current);

    for (const auto &pre : current->prerequisites()) {
      --in_degree[pre];
      if (in_degree[pre] == 0) {
        q.push(pre);
      }
    }
  }

  return sorted;
}

static void buildAndQueueConstruct(const struct Data &dt,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &context) {
  BConstructPtr construct;
  construct = BConstruct::Factory::factory().Data(dt);
  if (construct != nullptr && context.find(construct) == context.end()) {
    queue.push(construct);
  }
}

static void buildAndQueueConstruct(const MonomorphizedOperator &o,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &context) {
  BOperator op = o.getOperator();
  vector<shared_ptr<BType>> types = o.getTypes();
  BConstructPtr construct;

  switch (op.index()) {
    case 0:  // Pred::Comparison
    {
      const auto cmp = std::get<Pred::ComparisonOp>(op);
      switch (cmp) {
        case Pred::ComparisonOp::Membership:
          construct =
              BConstruct::Factory::factory().SetMembership(*types.at(0));
          break;
        case Pred::ComparisonOp::Equality:
          construct = BConstruct::Factory::factory().Equality(*types.at(0));
          break;
        case Pred::ComparisonOp::Subset:
          construct = BConstruct::Factory::factory().Inclusion(*types.at(0));
          break;
        case Pred::ComparisonOp::Strict_Subset:
          construct =
              BConstruct::Factory::factory().StrictInclusion(*types.at(0));
          break;
        case Pred::ComparisonOp::Ige:
        case Pred::ComparisonOp::Igt:
        case Pred::ComparisonOp::Ile:
        case Pred::ComparisonOp::Ilt:
        case Pred::ComparisonOp::Rge:
        case Pred::ComparisonOp::Rgt:
        case Pred::ComparisonOp::Rle:
        case Pred::ComparisonOp::Rlt:
        case Pred::ComparisonOp::Fge:
        case Pred::ComparisonOp::Fgt:
        case Pred::ComparisonOp::Fle:
        case Pred::ComparisonOp::Flt:
          construct = BConstruct::Factory::factory().NumberComparison();
          break;
      }
      break;
    }
    case 1:  // Expr::UnaryOp
             /* Cardinality, Domain, Range, Subsets, Non_Empty_Subsets,
                Finite_Subsets, Non_Empty_Finite_Subsets, Union, Intersection,
                IMinimum, IMaximum, Sequences, Non_Empty_Sequences,
                Injective_Sequences, Non_Empty_Injective_Sequences, IMinus, RMinus,
                Inverse, Size, Permutations, First, Last, Identity, Closure,
                Transitive_Closure, Tail, Front, Reverse, Concatenation, Rel, Fnc,
                RMinimum, RMaximum, Tree, Btree, Top, Sons,
                Prefix, Postfix, Sizet, Mirror, Left, Right, Infix, Bin */
      {
        const auto unop = std::get<Expr::UnaryOp>(op);
        switch (unop) {
          /* case of operators having a counterpart in SMT theory ALL*/
          case Expr::UnaryOp::Floor:
            construct = BConstruct::Factory::factory().Floor();
            break;
          case Expr::UnaryOp::Ceiling:
            construct = BConstruct::Factory::factory().Ceiling();
            break;
          case Expr::UnaryOp::Real:
            construct = BConstruct::Factory::factory().ToReal();
            break;
          default:
            throw std::runtime_error(fmt::format(
                "{}:{} Unknown unary operator {}", FILE_NAME, LINE_NUMBER, op));
        }
        break;
      }
    case 2:  // Expr::BinaryOp
      /* Mapplet, Cartesian_Product, Partial_Functions, Partial_Surjections,
          Set_Difference, Total_Functions, Total_Surjections, Head_Insertion,
          Interval, Intersection, Head_Restriction, Composition, Surcharge,
          Relations, Tail_Insertion, Domain_Subtraction, Domain_Restriction,
          Partial_Injections, Total_Injections, Partial_Bijections,
          Total_Bijections, Direct_Product, Parallel_Product, Union,
          Tail_Restriction, Concatenation, Modulo, Range_Restriction,
          Range_Subtraction, Image, Application, IAddition, ISubtraction,
          IMultiplication, IDivision, IExponentiation, RAddition,
         RSubtraction, RMultiplication, RDivision, RExponentiation, FAddition,
         FSubtraction, FMultiplication, FDivision, Iteration,
         First_Projection, Second_Projection, Const, Rank, Father, Subtree,
          Arity */
      {
        const Expr::BinaryOp binop = std::get<Expr::BinaryOp>(op);
        switch (binop) {
          /* the following have counterparts in SMT theory ALL*/

          /* 5.3 Arithmetical Expressions */
          case Expr::BinaryOp::IAddition:
          case Expr::BinaryOp::ISubtraction:
          case Expr::BinaryOp::IMultiplication:
          case Expr::BinaryOp::RAddition:
          case Expr::BinaryOp::RSubtraction:
          case Expr::BinaryOp::RMultiplication:
          case Expr::BinaryOp::RDivision:
            construct = nullptr;
            break;
          case Expr::BinaryOp::IDivision:
            construct = BConstruct::Factory::factory().IntegerDivision();
            break;

          /* 5.5 Expression of Couples */
          case Expr::BinaryOp::Mapplet:
            construct = BConstruct::Factory::factory().Maplet();
            break;

          /* 5.7 Set List Expressions */
          case Expr::BinaryOp::Cartesian_Product:
            construct =
                BConstruct::Factory::factory().ExpressionCartesianProduct(
                    *types.at(0), *types.at(1));
            break;
          default:
            throw std::runtime_error(
                fmt::format("{}:{} Unknown binary operator {}", FILE_NAME,
                            LINE_NUMBER, Expr::to_string(binop)));
        }
        break;
      }
    case 3:  // Expr::TernaryOp
      /* Son, Bin */
      throw std::runtime_error(fmt::format(
          "{}:{} Ternary operator are not supported", FILE_NAME, LINE_NUMBER));
    case 4:  // Expr::NaryOp
      /* Sequence, Set */
      throw std::runtime_error(
          fmt::format("{}:{} Unknown operator {}", FILE_NAME, LINE_NUMBER, op));
    case 5:  // Expr::QuantifiedOp
      /* Lambda, Intersection, Union, ISum, IProduct, RSum, RProduct */
      throw std::runtime_error(
          fmt::format("{}:{} Unknown operator {}", FILE_NAME, LINE_NUMBER, op));
    case 6:  // Expr::Visitor::EConstant => duplicate with Expr::EKind !!
             /* MaxInt, MinInt, INTEGER, NATURAL, NATURAL1, INT, NAT, NAT1,
                STRING, BOOL, REAL, FLOAT, TRUE, FALSE, EmptySet, Successor,
                Predecessor
                     */
      {
        const auto econst = std::get<Expr::Visitor::EConstant>(op);
        switch (econst) {
          /* 5.1 Boolean Expressions */
          case Expr::Visitor::EConstant::TRUE:
          case Expr::Visitor::EConstant::FALSE:
            construct = nullptr;
            break;

          /* 5.3 Arithmetical Expressions */
          case Expr::Visitor::EConstant::MaxInt:
            construct = BConstruct::Factory::factory().Maxint();
            break;
          case Expr::Visitor::EConstant::MinInt:
            construct = BConstruct::Factory::factory().Minint();
            break;

          /* 5.6 Building Sets */
          case Expr::Visitor::EConstant::INTEGER:
            construct = BConstruct::Factory::factory().Integer();
            break;
          case Expr::Visitor::EConstant::REAL:
            construct = BConstruct::Factory::factory().Real();
            break;
          case Expr::Visitor::EConstant::BOOL:
            construct = BConstruct::Factory::factory().Bool();
            break;
          case Expr::Visitor::EConstant::NAT:
            construct = BConstruct::Factory::factory().Nat();
            break;
          case Expr::Visitor::EConstant::NAT1:
            construct = BConstruct::Factory::factory().Nat1();
            break;
          case Expr::Visitor::EConstant::NATURAL:
            construct = BConstruct::Factory::factory().Natural();
            break;
          case Expr::Visitor::EConstant::NATURAL1:
            construct = BConstruct::Factory::factory().Natural1();
            break;
          case Expr::Visitor::EConstant::INT:
            construct = BConstruct::Factory::factory().Int();
            break;

          case Expr::Visitor::EConstant::EmptySet:
            if (types.size() != 1) {
              throw std::runtime_error(
                  fmt::format("Erroneous typing information associated to "
                              "empty set operator",
                              FILE_NAME, LINE_NUMBER));
            }
            construct = BConstruct::Factory::factory().EmptySet(*types.at(0));
            break;
          default:
            throw std::runtime_error(
                fmt::format("{}:{} Unknown constant expression {}", FILE_NAME,
                            LINE_NUMBER, op));
        }
        break;
      }
    case 7:  // Expr::EKind
             /* MaxInt, MinInt, INTEGER, NATURAL, NATURAL1, INT, NAT, NAT1,
                STRING, BOOL, REAL, FLOAT, TRUE, FALSE, EmptySet, IntegerLiteral,
                    StringLiteral, RealLiteral, Id, BooleanExpr, QuantifiedExpr,
                    QuantifiedSet, UnaryExpr, BinaryExpr, NaryExpr, Struct,
                Record, TernaryExpr, Record_Field_Access, Record_Field_Update,
                Successor, Predecessor */
      throw std::runtime_error(
          fmt::format("{}:{} Unknown operator {}", FILE_NAME, LINE_NUMBER, op));
  }

  if (construct != nullptr && context.find(construct) == context.end()) {
    queue.push(construct);
  }
}
