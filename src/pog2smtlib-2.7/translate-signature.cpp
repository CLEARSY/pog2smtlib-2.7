/******************************* CLEARSY **************************************
This file is part of pog2smtlib-2.7

Copyright (C) 2025 CLEARSY (contact@clearsy.com)

pog2smtlib-2.7 is free software: you can redistribute it and/or modify
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
 * @param t a B type
 * @param queue the queue of B constructs that will be processed
 * @param context the constructs that have already been translated
 * */
static void buildAndQueueConstruct(const std::shared_ptr<BType> &t,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &);

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
  for (auto &t : signature.m_types) {
    buildAndQueueConstruct(t, todo, context);
  }
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

static void buildAndQueueConstruct(const std::shared_ptr<BType> &t,
                                   stack<BConstructPtr> &queue,
                                   const BConstruct::Context &context) {
  BConstructPtr construct;
  construct = BConstruct::Factory::factory().Type(*t);
  if (construct != nullptr && context.find(construct) == context.end()) {
    queue.push(construct);
  }
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

          /* 5.3 Arithmetical Expressions */
          case Expr::UnaryOp::Floor:
            construct = BConstruct::Factory::factory().Floor();
            break;
          case Expr::UnaryOp::Ceiling:
            construct = BConstruct::Factory::factory().Ceiling();
            break;
          case Expr::UnaryOp::Real:
            construct = BConstruct::Factory::factory().ToReal();
            break;

          /* 5.4 Arithmetical Expressions (continued) */
          case Expr::UnaryOp::IMaximum:
            construct = BConstruct::Factory::factory().Max();
            break;
          case Expr::UnaryOp::IMinimum:
            construct = BConstruct::Factory::factory().Min();
            break;
          case Expr::UnaryOp::RMaximum:
            construct = BConstruct::Factory::factory().RMax();
            break;
          case Expr::UnaryOp::RMinimum:
            construct = BConstruct::Factory::factory().RMin();
            break;
          case Expr::UnaryOp::Cardinality:
            construct = BConstruct::Factory::factory().Card(*types.at(0));
            break;

          /* 5.7 Set List Expressions */
          case Expr::UnaryOp::Subsets:
            construct = BConstruct::Factory::factory().PowerSet(*types.at(0));
            break;
          case Expr::UnaryOp::Non_Empty_Subsets:
            construct = BConstruct::Factory::factory().PowerSet1(*types.at(0));
            break;
          case Expr::UnaryOp::Finite_Subsets:
            construct = BConstruct::Factory::factory().Fin(*types.at(0));
            break;
          case Expr::UnaryOp::Non_Empty_Finite_Subsets:
            construct = BConstruct::Factory::factory().Fin1(*types.at(0));
            break;

          /* 5.8 Set List Expressions (continued) */
          case Expr::UnaryOp::Union:
            construct =
                BConstruct::Factory::factory().GeneralizedUnion(*types.at(0));
            break;
          case Expr::UnaryOp::Intersection:
            construct = BConstruct::Factory::factory().GeneralizedIntersection(
                *types.at(0));
            break;

          /* 5.11 Expressions of Relations */
          case Expr::UnaryOp::Identity:
            construct = BConstruct::Factory::factory().Identity(*types.at(0));
            break;
          case Expr::UnaryOp::Inverse:
            construct = BConstruct::Factory::factory().Reverse(*types.at(0),
                                                               *types.at(1));
            break;

          /* 5.12 Expressions of Relations */
          case Expr::UnaryOp::Closure:
            construct = BConstruct::Factory::factory().Closure(*types.at(0));
            break;
          case Expr::UnaryOp::Transitive_Closure:
            construct = BConstruct::Factory::factory().Closure1(*types.at(0));
            break;

          /* 5.13 Expressions of Relations */
          case Expr::UnaryOp::Domain:
            construct = BConstruct::Factory::factory().Domain(*types.at(0),
                                                              *types.at(1));
            break;
          case Expr::UnaryOp::Range:
            construct = BConstruct::Factory::factory().Range(*types.at(0),
                                                             *types.at(1));
            break;

          /* 5.16 Expressions of Functions */
          case Expr::UnaryOp::Fnc:
            construct =
                BConstruct::Factory::factory().Transformed_Into_Function(
                    *types.at(0), *types.at(1));
            break;
          case Expr::UnaryOp::Rel:
            construct =
                BConstruct::Factory::factory().Transformed_Into_Relation(
                    *types.at(0), *types.at(1));
            break;

          /* 5.17 Set of Sequences */
          case Expr::UnaryOp::Sequences:
            construct = BConstruct::Factory::factory().Seq(*types.at(0));
            break;
          case Expr::UnaryOp::Non_Empty_Sequences:
            construct = BConstruct::Factory::factory().Seq1(*types.at(0));
            break;
          case Expr::UnaryOp::Injective_Sequences:
            construct =
                BConstruct::Factory::factory().Injective_Seq(*types.at(0));
            break;
          case Expr::UnaryOp::Non_Empty_Injective_Sequences:
            construct =
                BConstruct::Factory::factory().Injective_Seq1(*types.at(0));
            break;
          case Expr::UnaryOp::Permutations:
            construct = BConstruct::Factory::factory().Perm(*types.at(0));
            break;

          /* 5.18 Expressions of Sequences */
          case Expr::UnaryOp::Size:
            construct = BConstruct::Factory::factory().Size(*types.at(0));
            break;
          case Expr::UnaryOp::First:
            construct = BConstruct::Factory::factory().First(*types.at(0));
            break;
          case Expr::UnaryOp::Last:
            construct = BConstruct::Factory::factory().Last(*types.at(0));
            break;
          case Expr::UnaryOp::Front:
            construct = BConstruct::Factory::factory().Front(*types.at(0));
            break;
          case Expr::UnaryOp::Tail:
            construct = BConstruct::Factory::factory().Tail(*types.at(0));
            break;
          case Expr::UnaryOp::Reverse:
            construct = BConstruct::Factory::factory().Rev(*types.at(0));
            break;
          /* 5.19 Expressions of Sequences */
          case Expr::UnaryOp::Concatenation:
            construct = BConstruct::Factory::factory().General_Concatenation(
                *types.at(0));
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
          case Expr::BinaryOp::Modulo:
            construct = nullptr;
            break;
          case Expr::BinaryOp::IDivision:
            construct = BConstruct::Factory::factory().IntegerDivision();
            break;
          case Expr::BinaryOp::IExponentiation:
            construct = BConstruct::Factory::factory().Exponentiation();
            break;
          case Expr::BinaryOp::RDivision:
            construct = BConstruct::Factory::factory().RealDivision();
            break;
          case Expr::BinaryOp::RExponentiation:
            construct = BConstruct::Factory::factory().RExponentiation();
            break;

          /* 5.5 Expression of Couples */
          case Expr::BinaryOp::Mapplet:
            construct = BConstruct::Factory::factory().Maplet();
            break;

          /* 5.7 Set List Expressions */
          case Expr::BinaryOp::Interval:
            construct = BConstruct::Factory::factory().Interval();
            break;
          case Expr::BinaryOp::Cartesian_Product:
            construct =
                BConstruct::Factory::factory().ExpressionCartesianProduct(
                    *types.at(0), *types.at(1));
            break;

          /* 5.8 Set List Expressions (continued)*/
          case Expr::BinaryOp::Set_Difference:
            construct = BConstruct::Factory::factory().Difference(*types.at(0));
            break;
          case Expr::BinaryOp::Union:
            construct = BConstruct::Factory::factory().Union(*types.at(0));
            break;
          case Expr::BinaryOp::Intersection:
            construct =
                BConstruct::Factory::factory().Intersection(*types.at(0));
            break;

          /* 5.10 Set of Relations */
          case Expr::BinaryOp::Relations:
            construct = BConstruct::Factory::factory().Relation(*types.at(0),
                                                                *types.at(1));
            break;

          /* 5.11 Expressions of Relations */
          case Expr::BinaryOp::First_Projection:
            construct =
                BConstruct::Factory::factory().Prj1(*types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Second_Projection:
            construct =
                BConstruct::Factory::factory().Prj2(*types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Composition:
            construct = BConstruct::Factory::factory().Composition(
                *types.at(0), *types.at(1), *types.at(2));
            break;
          case Expr::BinaryOp::Direct_Product:
            construct = BConstruct::Factory::factory().Direct_Product(
                *types.at(0), *types.at(1), *types.at(2));
            break;
          case Expr::BinaryOp::Parallel_Product:
            construct = BConstruct::Factory::factory().Parallel_Product(
                *types.at(0), *types.at(1), *types.at(2), *types.at(3));
            break;

          /* 5.12 Expressions of Relations */
          case Expr::BinaryOp::Iteration:
            construct = BConstruct::Factory::factory().Iteration(*types.at(0));
            break;

          /* 5.13 Expressions of Relations */
          case Expr::BinaryOp::Image:
            construct = BConstruct::Factory::factory().Image(*types.at(0),
                                                             *types.at(1));
            break;

          /* 5.14 Expressions of Relations */
          case Expr::BinaryOp::Domain_Restriction:
            construct = BConstruct::Factory::factory().Restriction_Domain(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Domain_Subtraction:
            construct = BConstruct::Factory::factory().Subtraction_Domain(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Range_Restriction:
            construct = BConstruct::Factory::factory().Restriction_Range(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Range_Subtraction:
            construct = BConstruct::Factory::factory().Subtraction_Range(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Surcharge:
            construct = BConstruct::Factory::factory().Overwrite(*types.at(0),
                                                                 *types.at(1));
            break;

          /* 5.15 Sets of Functions */
          case Expr::BinaryOp::Partial_Functions:
            construct = BConstruct::Factory::factory().Partial_Function(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Total_Functions:
            construct = BConstruct::Factory::factory().Total_Function(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Partial_Injections:
            construct = BConstruct::Factory::factory().Partial_Injection(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Total_Injections:
            construct = BConstruct::Factory::factory().Total_Injection(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Partial_Surjections:
            construct = BConstruct::Factory::factory().Partial_Surjection(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Total_Surjections:
            construct = BConstruct::Factory::factory().Total_Surjection(
                *types.at(0), *types.at(1));
            break;
          case Expr::BinaryOp::Total_Bijections:
            construct = BConstruct::Factory::factory().Total_Bijection(
                *types.at(0), *types.at(1));
            break;

          /* 5.16 Expressions of Functions */
          case Expr::BinaryOp::Application:
            construct = BConstruct::Factory::factory().Evaluation(*types.at(0),
                                                                  *types.at(1));
            break;

          /* 5.19 Expressions of Sequences */
          case Expr::BinaryOp::Concatenation:
            construct =
                BConstruct::Factory::factory().Concatenation(*types.at(0));
            break;
          case Expr::BinaryOp::Head_Insertion:
            construct =
                BConstruct::Factory::factory().Insert_In_Front(*types.at(0));
            break;
          case Expr::BinaryOp::Tail_Insertion:
            construct =
                BConstruct::Factory::factory().Insert_At_Tail(*types.at(0));
            break;
          case Expr::BinaryOp::Head_Restriction:
            construct =
                BConstruct::Factory::factory().Restrict_In_Front(*types.at(0));
            break;
          case Expr::BinaryOp::Tail_Restriction:
            construct =
                BConstruct::Factory::factory().Restrict_At_Tail(*types.at(0));
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
      {
        const Expr::NaryOp nop = std::get<Expr::NaryOp>(op);
        switch (nop) {
          /* 5.7 Set List Expressions */
          case Expr::NaryOp::Set:
            construct = BConstruct::Factory::factory().Set(*types.at(0));
            break;
          case Expr::NaryOp::Sequence:
            construct = BConstruct::Factory::factory().Set(
                BType::PROD(BType::INT, *types.at(0)));
            break;
          default:
            throw std::runtime_error(
                fmt::format("{}:{} Unknown Nary operator {}", FILE_NAME,
                            LINE_NUMBER, Expr::to_string(nop)));
        }
        break;
      }
    case 5:  // Expr::QuantifiedOp
      /* Lambda, Intersection, Union, ISum, IProduct, RSum, RProduct */
      {
        const Expr::QuantifiedOp qop = std::get<Expr::QuantifiedOp>(op);
        switch (qop) {
          case Expr::QuantifiedOp::Lambda:
            construct = BConstruct::Factory::factory().Lambda(*types.at(0),
                                                              *types.at(1));
            break;
          case Expr::QuantifiedOp::Union:
            construct = BConstruct::Factory::factory().Quantified_Union(
                *types.at(0), *types.at(1));
            break;
          case Expr::QuantifiedOp::Intersection:
            construct = BConstruct::Factory::factory().Quantified_Intersection(
                *types.at(0), *types.at(1));
            break;
          case Expr::QuantifiedOp::ISum:
            construct = BConstruct::Factory::factory().GeneralizedSum();
            break;
          case Expr::QuantifiedOp::IProduct:
            construct = BConstruct::Factory::factory().GeneralizedProduct();
            break;
          case Expr::QuantifiedOp::RSum:
            construct = BConstruct::Factory::factory().RGeneralizedSum();
            break;
          case Expr::QuantifiedOp::RProduct:
            construct = BConstruct::Factory::factory().RGeneralizedProduct();
            break;
          default:
            throw std::runtime_error(
                fmt::format("{}:{} Unknown Quantified operator {}", FILE_NAME,
                            LINE_NUMBER, Expr::to_string(qop)));
        }
        break;
      }
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
          case Expr::Visitor::EConstant::Successor:
            construct = BConstruct::Factory::factory().Succ();
            break;
          case Expr::Visitor::EConstant::Predecessor:
            construct = BConstruct::Factory::factory().Predecessor();
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
          case Expr::Visitor::EConstant::STRING:
            construct = BConstruct::Factory::factory().String();
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
      {
        const Expr::EKind ekind = std::get<Expr::EKind>(op);
        switch (ekind) {
          /* 5.7 Set List Expressions */
          case Expr::EKind::QuantifiedSet:
            construct = BConstruct::Factory::factory().Set(*types.at(0));
            break;

          /* 5.9 Expressions of Records */
          case Expr::EKind::Struct:
            construct = BConstruct::Factory::factory().Struct(*types.at(0));
            break;
          default:
            throw std::runtime_error(
                fmt::format("{}:{} operator {} is not supported", FILE_NAME,
                            LINE_NUMBER, op));
        }
        break;
      }
  }

  if (construct != nullptr && context.find(construct) == context.end()) {
    queue.push(construct);
  }
}
