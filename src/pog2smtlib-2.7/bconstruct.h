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
#ifndef BBIT_H
#define BBIT_H

#include <memory>
#include <set>
#include <string>
#include <variant>

#include "btype.h"
#include "signature.h"

namespace BConstruct {

class Abstract;

namespace Type {
class Type;
class PowerSet;
class CartesianProduct;
};  // namespace Type

namespace Predicate {
class SetMembership;
class Equality;
class Inclusion;
class StrictInclusion;
class NumberComparison;
};  // namespace Predicate

namespace Expression {
/* 5.1 Primary Expressions */
class Data;

/* 5.2 Boolean Expressions */
class BooleanExpression;

/* 5.3 Arithmetical Expressions */
class Maxint;
class Minint;
class Addition;
class Subtraction;
class Multiplication;
class IntegerDivision;
class RealDivision;
class Floor;
class Ceiling;
class ToReal;
class Succ;
class Predecessor;
class Exponentiation;
class RExponentiation;

/* 5.4 Arithmetical Expressions (continued) */
class Max;
class Min;
class RMax;
class RMin;
class Cardinals;
class Card;
class GeneralizedSum;
class GeneralizedProduct;
class RGeneralizedSum;
class RGeneralizedProduct;

/* 5.5 Expression of Couples */
class Maplet;

/* 5.6 Building Sets */
class EmptySet;
class Integer;
class Natural;
class Natural1;
class Nat;
class Nat1;
class Real;
class Bool;
class Int;

/* 5.7 Set List Expressions */
class PowerSet;
class PowerSet1;
class Interval;
class CartesianProduct;
class Set;
class Fin;
class Fin1;

/* 5.8 Set List Expressions (continued) */
class Difference;
class Union;
class Intersection;
class GeneralizedUnion;
class GeneralizedIntersection;
class Quantified_Union;
class Quantified_Intersection;

/* 5.10 Set of Relations */
class Relation;
class Total_Relation;

/* 5.11 Expressions of Relations */
class Identity;
class Reverse;
class Prj1;
class Prj2;
class Composition;
class Direct_Product;
class Parallel_Product;

/* 5.12 Expressions of Relations */
class Iteration;
class Closure;
class Closure1;

/* 5.13 Expressions of Relations */
class Domain;
class Range;
class Image;

/* 5.14 Expressions of Relations */
class Restriction_Domain;
class Subtraction_Domain;
class Restriction_Range;
class Subtraction_Range;
class Overwrite;

/* 5.15 Sets of Functions */
class Injection;
class Surjection;
class Bijection;
class Function;
class Partial_Function;
class Total_Function;
class Partial_Injection;
class Total_Injection;
class Partial_Surjection;
class Total_Surjection;
class Total_Bijection;

/* 5.16 Expressions of Functions */
class Evaluation;
class Transformed_Into_Function;
class Transformed_Into_Relation;
class Lambda;

/* 5.17 Set of Sequences */
class Seq;
class Seq1;
class Injective_Seq;
class Injective_Seq1;
class Perm;
class EmptySeq;

/* 5.18 Expressions of Sequences */
class Size;
class First;
class Last;
class Front;
class Tail;
class Rev;

/* 5.19 Expressions of Sequences */
class Concatenation;
class Insert_In_Front;
class Insert_At_Tail;
class Restrict_In_Front;
class Restrict_At_Tail;
class General_Concatenation;

};  // namespace Expression

class Factory {
 public:
  static Factory &factory() {
    static Factory instance;
    return instance;
  }

 private:
  Factory() {}

 public:
  Factory(const Factory &) = delete;
  Factory &operator=(const Factory &) = delete;

  /**
   * @brief Gets the number of BConstruct instances created by the factory.
   * @return The number of created BConstruct instances.
   */
  size_t size();
  /**
   * @brief Gets the BConstruct at a specific index in the factory's internal
   * index.
   * @param index The index of the Expression to retrieve.
   * @return A shared pointer to the Expression at the given index.
   */
  std::shared_ptr<Abstract> at(size_t index);

  std::shared_ptr<Abstract> Type(const BType &);
  std::shared_ptr<Abstract> PowerSet();
  std::shared_ptr<Abstract> CartesianProduct();
  std::shared_ptr<Abstract> SetMembership(const BType &);
  std::shared_ptr<Abstract> Equality(const BType &);
  std::shared_ptr<Abstract> Inclusion(const BType &);
  std::shared_ptr<Abstract> StrictInclusion(const BType &);
  std::shared_ptr<Abstract> NumberComparison();

  /* 5.1 Primary Expressions */
  std::shared_ptr<Abstract> Data(const Data &);

  /* 5.2 Boolean Expressions */
  std::shared_ptr<Abstract> BooleanExpression();

  /* 5.3 Arithmetical Expressions */
  std::shared_ptr<Abstract> Maxint();
  std::shared_ptr<Abstract> Minint();
  std::shared_ptr<Abstract> Addition();
  std::shared_ptr<Abstract> Subtraction();
  std::shared_ptr<Abstract> Multiplication();
  std::shared_ptr<Abstract> IntegerDivision();
  std::shared_ptr<Abstract> Floor();
  std::shared_ptr<Abstract> Ceiling();
  std::shared_ptr<Abstract> ToReal();
  std::shared_ptr<Abstract> Succ();
  std::shared_ptr<Abstract> Predecessor();
  std::shared_ptr<Abstract> Exponentiation();
  std::shared_ptr<Abstract> RealDivision();
  std::shared_ptr<Abstract> RExponentiation();

  /* 5.4 Arithmetical Expressions (continued) */
  std::shared_ptr<Abstract> Max();
  std::shared_ptr<Abstract> Min();
  std::shared_ptr<Abstract> RMax();
  std::shared_ptr<Abstract> RMin();
  std::shared_ptr<Abstract> Cardinals();
  std::shared_ptr<Abstract> Card(const BType &);
  std::shared_ptr<Abstract> GeneralizedSum();
  std::shared_ptr<Abstract> GeneralizedProduct();
  std::shared_ptr<Abstract> RGeneralizedSum();
  std::shared_ptr<Abstract> RGeneralizedProduct();

  /* 5.5 Expression of Couples */
  std::shared_ptr<Abstract> Maplet();

  /* 5.6 Building Sets */
  std::shared_ptr<Abstract> EmptySet(const BType &);
  std::shared_ptr<Abstract> Integer();
  std::shared_ptr<Abstract> Natural();
  std::shared_ptr<Abstract> Natural1();
  std::shared_ptr<Abstract> Nat();
  std::shared_ptr<Abstract> Nat1();
  std::shared_ptr<Abstract> Real();
  std::shared_ptr<Abstract> Bool();
  std::shared_ptr<Abstract> Int();

  /* 5.7 Set List Expressions */
  std::shared_ptr<Abstract> PowerSet(const BType &);
  std::shared_ptr<Abstract> PowerSet1(const BType &);
  std::shared_ptr<Abstract> Interval();
  std::shared_ptr<Abstract> ExpressionCartesianProduct(const BType &,
                                                       const BType &);
  std::shared_ptr<Abstract> Set(const BType &);
  std::shared_ptr<Abstract> Fin(const BType &);
  std::shared_ptr<Abstract> Fin1(const BType &);

  /* 5.8 Set List Expressions (continued) */
  std::shared_ptr<Abstract> Difference(const BType &);
  std::shared_ptr<Abstract> Union(const BType &);
  std::shared_ptr<Abstract> Intersection(const BType &);
  std::shared_ptr<Abstract> GeneralizedUnion(const BType &);
  std::shared_ptr<Abstract> GeneralizedIntersection(const BType &);
  std::shared_ptr<Abstract> Quantified_Union(const BType &, const BType &);
  std::shared_ptr<Abstract> Quantified_Intersection(const BType &,
                                                    const BType &);

  /* 5.10 Set of Relations */
  std::shared_ptr<Abstract> Relation(const BType &, const BType &);
  std::shared_ptr<Abstract> Total_Relation(const BType &, const BType &);

  /* 5.11 Expressions of Relations */
  std::shared_ptr<Abstract> Identity(const BType &);
  std::shared_ptr<Abstract> Reverse(const BType &, const BType &);
  std::shared_ptr<Abstract> Prj1(const BType &, const BType &);
  std::shared_ptr<Abstract> Prj2(const BType &, const BType &);
  std::shared_ptr<Abstract> Composition(const BType &, const BType &,
                                        const BType &);
  std::shared_ptr<Abstract> Direct_Product(const BType &, const BType &,
                                           const BType &);

  std::shared_ptr<Abstract> Parallel_Product(const BType &, const BType &,
                                             const BType &, const BType &);

  /* 5.12 Expressions of Relations */
  std::shared_ptr<Abstract> Iteration(const BType &);
  std::shared_ptr<Abstract> Closure(const BType &);
  std::shared_ptr<Abstract> Closure1(const BType &);

  /* 5.13 Expressions of Relations */
  std::shared_ptr<Abstract> Domain(const BType &, const BType &);
  std::shared_ptr<Abstract> Range(const BType &, const BType &);
  std::shared_ptr<Abstract> Image(const BType &, const BType &);

  /* 5.14 Expressions of Relations */
  std::shared_ptr<Abstract> Restriction_Domain(const BType &, const BType &);
  std::shared_ptr<Abstract> Subtraction_Domain(const BType &, const BType &);
  std::shared_ptr<Abstract> Restriction_Range(const BType &, const BType &);
  std::shared_ptr<Abstract> Subtraction_Range(const BType &, const BType &);
  std::shared_ptr<Abstract> Overwrite(const BType &, const BType &);

  /* 5.15 Sets of Functions */
  std::shared_ptr<Abstract> Injection(const BType &, const BType &);
  std::shared_ptr<Abstract> Surjection(const BType &, const BType &);
  std::shared_ptr<Abstract> Bijection(const BType &, const BType &);
  std::shared_ptr<Abstract> Function(const BType &, const BType &);
  std::shared_ptr<Abstract> Total_Function(const BType &, const BType &);
  std::shared_ptr<Abstract> Partial_Function(const BType &, const BType &);
  std::shared_ptr<Abstract> Partial_Injection(const BType &, const BType &);
  std::shared_ptr<Abstract> Total_Injection(const BType &, const BType &);
  std::shared_ptr<Abstract> Partial_Surjection(const BType &, const BType &);
  std::shared_ptr<Abstract> Total_Surjection(const BType &, const BType &);
  std::shared_ptr<Abstract> Total_Bijection(const BType &, const BType &);

  /* 5.16 Expressions of Functions */
  std::shared_ptr<Abstract> Evaluation(const BType &, const BType &);
  std::shared_ptr<Abstract> Transformed_Into_Function(const BType &,
                                                      const BType &);
  std::shared_ptr<Abstract> Transformed_Into_Relation(const BType &,
                                                      const BType &);
  std::shared_ptr<Abstract> Lambda(const BType &, const BType &);

  /* 5.17 Set of Sequences */
  std::shared_ptr<Abstract> Seq(const BType &);
  std::shared_ptr<Abstract> Seq1(const BType &);
  std::shared_ptr<Abstract> Injective_Seq(const BType &);
  std::shared_ptr<Abstract> Injective_Seq1(const BType &);
  std::shared_ptr<Abstract> Perm(const BType &);
  std::shared_ptr<Abstract> EmptySeq(const BType &);

  /* 5.18 Expressions of Sequences */
  std::shared_ptr<Abstract> Size(const BType &);
  std::shared_ptr<Abstract> First(const BType &);
  std::shared_ptr<Abstract> Last(const BType &);
  std::shared_ptr<Abstract> Front(const BType &);
  std::shared_ptr<Abstract> Tail(const BType &);
  std::shared_ptr<Abstract> Rev(const BType &);

  /* 5.19 Expressions of Sequences */
  std::shared_ptr<Abstract> Concatenation(const BType &);
  std::shared_ptr<Abstract> Insert_In_Front(const BType &);
  std::shared_ptr<Abstract> Insert_At_Tail(const BType &);
  std::shared_ptr<Abstract> Restrict_In_Front(const BType &);
  std::shared_ptr<Abstract> Restrict_At_Tail(const BType &);
  std::shared_ptr<Abstract> General_Concatenation(const BType &);

  class Exception : public std::exception {
   public:
    Exception(const std::string &msg) : msg{msg} {}
    const char *what() const noexcept override { return msg.c_str(); }

   private:
    std::string msg;
  };

 private:
  struct BTypeHash {
    size_t operator()(const std::shared_ptr<const BType> &t) const {
      size_t result = t->hash_combine(0);
      return result;
    }
  };
  struct BinaryBTypeHash {
    size_t operator()(const std::pair<std::shared_ptr<const BType>,
                                      std::shared_ptr<const BType>> &p) const {
      return p.second->hash_combine(p.first->hash_combine(0));
    }
  };
  struct TernaryBTypeHash {
    size_t operator()(const std::pair<std::pair<std::shared_ptr<const BType>,
                                                std::shared_ptr<const BType>>,
                                      std::shared_ptr<const BType>> &p) const {
      return p.second->hash_combine(
          p.first.second->hash_combine(p.first.first->hash_combine(0)));
    }
  };
  struct NaryBTypeHash {
    size_t operator()(
        const std::pair<std::pair<std::pair<std::shared_ptr<const BType>,
                                            std::shared_ptr<const BType>>,
                                  std::shared_ptr<const BType>>,
                        std::shared_ptr<const BType>> &p) const {
      return p.second->hash_combine(
          p.first.second->hash_combine(p.first.first.second->hash_combine(
              p.first.first.first->hash_combine(0))));
    }
  };
  struct DataHash {
    size_t operator()(const std::shared_ptr<const struct Data> &dt) const {
      return dt->m_name->hash_combine(0);
    }
  };

  /* Type */
  std::vector<std::shared_ptr<BConstruct::Abstract>> m_index;
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Type::Type>, BTypeHash>
      m_Types;

  std::shared_ptr<BConstruct::Type::PowerSet> m_PowerSet;
  std::shared_ptr<BConstruct::Type::CartesianProduct> m_CartesianProduct;

  /* Predicate */

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Predicate::SetMembership>,
                     BTypeHash>
      m_SetMemberships;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Predicate::Equality>,
                     BTypeHash>
      m_Equalities;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Predicate::Inclusion>,
                     BTypeHash>
      m_Inclusions;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Predicate::StrictInclusion>,
                     BTypeHash>
      m_StrictInclusions;

  std::shared_ptr<BConstruct::Predicate::NumberComparison> m_NumberComparison;

  /* 5.1 Primary Expressions */
  std::unordered_map<std::shared_ptr<const struct Data>,
                     std::shared_ptr<BConstruct::Expression::Data>, DataHash>
      m_data;

  /* 5.2 Boolean Expressions */
  std::shared_ptr<BConstruct::Expression::BooleanExpression>
      m_BooleanExpression;

  /* 5.3 Arithmetical Expressions */
  std::shared_ptr<BConstruct::Expression::Maxint> m_Maxint;
  std::shared_ptr<BConstruct::Expression::Minint> m_Minint;
  std::shared_ptr<BConstruct::Expression::Addition> m_Addition;
  std::shared_ptr<BConstruct::Expression::Subtraction> m_Subtraction;
  std::shared_ptr<BConstruct::Expression::Multiplication> m_Multiplication;
  std::shared_ptr<BConstruct::Expression::IntegerDivision> m_IntegerDivision;
  std::shared_ptr<BConstruct::Expression::Floor> m_Floor;
  std::shared_ptr<BConstruct::Expression::Ceiling> m_Ceiling;
  std::shared_ptr<BConstruct::Expression::ToReal> m_ToReal;
  std::shared_ptr<BConstruct::Expression::Succ> m_Succ;
  std::shared_ptr<BConstruct::Expression::Predecessor> m_Predecessor;
  std::shared_ptr<BConstruct::Expression::Exponentiation> m_Exponentiation;
  std::shared_ptr<BConstruct::Expression::RealDivision> m_RealDivision;
  std::shared_ptr<BConstruct::Expression::RExponentiation> m_RExponentiation;

  /* 5.4 Arithmetical Expressions (continued) */
  std::shared_ptr<BConstruct::Expression::Max> m_Max;
  std::shared_ptr<BConstruct::Expression::Min> m_Min;
  std::shared_ptr<BConstruct::Expression::RMax> m_RMax;
  std::shared_ptr<BConstruct::Expression::RMin> m_RMin;
  std::shared_ptr<BConstruct::Expression::Cardinals> m_Cardinals;
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Card>, BTypeHash>
      m_Cards;
  std::shared_ptr<BConstruct::Expression::GeneralizedSum> m_GeneralizedSum;
  std::shared_ptr<BConstruct::Expression::GeneralizedProduct>
      m_GeneralizedProduct;
  std::shared_ptr<BConstruct::Expression::RGeneralizedSum> m_RGeneralizedSum;
  std::shared_ptr<BConstruct::Expression::RGeneralizedProduct>
      m_RGeneralizedProduct;

  /* 5.5 Expression of Couples */
  std::shared_ptr<BConstruct::Expression::Maplet> m_Maplet;

  /* 5.6 Building Sets */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::EmptySet>,
                     BTypeHash>
      m_EmptySets;
  std::shared_ptr<BConstruct::Expression::Integer> m_Integer;
  std::shared_ptr<BConstruct::Expression::Natural> m_Natural;
  std::shared_ptr<BConstruct::Expression::Natural1> m_Natural1;
  std::shared_ptr<BConstruct::Expression::Nat> m_Nat;
  std::shared_ptr<BConstruct::Expression::Nat1> m_Nat1;
  std::shared_ptr<BConstruct::Expression::Real> m_Real;
  std::shared_ptr<BConstruct::Expression::Bool> m_Bool;
  std::shared_ptr<BConstruct::Expression::Int> m_Int;

  /* 5.7 Set List Expressions */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::PowerSet>,
                     BTypeHash>
      m_PowerSets;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::PowerSet1>,
                     BTypeHash>
      m_PowerSet1s;

  std::shared_ptr<BConstruct::Expression::Interval> m_Interval;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::CartesianProduct>,
      BinaryBTypeHash>
      m_ExpressionCartesianProducts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Set>, BTypeHash>
      m_Sets;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Fin>, BTypeHash>
      m_Fins;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Fin1>, BTypeHash>
      m_Fin1s;

  /* 5.8 Set List Expressions (continued) */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Difference>,
                     BTypeHash>
      m_Differences;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Union>, BTypeHash>
      m_Unions;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Intersection>,
                     BTypeHash>
      m_Intersections;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::GeneralizedUnion>,
                     BTypeHash>
      m_GeneralizedUnions;

  std::unordered_map<
      std::shared_ptr<const BType>,
      std::shared_ptr<BConstruct::Expression::GeneralizedIntersection>,
      BTypeHash>
      m_GeneralizedIntersections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Quantified_Union>,
      BinaryBTypeHash>
      m_Quantified_Unions;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Quantified_Intersection>,
      BinaryBTypeHash>
      m_Quantified_Intersections;

  /* 5.10 Set of Relations */
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Relation>, BinaryBTypeHash>
      m_Relations;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Total_Relation>, BinaryBTypeHash>
      m_Total_Relations;

  /* 5.11 Expressions of Relations */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Identity>,
                     BTypeHash>
      m_Identitys;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Reverse>, BinaryBTypeHash>
      m_Reverses;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Prj1>, BinaryBTypeHash>
      m_Prj1s;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Prj2>, BinaryBTypeHash>
      m_Prj2s;

  std::unordered_map<
      std::pair<
          std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
          std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Composition>, TernaryBTypeHash>
      m_Compositions;

  std::unordered_map<
      std::pair<
          std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
          std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Direct_Product>, TernaryBTypeHash>
      m_Direct_Products;

  std::unordered_map<
      std::pair<std::pair<std::pair<std::shared_ptr<const BType>,
                                    std::shared_ptr<const BType>>,
                          std::shared_ptr<const BType>>,
                std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Parallel_Product>, NaryBTypeHash>
      m_Parallel_Products;

  /* 5.12 Expressions of Relations */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Iteration>,
                     BTypeHash>
      m_Iterations;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Closure>,
                     BTypeHash>
      m_Closures;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Closure1>,
                     BTypeHash>
      m_Closure1s;

  /* 5.13 Expressions of Relations */
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Domain>, BinaryBTypeHash>
      m_Domains;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Range>, BinaryBTypeHash>
      m_Ranges;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Image>, BinaryBTypeHash>
      m_Images;

  /* 5.14 Expressions of Relations */
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Restriction_Domain>,
      BinaryBTypeHash>
      m_Restriction_Domains;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Subtraction_Domain>,
      BinaryBTypeHash>
      m_Subtraction_Domains;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Restriction_Range>,
      BinaryBTypeHash>
      m_Restriction_Ranges;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Subtraction_Range>,
      BinaryBTypeHash>
      m_Subtraction_Ranges;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Overwrite>, BinaryBTypeHash>
      m_Overwrites;

  /* 5.15 Sets of Functions */
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Injection>, BinaryBTypeHash>
      m_Injections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Surjection>, BinaryBTypeHash>
      m_Surjections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Bijection>, BinaryBTypeHash>
      m_Bijections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Function>, BinaryBTypeHash>
      m_Functions;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Total_Function>, BinaryBTypeHash>
      m_Total_Functions;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Partial_Function>,
      BinaryBTypeHash>
      m_Partial_Functions;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Partial_Injection>,
      BinaryBTypeHash>
      m_Partial_Injections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Total_Injection>, BinaryBTypeHash>
      m_Total_Injections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Partial_Surjection>,
      BinaryBTypeHash>
      m_Partial_Surjections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Total_Surjection>,
      BinaryBTypeHash>
      m_Total_Surjections;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Total_Bijection>, BinaryBTypeHash>
      m_Total_Bijections;

  /* 5.16 Expressions of Functions */
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Evaluation>, BinaryBTypeHash>
      m_Evaluations;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Transformed_Into_Function>,
      BinaryBTypeHash>
      m_Transformed_Into_Functions;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Transformed_Into_Relation>,
      BinaryBTypeHash>
      m_Transformed_Into_Relations;

  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::Lambda>, BinaryBTypeHash>
      m_Lambdas;

  /* 5.17 Set of Sequences */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Seq>, BTypeHash>
      m_Seqs;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Seq1>, BTypeHash>
      m_Seq1s;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Injective_Seq>,
                     BTypeHash>
      m_Injective_Seqs;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Injective_Seq1>,
                     BTypeHash>
      m_Injective_Seq1s;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Perm>, BTypeHash>
      m_Perms;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::EmptySeq>,
                     BTypeHash>
      m_EmptySeqs;

  /* 5.18 Expressions of Sequences */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Size>, BTypeHash>
      m_Sizes;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::First>, BTypeHash>
      m_Firsts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Last>, BTypeHash>
      m_Lasts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Front>, BTypeHash>
      m_Fronts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Tail>, BTypeHash>
      m_Tails;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Rev>, BTypeHash>
      m_Revs;

  /* 5.19 Expressions of Sequences */
  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Concatenation>,
                     BTypeHash>
      m_Concatenations;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Insert_In_Front>,
                     BTypeHash>
      m_Insert_In_Fronts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Insert_At_Tail>,
                     BTypeHash>
      m_Insert_At_Tails;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Restrict_In_Front>,
                     BTypeHash>
      m_Restrict_In_Fronts;

  std::unordered_map<std::shared_ptr<const BType>,
                     std::shared_ptr<BConstruct::Expression::Restrict_At_Tail>,
                     BTypeHash>
      m_Restrict_At_Tails;

  std::unordered_map<
      std::shared_ptr<const BType>,
      std::shared_ptr<BConstruct::Expression::General_Concatenation>, BTypeHash>
      m_General_Concatenations;

  void index(std::shared_ptr<Abstract>);

 private:
  template <typename T> std::shared_ptr<Abstract> get(std::shared_ptr<T> &m);

  template <typename T>
  std::shared_ptr<Abstract> get(
      std::unordered_map<std::shared_ptr<const BType>, std::shared_ptr<T>,
                         BTypeHash> &m,
      const BType &t);

  template <typename T>
  std::shared_ptr<Abstract> get(
      std::unordered_map<
          std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
          std::shared_ptr<T>, BinaryBTypeHash> &m,
      const BType &tl, const BType &tr);

  template <typename T>
  std::shared_ptr<Abstract> get(
      std::unordered_map<std::pair<std::pair<std::shared_ptr<const BType>,
                                             std::shared_ptr<const BType>>,
                                   std::shared_ptr<const BType>>,
                         std::shared_ptr<T>, TernaryBTypeHash> &m,
      const BType &fst, const BType &snd, const BType &thd);

  template <typename T>
  std::shared_ptr<Abstract> get(
      std::unordered_map<
          std::pair<std::pair<std::pair<std::shared_ptr<const BType>,
                                        std::shared_ptr<const BType>>,
                              std::shared_ptr<const BType>>,
                    std::shared_ptr<const BType>>,
          std::shared_ptr<T>, NaryBTypeHash> &m,
      const BType &fst, const BType &snd, const BType &thd, const BType &fth);

  std::shared_ptr<Abstract> get(const struct Data &t);
};

class Abstract : public std::enable_shared_from_this<Abstract> {
 public:
  Abstract()
      : m_index(0ul), m_script(NoScript), m_prerequisites(NoPrerequisites) {}
  virtual ~Abstract() = default;

  Abstract &operator=(const Abstract &) = delete;
  Abstract(const Abstract &) = delete;
  Abstract(Abstract &&) = delete;

  virtual std::string script() const { return m_script; }
  virtual std::set<std::shared_ptr<Abstract>> prerequisites() const {
    return m_prerequisites;
  }

  static int compare(const Abstract &v1, const Abstract &v2) {
    size_t hash1 = v1.hash_combine(0);
    size_t hash2 = v2.hash_combine(0);
    if (hash1 < hash2) return -1;
    if (hash1 > hash2) return 1;
    return 0;
  }
  inline bool operator==(const Abstract &other) const {
    return compare(*this, other) == 0;
  }
  inline bool operator!=(const Abstract &other) const {
    return compare(*this, other) != 0;
  }
  inline bool operator<(const Abstract &other) const {
    return compare(*this, other) < 0;
  }
  inline bool operator>(const Abstract &other) const {
    return compare(*this, other) > 0;
  }
  inline bool operator<=(const Abstract &other) const {
    return compare(*this, other) <= 0;
  }
  inline bool operator>=(const Abstract &other) const {
    return compare(*this, other) >= 0;
  }

  size_t hash_combine(size_t seed) const;
  friend class Factory;

  size_t hash() const {
    if (!m_hash_valid) {
      m_hash = hash_special();
      m_hash_valid = true;
    }
    return m_hash;
  }
  virtual size_t hash_special() const = 0;
  virtual std::string to_string() const = 0;

  std::uint64_t index() const { return m_index; }

 private:
  mutable bool m_hash_valid = false;
  mutable size_t m_hash;

 protected:
  std::uint64_t m_index;
  std::string m_script;
  std::set<std::shared_ptr<Abstract>> m_prerequisites;
  std::string m_debug_string = "B Construct";

 protected:
  static const std::string NoScript;
  static const std::set<std::shared_ptr<Abstract>> NoPrerequisites;
};

class Uniform : public Abstract {
 public:
  virtual ~Uniform() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::string_view m_label;
};

class UnaryBType : public Abstract {
 public:
  UnaryBType(const BType &t) : m_type(std::make_shared<const BType>(t)) {}
  virtual ~UnaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::string_view m_label;
  std::shared_ptr<const BType> m_type;
};

class BinaryBType : public Abstract {
 public:
  BinaryBType(const BType &t1, const BType &t2)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)) {}
  virtual ~BinaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::string_view m_label;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
};

class TernaryBType : public Abstract {
 public:
  TernaryBType(const BType &t1, const BType &t2, const BType &t3)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)),
        m_type3(std::make_shared<const BType>(t3)) {}
  virtual ~TernaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::string_view m_label;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
  std::shared_ptr<const BType> m_type3;
};

class NaryBType : public Abstract {
 public:
  NaryBType(const BType &t1, const BType &t2, const BType &t3, const BType &t4)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)),
        m_type3(std::make_shared<const BType>(t3)),
        m_type4(std::make_shared<const BType>(t4)) {}
  virtual ~NaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::string_view m_label;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
  std::shared_ptr<const BType> m_type3;
  std::shared_ptr<const BType> m_type4;
};

/* Classes for the type system constructs */
namespace Type {
class Type : public UnaryBType {
 public:
  explicit Type(const BType &Abstract);
  virtual ~Type() = default;
};

class PowerSet : public Uniform {
 public:
  explicit PowerSet();
  virtual ~PowerSet() = default;
};

class CartesianProduct : public Uniform {
 public:
  explicit CartesianProduct();
  virtual ~CartesianProduct() = default;
};
};  // namespace Type

/* Classes for predicate operators */

namespace Predicate {

class SetMembership : public UnaryBType {
 public:
  /** @param etype type of the elements */
  explicit SetMembership(const BType &etype);
  virtual ~SetMembership() = default;
};

class Equality : public UnaryBType {
 public:
  /** @param atype type of the arguments */
  explicit Equality(const BType &atype);
  virtual ~Equality() = default;
};

class Inclusion : public UnaryBType {
 public:
  /** @param t type of the elements of the compared sets */
  explicit Inclusion(const BType &t);
  virtual ~Inclusion() = default;
};

class StrictInclusion : public UnaryBType {
 public:
  /** @param t type of the elements of the compared sets */
  explicit StrictInclusion(const BType &t);
  virtual ~StrictInclusion() = default;
};

class NumberComparison : public Uniform {
 public:
  explicit NumberComparison() { m_label = "<"; }
  virtual ~NumberComparison() = default;

 private:
};

};  // namespace Predicate

/* 5 Classes for expressions */

namespace Expression {

/* 5.1 Classes for Primary expressions */

class Data : public std::enable_shared_from_this<Data>, public Uniform {
 public:
  explicit Data(const struct ::Data &dt);
  virtual ~Data() = default;

  Data &operator=(const Data &) = delete;
  Data(Data &&) = delete;

  const BType &type() const { return m_type; }

 private:
  const BType &m_type;
  const std::string m_name;
};

/* 5.1 Boolean Expressions */
class BooleanExpression : public Uniform {
 public:
  explicit BooleanExpression() { m_label = "bool()"; }
  virtual ~BooleanExpression() = default;
};

/* 5.3 Arithmetical Expressions */
class Maxint : public Uniform {
 public:
  explicit Maxint();
  virtual ~Maxint() = default;
};

class Minint : public Uniform {
 public:
  explicit Minint();
  virtual ~Minint() = default;
};

class Addition : public Uniform {
 public:
  explicit Addition() { m_label = "+"; }
  virtual ~Addition() = default;
};

class Subtraction : public Uniform {
 public:
  explicit Subtraction() { m_label = "-"; }
  virtual ~Subtraction() = default;
};

class Multiplication : public Uniform {
 public:
  explicit Multiplication() { m_label = "*"; }
  virtual ~Multiplication() = default;
};

class IntegerDivision : public Uniform {
 public:
  explicit IntegerDivision();
  virtual ~IntegerDivision() = default;
};

class Floor : public Uniform {
 public:
  explicit Floor();
  virtual ~Floor() = default;
};

class Ceiling : public Uniform {
 public:
  explicit Ceiling();
  virtual ~Ceiling() = default;
};

class ToReal : public Uniform {
 public:
  explicit ToReal();
  virtual ~ToReal() = default;
};

class Succ : public Uniform {
 public:
  explicit Succ();
  virtual ~Succ() = default;
};

class Predecessor : public Uniform {
 public:
  explicit Predecessor();
  virtual ~Predecessor() = default;
};

class Exponentiation : public Uniform {
 public:
  explicit Exponentiation();
  virtual ~Exponentiation() = default;
};

class RealDivision : public Uniform {
 public:
  explicit RealDivision();
  virtual ~RealDivision() = default;
};

class RExponentiation : public Uniform {
 public:
  explicit RExponentiation();
  virtual ~RExponentiation() = default;
};

/* 5.3 Arithmetical Expressions */
class Max : public Uniform {
 public:
  explicit Max();
  virtual ~Max() = default;
};

class Min : public Uniform {
 public:
  explicit Min();
  virtual ~Min() = default;
};

class RMax : public Uniform {
 public:
  explicit RMax();
  virtual ~RMax() = default;
};

class RMin : public Uniform {
 public:
  explicit RMin();
  virtual ~RMin() = default;
};

class Cardinals : public Uniform {
 public:
  explicit Cardinals();
  virtual ~Cardinals() = default;
};

class Card : public UnaryBType {
 public:
  explicit Card(const BType &t);
  virtual ~Card() = default;
};

class GeneralizedSum : public Uniform {
 public:
  explicit GeneralizedSum();
  virtual ~GeneralizedSum() = default;
};

class GeneralizedProduct : public Uniform {
 public:
  explicit GeneralizedProduct();
  virtual ~GeneralizedProduct() = default;
};

class RGeneralizedSum : public Uniform {
 public:
  explicit RGeneralizedSum();
  virtual ~RGeneralizedSum() = default;
};

class RGeneralizedProduct : public Uniform {
 public:
  explicit RGeneralizedProduct();
  virtual ~RGeneralizedProduct() = default;
};

/* 5.5 Expression of Couples */

class Maplet : public Uniform {
 public:
  explicit Maplet();
  virtual ~Maplet() = default;
};

/* 5.6 Classes for Building Sets */

class EmptySet : public UnaryBType {
 public:
  /** @param t type of the elements of the set (even empty set must be strictly
   * typed) */
  explicit EmptySet(const BType &t);
  virtual ~EmptySet() = default;
};
class Integer : public Uniform {
 public:
  explicit Integer();
  virtual ~Integer() = default;
};

class Natural : public Uniform {
 public:
  explicit Natural();
  virtual ~Natural() = default;
};

class Natural1 : public Uniform {
 public:
  explicit Natural1();
  virtual ~Natural1() = default;
};

class Nat : public Uniform {
 public:
  explicit Nat();
  virtual ~Nat() = default;
};

class Nat1 : public Uniform {
 public:
  explicit Nat1();
  virtual ~Nat1() = default;
};

class Real : public Uniform {
 public:
  explicit Real();
  virtual ~Real() = default;
};

class Bool : public Uniform {
 public:
  explicit Bool();
  virtual ~Bool() = default;
};

class Int : public Uniform {
 public:
  explicit Int();
  virtual ~Int() = default;
};

/* 5.7 Classes for Set List Expressions */

class PowerSet : public UnaryBType {
 public:
  explicit PowerSet(const BType &);
  virtual ~PowerSet() = default;
};

class PowerSet1 : public UnaryBType {
 public:
  explicit PowerSet1(const BType &);
  virtual ~PowerSet1() = default;
};

class Interval : public Uniform {
 public:
  explicit Interval();
  virtual ~Interval() = default;
};

class CartesianProduct : public BinaryBType {
 public:
  explicit CartesianProduct(const BType &lhs, const BType &rhs);
  virtual ~CartesianProduct() = default;
};

class Set : public UnaryBType {
 public:
  explicit Set(const BType &);
  virtual ~Set() = default;
};

class Fin : public UnaryBType {
 public:
  explicit Fin(const BType &);
  virtual ~Fin() = default;
};

class Fin1 : public UnaryBType {
 public:
  explicit Fin1(const BType &);
  virtual ~Fin1() = default;
};

/* 5.8 Classes for Set List Expressions (continued) */

class Difference : public UnaryBType {
 public:
  explicit Difference(const BType &);
  virtual ~Difference() = default;
};

class Union : public UnaryBType {
 public:
  explicit Union(const BType &);
  virtual ~Union() = default;
};

class Intersection : public UnaryBType {
 public:
  explicit Intersection(const BType &);
  virtual ~Intersection() = default;
};

class GeneralizedUnion : public UnaryBType {
 public:
  explicit GeneralizedUnion(const BType &);
  virtual ~GeneralizedUnion() = default;
};

class GeneralizedIntersection : public UnaryBType {
 public:
  explicit GeneralizedIntersection(const BType &);
  virtual ~GeneralizedIntersection() = default;
};

class Quantified_Union : public BinaryBType {
 public:
  explicit Quantified_Union(const BType &, const BType &);
  virtual ~Quantified_Union() = default;
};

class Quantified_Intersection : public BinaryBType {
 public:
  explicit Quantified_Intersection(const BType &, const BType &);
  virtual ~Quantified_Intersection() = default;
};

/* 5.10 Set of Relations  */

class Relation : public BinaryBType {
 public:
  explicit Relation(const BType &, const BType &);
  virtual ~Relation() = default;
};

class Total_Relation : public BinaryBType {
 public:
  explicit Total_Relation(const BType &, const BType &);
  virtual ~Total_Relation() = default;
};

/* 5.11 Expressions of Relations */

class Identity : public UnaryBType {
 public:
  explicit Identity(const BType &);
  virtual ~Identity() = default;
};

class Reverse : public BinaryBType {
 public:
  explicit Reverse(const BType &, const BType &);
  virtual ~Reverse() = default;
};

class Prj1 : public BinaryBType {
 public:
  explicit Prj1(const BType &, const BType &);
  virtual ~Prj1() = default;
};

class Prj2 : public BinaryBType {
 public:
  explicit Prj2(const BType &, const BType &);
  virtual ~Prj2() = default;
};

class Composition : public TernaryBType {
 public:
  explicit Composition(const BType &, const BType &, const BType &);
  virtual ~Composition() = default;
};

class Direct_Product : public TernaryBType {
 public:
  explicit Direct_Product(const BType &, const BType &, const BType &);
  virtual ~Direct_Product() = default;
};

class Parallel_Product : public NaryBType {
 public:
  explicit Parallel_Product(const BType &, const BType &, const BType &,
                            const BType &);
  virtual ~Parallel_Product() = default;
};

/* 5.12 Expressions of Relations */

class Iteration : public UnaryBType {
 public:
  explicit Iteration(const BType &);
  virtual ~Iteration() = default;
};

class Closure : public UnaryBType {
 public:
  explicit Closure(const BType &);
  virtual ~Closure() = default;
};

class Closure1 : public UnaryBType {
 public:
  explicit Closure1(const BType &);
  virtual ~Closure1() = default;
};

/* 5.13 Expressions of Relations */

class Domain : public BinaryBType {
 public:
  explicit Domain(const BType &, const BType &);
  virtual ~Domain() = default;
};

class Range : public BinaryBType {
 public:
  explicit Range(const BType &, const BType &);
  virtual ~Range() = default;
};

class Image : public BinaryBType {
 public:
  explicit Image(const BType &, const BType &);
  virtual ~Image() = default;
};

/* 5.14 Expressions of Relations */

class Restriction_Domain : public BinaryBType {
 public:
  explicit Restriction_Domain(const BType &, const BType &);
  virtual ~Restriction_Domain() = default;
};

class Subtraction_Domain : public BinaryBType {
 public:
  explicit Subtraction_Domain(const BType &, const BType &);
  virtual ~Subtraction_Domain() = default;
};

class Restriction_Range : public BinaryBType {
 public:
  explicit Restriction_Range(const BType &, const BType &);
  virtual ~Restriction_Range() = default;
};

class Subtraction_Range : public BinaryBType {
 public:
  explicit Subtraction_Range(const BType &, const BType &);
  virtual ~Subtraction_Range() = default;
};

class Overwrite : public BinaryBType {
 public:
  explicit Overwrite(const BType &, const BType &);
  virtual ~Overwrite() = default;
};

/* 5.15 Sets of Functions */

class Injection : public BinaryBType {
 public:
  explicit Injection(const BType &, const BType &);
  virtual ~Injection() = default;
};

class Surjection : public BinaryBType {
 public:
  explicit Surjection(const BType &, const BType &);
  virtual ~Surjection() = default;
};

class Bijection : public BinaryBType {
 public:
  explicit Bijection(const BType &, const BType &);
  virtual ~Bijection() = default;
};

class Function : public BinaryBType {
 public:
  explicit Function(const BType &, const BType &);
  virtual ~Function() = default;
};

class Partial_Function : public BinaryBType {
 public:
  explicit Partial_Function(const BType &, const BType &);
  virtual ~Partial_Function() = default;
};

class Total_Function : public BinaryBType {
 public:
  explicit Total_Function(const BType &, const BType &);
  virtual ~Total_Function() = default;
};

class Partial_Injection : public BinaryBType {
 public:
  explicit Partial_Injection(const BType &, const BType &);
  virtual ~Partial_Injection() = default;
};

class Total_Injection : public BinaryBType {
 public:
  explicit Total_Injection(const BType &, const BType &);
  virtual ~Total_Injection() = default;
};

class Partial_Surjection : public BinaryBType {
 public:
  explicit Partial_Surjection(const BType &, const BType &);
  virtual ~Partial_Surjection() = default;
};

class Total_Surjection : public BinaryBType {
 public:
  explicit Total_Surjection(const BType &, const BType &);
  virtual ~Total_Surjection() = default;
};

class Total_Bijection : public BinaryBType {
 public:
  explicit Total_Bijection(const BType &, const BType &);
  virtual ~Total_Bijection() = default;
};

/* 5.16 Expressions of Functions */

class Evaluation : public BinaryBType {
 public:
  explicit Evaluation(const BType &, const BType &);
  virtual ~Evaluation() = default;
};

class Transformed_Into_Function : public BinaryBType {
 public:
  explicit Transformed_Into_Function(const BType &, const BType &);
  virtual ~Transformed_Into_Function() = default;
};

class Transformed_Into_Relation : public BinaryBType {
 public:
  explicit Transformed_Into_Relation(const BType &, const BType &);
  virtual ~Transformed_Into_Relation() = default;
};

class Lambda : public BinaryBType {
 public:
  explicit Lambda(const BType &, const BType &);
  virtual ~Lambda() = default;
};

/* 5.17 Set of Sequences */

class Seq : public UnaryBType {
 public:
  explicit Seq(const BType &);
  virtual ~Seq() = default;
};

class Seq1 : public UnaryBType {
 public:
  explicit Seq1(const BType &);
  virtual ~Seq1() = default;
};

class Injective_Seq : public UnaryBType {
 public:
  explicit Injective_Seq(const BType &);
  virtual ~Injective_Seq() = default;
};

class Injective_Seq1 : public UnaryBType {
 public:
  explicit Injective_Seq1(const BType &);
  virtual ~Injective_Seq1() = default;
};

class Perm : public UnaryBType {
 public:
  explicit Perm(const BType &);
  virtual ~Perm() = default;
};

class EmptySeq : public UnaryBType {
 public:
  explicit EmptySeq(const BType &);
  virtual ~EmptySeq() = default;
};

/* 5.18 Expressions of Sequences */

class Size : public UnaryBType {
 public:
  explicit Size(const BType &);
  virtual ~Size() = default;
};

class First : public UnaryBType {
 public:
  explicit First(const BType &);
  virtual ~First() = default;
};

class Last : public UnaryBType {
 public:
  explicit Last(const BType &);
  virtual ~Last() = default;
};

class Front : public UnaryBType {
 public:
  explicit Front(const BType &);
  virtual ~Front() = default;
};

class Tail : public UnaryBType {
 public:
  explicit Tail(const BType &);
  virtual ~Tail() = default;
};

class Rev : public UnaryBType {
 public:
  explicit Rev(const BType &);
  virtual ~Rev() = default;
};

/* 5.19 Expressions of Sequences */

class Concatenation : public UnaryBType {
 public:
  explicit Concatenation(const BType &);
  virtual ~Concatenation() = default;
};

class Insert_In_Front : public UnaryBType {
 public:
  explicit Insert_In_Front(const BType &);
  virtual ~Insert_In_Front() = default;
};

class Insert_At_Tail : public UnaryBType {
 public:
  explicit Insert_At_Tail(const BType &);
  virtual ~Insert_At_Tail() = default;
};

class Restrict_In_Front : public UnaryBType {
 public:
  explicit Restrict_In_Front(const BType &);
  virtual ~Restrict_In_Front() = default;
};

class Restrict_At_Tail : public UnaryBType {
 public:
  explicit Restrict_At_Tail(const BType &);
  virtual ~Restrict_At_Tail() = default;
};

class General_Concatenation : public UnaryBType {
 public:
  explicit General_Concatenation(const BType &);
  virtual ~General_Concatenation() = default;
};

};  // namespace Expression

// Custom hash function
struct BConstructPtrHash {
  std::size_t operator()(const std::shared_ptr<Abstract> &key) const {
    return std::hash<uint64_t>()(key.get()->index());
  }
};

// Custom equality function
struct BConstructPtrEqual {
  bool operator()(const std::shared_ptr<Abstract> &lhs,
                  const std::shared_ptr<Abstract> &rhs) const {
    return *lhs.get() == *rhs.get();
  }
};

using Context = std::unordered_set<std::shared_ptr<Abstract>, BConstructPtrHash,
                                   BConstructPtrEqual>;
};  // namespace BConstruct

#endif  // BBIT_H
