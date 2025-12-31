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

#include <array>
#include <memory>
#include <set>
#include <string>
#include <variant>

#include "btype-utils.h"
#include "btype.h"
#include "signature.h"

/**
 * @details
 * Polymorphic B constructs need to be monomorphized, i.e., sort parameters are
 * instantiated. For instance, Cartesian product operator has two sort
 * parameters: the sort of the domain and the sort of the range. The number of
 * sort parameters are 0, 1, 2, 3, 4.
 */
namespace BConstruct {
class Uniform; /** @brief abstract class for operators with 0 sort parameters */
class UnaryBType; /** @brief abstract class for operators with 1 sort parameters
                   */
class BinaryBType;     /** @brief abstract class for operators with 2 sort
                          parameters */
class TernaryBType;    /** @brief abstract class for operators with 3 sort
                          parameters */
class QuaternaryBType; /** @brief abstract class for operators with 4 sort
                          parameters */
}  // namespace BConstruct

/**
 * @brief BinaryBType is an alias of a pair of B types.
 * @details Useful to index B operators with two sort parameters.
 */
using BinaryBType =
    std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>;

struct BinaryBTypeHash {
  size_t operator()(const BinaryBType &p) const;
};
struct BinaryBTypeEqual {
  bool operator()(const BinaryBType &lhs, const BinaryBType &rhs) const;
};

/**
 * @brief TernaryBType is an alias of a triplet of B types.
 * @details Useful to index B operators with three sort parameters.
 */
using TernaryBType = std::array<std::shared_ptr<const BType>, 3>;
struct TernaryBTypeHash {
  size_t operator()(const TernaryBType &p) const;
};
struct TernaryBTypeEqual {
  bool operator()(const TernaryBType &lhs, const TernaryBType &rhs) const;
};

/**
 * @brief QuadrupleBType is an alias of a quadruplet of B types.
 * @details Useful to index B operators with four sort parameters.
 */
using QuadrupleBType = std::array<std::shared_ptr<const BType>, 4>;
struct QuadrupleBTypeHash {
  size_t operator()(const QuadrupleBType &p) const;
};
struct QuadrupleBTypeEqual {
  bool operator()(const QuadrupleBType &lhs, const QuadrupleBType &rhs) const;
};

template <typename Construct>
using MapUnaryBType =
    std::unordered_map<std::shared_ptr<const BType>, std::shared_ptr<Construct>,
                       BTypeHash, BTypeEqual>;

template <typename Construct>
using MapBinaryBType =
    std::unordered_map<BinaryBType, std::shared_ptr<Construct>, BinaryBTypeHash,
                       BinaryBTypeEqual>;

template <typename Construct>
using MapTernaryBType =
    std::unordered_map<TernaryBType, std::shared_ptr<Construct>,
                       TernaryBTypeHash, TernaryBTypeEqual>;

template <typename Construct>
using MapQuadrupleBType =
    std::unordered_map<QuadrupleBType, std::shared_ptr<Construct>,
                       QuadrupleBTypeHash, QuadrupleBTypeEqual>;

namespace BConstruct {

class Abstract;

struct PtrHash {
  std::size_t operator()(const std::shared_ptr<BConstruct::Abstract> &t) const;
};

struct PtrCompare {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const;
};

struct PtrEqual {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const;
};

using PreRequisites = std::set<std::shared_ptr<Abstract>, PtrCompare>;

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
class String;

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

/* 5.9 Expressions of Records */
class Struct;

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
  std::shared_ptr<Abstract> String();

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

  /* 5.9 Expressions of Records */
  std::shared_ptr<Abstract> Struct(const BType &);

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
  std::vector<std::shared_ptr<BConstruct::Abstract>> m_index;

  /* Predicate */

  std::shared_ptr<BConstruct::Predicate::NumberComparison> m_NumberComparison;

  /* 5.2 Boolean Expressions */
  std::shared_ptr<BConstruct::Expression::BooleanExpression>
      m_BooleanExpression;

  /* 5.3 Arithmetical Expressions */
  std::shared_ptr<BConstruct::Expression::Addition> m_Addition;
  std::shared_ptr<BConstruct::Expression::Subtraction> m_Subtraction;
  std::shared_ptr<BConstruct::Expression::Multiplication> m_Multiplication;

  void index(std::shared_ptr<Abstract>);

 private:
  template <typename T> std::shared_ptr<Abstract> find(std::shared_ptr<T> &m) {
    return m;
  }
  template <typename T>
  std::shared_ptr<Abstract> make(std::shared_ptr<T> &m,
                                 const std::string &script,
                                 const PreRequisites &requisites) {
    if (m != nullptr) {
      return m;
    }
    m = std::make_shared<T>(script, requisites);
    index(m);
    return m;
  }
  template <typename T> std::shared_ptr<Abstract> get(std::shared_ptr<T> &m);

  template <typename T>
  std::shared_ptr<Abstract> find(MapUnaryBType<T> &m, const BType &t) {
    auto it = m.find(std::make_shared<const BType>(t));
    if (it != m.end()) {
      return it->second;
    }
    return nullptr;
  }

  template <typename T>
  std::shared_ptr<Abstract> make(MapUnaryBType<T> &m, const BType &t,
                                 const std::string &script,
                                 const PreRequisites &requisites) {
    std::shared_ptr<const BType> pt = std::make_shared<const BType>(t);
    auto it = m.find(pt);
    if (it != m.end()) {
      return it->second;
    }
    auto construct = std::make_shared<T>(t, script, requisites);
    m[pt] = construct;
    index(construct);
    return construct;
  }

  template <typename T>
  std::shared_ptr<Abstract> find(MapBinaryBType<T> &m, const BType &U,
                                 const BType &V) {
    ::BinaryBType UxV = std::make_pair(std::make_shared<const BType>(U),
                                       std::make_shared<const BType>(V));
    auto it = m.find(UxV);
    if (it != m.end()) {
      return it->second;
    }
    return nullptr;
  }

  template <typename T>
  std::shared_ptr<Abstract> make(MapBinaryBType<T> &m, const BType &U,
                                 const BType &V, const std::string &script,
                                 const PreRequisites &requisites) {
    ::BinaryBType UxV = std::make_pair(std::make_shared<const BType>(U),
                                       std::make_shared<const BType>(V));
    auto it = m.find(UxV);
    if (it != m.end()) {
      return it->second;
    }
    auto construct = std::make_shared<T>(U, V, script, requisites);
    m[UxV] = construct;
    index(construct);
    return construct;
  }

  template <typename T>
  std::shared_ptr<Abstract> find(MapTernaryBType<T> &m, const BType &fst,
                                 const BType &snd, const BType &thd) {
    ::TernaryBType pt = {std::make_shared<const BType>(fst),
                         std::make_shared<const BType>(snd),
                         std::make_shared<const BType>(thd)};
    auto it = m.find(pt);
    if (it != m.end()) {
      return it->second;
    }
    return nullptr;
  }

  template <typename T>
  std::shared_ptr<Abstract> make(MapTernaryBType<T> &m, const BType &fst,
                                 const BType &snd, const BType &thd,
                                 const std::string &script,
                                 const PreRequisites &requisites) {
    ::TernaryBType pt = {std::make_shared<const BType>(fst),
                         std::make_shared<const BType>(snd),
                         std::make_shared<const BType>(thd)};
    auto it = m.find(pt);
    if (it != m.end()) {
      return it->second;
    }
    auto construct = std::make_shared<T>(fst, snd, thd, script, requisites);
    m[pt] = construct;
    index(construct);
    return construct;
  }

  template <typename T>
  std::shared_ptr<Abstract> find(MapQuadrupleBType<T> &m, const BType &U,
                                 const BType &V, const BType &W,
                                 const BType &Z) {
    ::QuadrupleBType pt = {
        std::make_shared<const BType>(U), std::make_shared<const BType>(V),
        std::make_shared<const BType>(W), std::make_shared<const BType>(Z)};
    auto it = m.find(pt);
    if (it != m.end()) {
      return it->second;
    }
    return nullptr;
  }

  template <typename T>
  std::shared_ptr<Abstract> make(MapQuadrupleBType<T> &m, const BType &U,
                                 const BType &V, const BType &W, const BType &Z,
                                 const std::string &script,
                                 const PreRequisites &requisites) {
    ::QuadrupleBType pt = {
        std::make_shared<const BType>(U), std::make_shared<const BType>(V),
        std::make_shared<const BType>(W), std::make_shared<const BType>(Z)};
    auto it = m.find(pt);
    if (it != m.end()) {
      return it->second;
    }
    auto construct = std::make_shared<T>(U, V, W, Z, script, requisites);
    m[pt] = construct;
    index(construct);
    return construct;
  }
};

class Abstract : public std::enable_shared_from_this<Abstract> {
 public:
  Abstract()
      : m_index(0ul), m_script(NoScript), m_prerequisites(NoPrerequisites) {}
  virtual ~Abstract() = default;

  Abstract &operator=(const Abstract &) = delete;
  Abstract(const Abstract &) = delete;
  Abstract(Abstract &&) = delete;

  // Custom equality function
  struct PtrHash {
    std::size_t operator()(const std::shared_ptr<Abstract> &key) const {
      static constexpr bool debug_me = false;
      std::size_t result = std::hash<uint64_t>()(key.get()->index());
      if (debug_me) {
        std::cerr << fmt::format("hash({}) = {}\n", key->to_string(), result);
      }
      return result;
    }
  };

  // Custom equality function
  struct PtrEqual {
    bool operator()(const std::shared_ptr<Abstract> &lhs,
                    const std::shared_ptr<Abstract> &rhs) const {
      static constexpr bool debug_me = false;
      bool result = (*lhs.get() == *rhs.get());
      if (debug_me) {
        std::cerr << fmt::format("({} == {}) = {}\n", lhs->to_string(),
                                 rhs->to_string(), result);
      }
      return result;
    }
  };

  virtual std::string script() const { return m_script; }
  virtual PreRequisites prerequisites() const { return m_prerequisites; }

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
  PreRequisites m_prerequisites;
  std::string m_label;
  std::string m_debug_string = "B Construct";

 protected:
  static const std::string NoScript;
  static const PreRequisites NoPrerequisites;

  Abstract(const std::string script,
           std::set<std::shared_ptr<Abstract>> &requisites,
           const std::string &label, const std::string &debug_string)
      : m_index(0ul),
        m_script(script),
        m_prerequisites(),
        m_label(label),
        m_debug_string(debug_string) {
    m_prerequisites.insert(requisites.begin(), requisites.end());
  }

  Abstract(const std::string script, const PreRequisites &requisites,
           const std::string &label, const std::string &debug_string)
      : m_index(0ul),
        m_script(script),
        m_prerequisites(requisites),
        m_label(label),
        m_debug_string(debug_string) {}
};

class Uniform : public Abstract {
 public:
  virtual ~Uniform() = default;

  virtual std::string to_string() const override;

 protected:
  Uniform() = default;
  Uniform(const std::string script, const PreRequisites &requisites,
          const std::string &label)
      : Abstract(script, requisites, label, label) {}
  size_t hash_special() const override;
};

class UnaryBType : public Abstract {
 public:
  UnaryBType(const BType &T, const std::string script,
             const PreRequisites &requisites, const std::string &label)
      : Abstract(script, requisites,
                 fmt::format("{}_<{}>", label, T.to_string()),
                 fmt::format("{}_<{}>", label, T.to_string())),
        m_type(std::make_shared<const BType>(T)) {}
  virtual ~UnaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::shared_ptr<const BType> m_type;
};

class BinaryBType : public Abstract {
 public:
  BinaryBType(const BType &U, const BType &V, const std::string script,
              const PreRequisites &requisites, const std::string &label)
      : Abstract(
            script, requisites, label,
            fmt::format("{}_<{},{}>", label, U.to_string(), V.to_string())),
        m_type1(std::make_shared<const BType>(U)),
        m_type2(std::make_shared<const BType>(V)) {}
  BinaryBType(const BType &t1, const BType &t2)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)) {}
  virtual ~BinaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
};

class TernaryBType : public Abstract {
 public:
  TernaryBType(const BType &T, const BType &U, const BType &V,
               const std::string script, const PreRequisites &requisites,
               const std::string &label)
      : Abstract(script, requisites, label,
                 fmt::format("{}_<{},{},{}>", label, T.to_string(),
                             U.to_string(), V.to_string())),
        m_type1(std::make_shared<const BType>(T)),
        m_type2(std::make_shared<const BType>(U)),
        m_type3(std::make_shared<const BType>(V)) {}
  TernaryBType(const BType &t1, const BType &t2, const BType &t3)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)),
        m_type3(std::make_shared<const BType>(t3)) {}
  virtual ~TernaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
  std::shared_ptr<const BType> m_type3;
};

class QuaternaryBType : public Abstract {
 public:
  QuaternaryBType(const BType &t1, const BType &t2, const BType &t3,
                  const BType &t4, const std::string script,
                  const PreRequisites &requisites, const std::string &label)
      : Abstract(script, requisites, label,
                 fmt::format("{}_<{},{},{},{}>", label, t1.to_string(),
                             t2.to_string(), t3.to_string(), t4.to_string())),
        m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)),
        m_type3(std::make_shared<const BType>(t3)),
        m_type4(std::make_shared<const BType>(t4)) {}
  QuaternaryBType(const BType &t1, const BType &t2, const BType &t3,
                  const BType &t4)
      : m_type1(std::make_shared<const BType>(t1)),
        m_type2(std::make_shared<const BType>(t2)),
        m_type3(std::make_shared<const BType>(t3)),
        m_type4(std::make_shared<const BType>(t4)) {}
  virtual ~QuaternaryBType() = default;

  virtual std::string to_string() const override;

 protected:
  size_t hash_special() const override;
  std::shared_ptr<const BType> m_type1;
  std::shared_ptr<const BType> m_type2;
  std::shared_ptr<const BType> m_type3;
  std::shared_ptr<const BType> m_type4;
};

/* Classes for predicate operators */

namespace Predicate {

class NumberComparison : public Uniform {
 public:
  explicit NumberComparison() { m_label = "<"; }
  virtual ~NumberComparison() = default;

 private:
};

};  // namespace Predicate

/* 5 Classes for expressions */

namespace Expression {

/* 5.1 Boolean Expressions */
class BooleanExpression : public Uniform {
 public:
  explicit BooleanExpression() { m_label = "bool()"; }
  virtual ~BooleanExpression() = default;
};

/* 5.3 Arithmetical Expressions */
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

};  // namespace Expression

class Abstract;

// Custom equality function
struct BConstructPtrHash {
  std::size_t operator()(const std::shared_ptr<Abstract> &key) const {
    static constexpr bool debug_me = false;
    std::size_t result = std::hash<uint64_t>()(key.get()->index());
    if (debug_me) {
      std::cerr << fmt::format("hash({}) = {}\n", key->to_string(), result);
    }
    return result;
  }
};

// Custom equality function
struct BConstructPtrEqual {
  bool operator()(const std::shared_ptr<Abstract> &lhs,
                  const std::shared_ptr<Abstract> &rhs) const {
    static constexpr bool debug_me = false;
    bool result = (*lhs.get() == *rhs.get());
    if (debug_me) {
      std::cerr << fmt::format("({} == {}) = {}\n", lhs->to_string(),
                               rhs->to_string(), result);
    }
    return result;
  }
};

using Context = std::unordered_set<std::shared_ptr<Abstract>, Abstract::PtrHash,
                                   Abstract::PtrEqual>;
};  // namespace BConstruct

extern std::string toString(const BConstruct::Context &context);

#endif  // BBIT_H
