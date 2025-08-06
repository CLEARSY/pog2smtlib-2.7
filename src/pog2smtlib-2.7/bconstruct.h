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
class Floor;
class Ceiling;
class ToReal;

/* 5.4 Arithmetical Expressions (continued) */

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
class CartesianProduct;
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
  
  /* 5.4 Arithmetical Expressions (continued) */
  
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
  std::shared_ptr<Abstract> ExpressionCartesianProduct(const BType &,
                                                       const BType &);

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

  /* 5.3 Arithmetical Expressions I */
  std::shared_ptr<BConstruct::Expression::Maxint> m_Maxint;
  std::shared_ptr<BConstruct::Expression::Minint> m_Minint;
  std::shared_ptr<BConstruct::Expression::Addition> m_Addition;
  std::shared_ptr<BConstruct::Expression::Subtraction> m_Subtraction;
  std::shared_ptr<BConstruct::Expression::Multiplication> m_Multiplication;
  std::shared_ptr<BConstruct::Expression::IntegerDivision> m_IntegerDivision;
  std::shared_ptr<BConstruct::Expression::Floor> m_Floor;
  std::shared_ptr<BConstruct::Expression::Ceiling> m_Ceiling;
  std::shared_ptr<BConstruct::Expression::ToReal> m_ToReal;

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
      
  std::unordered_map<
      std::pair<std::shared_ptr<const BType>, std::shared_ptr<const BType>>,
      std::shared_ptr<BConstruct::Expression::CartesianProduct>,
      BinaryBTypeHash>
      m_ExpressionCartesianProducts;

  void index(std::shared_ptr<Abstract>);

 private:
  template <typename T>
  std::shared_ptr<Abstract> get(std::shared_ptr<T> &m);

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

class CartesianProduct : public BinaryBType {
 public:
  explicit CartesianProduct(const BType &lhs, const BType &rhs);
  virtual ~CartesianProduct() = default;
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
