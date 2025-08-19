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
#ifndef SIGNATURE_H
#define SIGNATURE_H

#include <iostream>
#include <memory>
#include <queue>
#include <string>
#include <unordered_set>
#include <variant>
#include <vector>

#include "btype.h"
#include "expr.h"
#include "pred.h"
#include "symbols.h"

extern bool operator==(const std::vector<std::shared_ptr<BType>> &lhs,
                       const std::vector<std::shared_ptr<BType>> &rhs);

/** @brief The class MonomorphizedOperator represents fully-instantiated
 * versions of polymorphic operators. */
class MonomorphizedOperator {
 private:
  BOperator m_operator;
  std::vector<std::shared_ptr<BType>> m_types;
  mutable bool m_hash_valid = false;
  mutable size_t m_hash = 0;

 public:
  MonomorphizedOperator(const BOperator &op) : m_operator(op), m_types() {}
  MonomorphizedOperator(const BOperator &op, std::shared_ptr<BType> type)
      : m_operator(op), m_types({type}) {}
  MonomorphizedOperator(const BOperator &op, std::shared_ptr<BType> type1,
                        std::shared_ptr<BType> type2)
      : m_operator(op), m_types({type1, type2}) {}
  MonomorphizedOperator(const BOperator &op, std::shared_ptr<BType> type1,
                        std::shared_ptr<BType> type2,
                        std::shared_ptr<BType> type3)
      : m_operator(op), m_types({type1, type2, type3}) {}
  MonomorphizedOperator(const BOperator &op, std::shared_ptr<BType> type1,
                        std::shared_ptr<BType> type2,
                        std::shared_ptr<BType> type3,
                        std::shared_ptr<BType> type4)
      : m_operator(op), m_types({type1, type2, type3, type4}) {}
  MonomorphizedOperator(const BOperator &op,
                        const std::vector<std::shared_ptr<BType>> &types)
      : m_operator(op), m_types(types) {}

  MonomorphizedOperator(const MonomorphizedOperator &other)
      : m_operator(other.m_operator),
        m_types(other.m_types),
        m_hash_valid(other.m_hash_valid),
        m_hash(other.m_hash) {}

  MonomorphizedOperator &operator=(const MonomorphizedOperator &other) {
    if (this != &other) {
      m_operator = other.m_operator;
      m_types = other.m_types;
      m_hash_valid = other.m_hash_valid;
      m_hash = other.m_hash;
    }
    return *this;
  }
  inline bool operator<(const MonomorphizedOperator &other) const {
    if (this->m_hash < other.m_hash) {
      return -1;
    } else if (other.m_hash < this->m_hash) {
      return 1;
    } else {
      return 0;
    }
  }

  MonomorphizedOperator(MonomorphizedOperator &&) = default;
  MonomorphizedOperator &operator=(MonomorphizedOperator &&) = default;

  bool operator==(const MonomorphizedOperator &rhs) const {
    if (this == &rhs) return true;
    return m_operator == rhs.m_operator && m_types == rhs.m_types;
  }

  std::string to_string() const;
  size_t opHash() const;
  const BOperator &getOperator() const { return m_operator; }
  const std::vector<std::shared_ptr<BType>> &getTypes() const {
    return m_types;
  }
};

namespace std {
template <> struct hash<MonomorphizedOperator> {
  // Add required constructors
  hash() = default;
  hash(const hash &) = default;
  hash(hash &&) = default;
  hash &operator=(const hash &) = default;
  hash &operator=(hash &&) = default;
  ~hash() = default;

  size_t operator()(const MonomorphizedOperator &op) const {
    return op.opHash();
  }
};
}  // namespace std

namespace std {
template <> struct hash<VarName> {
  // Add required constructors
  hash() = default;
  hash(const hash &) = default;
  hash(hash &&) = default;
  hash &operator=(const hash &) = default;
  hash &operator=(hash &&) = default;
  ~hash() = default;

  size_t operator()(const VarName &d) const { return d.hash_combine(0); }
};
}  // namespace std

/** @brief represents a free, user-defined, identifier appearing in a proof
 * obligation.
 */
typedef struct Data {
  std::shared_ptr<VarName> m_name;
  const BType &m_type;

  std::string to_string() const;
  inline bool operator==(const Data &other) const {
    return (*m_name == *(other.m_name) ||
            m_name->show() == other.m_name->show());
  }
} Data;

namespace std {
template <> struct hash<Data> {
  // Add required constructors
  hash() = default;
  hash(const hash &) = default;
  hash(hash &&) = default;
  hash &operator=(const hash &) = default;
  hash &operator=(hash &&) = default;
  ~hash() = default;

  size_t operator()(const Data &d) const { return d.m_name->hash_combine(0); }
};
}  // namespace std

struct Signature {
  std::unordered_set<MonomorphizedOperator> m_operators;
  std::unordered_set<Data> m_data;

  Signature() : m_operators{}, m_data{} {}
};

/**
 * @brief Get the signature of a predicate.
 *
 * The signature of a predicate is the set of monomorphized operators that
 * occur in the predicate.
 *
 * @param p The predicate to get the signature of.
 * @return The signature of the predicate.
 */
extern Signature predicateSignature(const Pred &p);

/**
 * @brief adds the contents of a signature to another signature
 * @param lhs the receiving object
 * @param rhs the source object
 */
extern Signature &operator+=(Signature &lhs, const Signature &rhs);

/** @brief removes elements of a signature from another signature */
extern Signature &operator-=(Signature &lhs, const Signature &rhs);

extern std::string toString(const Signature &sig);

#endif  // SIGNATURE_H