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
#ifndef BTYPE_UTILS_H
#define BTYPE_UTILS_H

#include "btype.h"

/**
 * @brief Functor to compute a hash for shared pointers to BType.
 *
 * This can be used with unordered containers keyed by
 * std::shared_ptr<const BType>. The hash delegates to the pointed-to
 * BType's hash_combine method.
 */
struct BTypeHash {
  /**
   * @brief Compute a size_t hash for a shared pointer to a BType.
   *
   * @param t Shared pointer to the BType to hash; must not be null.
   * @return A size_t value suitable for use in unordered containers.
   */
  size_t operator()(const std::shared_ptr<const BType> &t) const {
    size_t result = t->hash_combine(0);
    return result;
  }
};

/**
 * @brief Functor to compare two shared pointers to BType for equality.
 *
 * Equality is defined by delegating to the pointed-to BType's
 * operator==. Both pointers must be non-null.
 */
struct BTypeEqual {
  /**
   * @brief Test whether two shared pointers refer to equal BType values.
   *
   * @param lhs Left-hand shared pointer (non-null).
   * @param rhs Right-hand shared pointer (non-null).
   * @return true if the pointed-to BType values are equal, false otherwise.
   */
  bool operator()(const std::shared_ptr<const BType> &lhs,
                  const std::shared_ptr<const BType> &rhs) const {
    int result = (*lhs == *rhs);
    return result;
  }
};

/**
 * @brief Strict-weak-order comparator for shared pointers to BType.
 *
 * Uses the pointed-to BType's operator< to provide a total ordering suitable
 * for ordered containers (std::set, std::map) keyed by
 * std::shared_ptr<const BType>.
 */
struct BTypeCompare {
  /**
   * @brief Compare two shared pointers by comparing the referenced BType
   *        values.
   *
   * @param lhs Left-hand shared pointer (non-null).
   * @param rhs Right-hand shared pointer (non-null).
   * @return true if *lhs is less than *rhs, false otherwise.
   */
  bool operator()(const std::shared_ptr<const BType> &lhs,
                  const std::shared_ptr<const BType> &rhs) const {
    return *lhs < *rhs;
  }
};

#endif /* BTYPE_UTILS_H */
