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
#ifndef AXIOM_TEMPLATES_H
#define AXIOM_TEMPLATES_H

#include <string>
using std::string;
#include <map>

#include "expr.h"

namespace baxioms {

/** @brief Utility class to instantiate axiom schematas */
class AxiomInstantiator {
 public:
  AxiomInstantiator();

  /** @brief returns the distinguishing suffix of a type for monomorphisation
   */
  string getTypeSuffixString(const BType &type);

  /** @brief returns the set of symbols that are used (transitively) in the
   * axiomatization of a symbol */
  std::vector<string> getDependencies(const string &symbol);

 private:
  std::map<string, std::vector<string>> axiom_dependencies;
  std::map<BType, int> types_suffix_number;
  std::map<BType, string> types_suffix;
};

extern const string sortP;
extern const string sortC;
extern const string interval;

// Building sets
extern const string empty;
extern const string INT;
extern const string INTEGER;
extern const string NAT;
extern const string NAT1;
extern const string NATURAL;
extern const string NATURAL1;
extern const string FLOAT;
extern const string MaxInt;
extern const string MinInt;
extern const string STRING;
extern const string REAL;

// Binary Expression Operators
extern const string set_eq;
extern const string set_prod;
extern const string set_diff;
extern const string iexp;
extern const string rexp;

// extern const string |+->|;
// extern const string |+->>|;
// extern const string |-->|;
// extern const string |-->>|;
// extern const string |<->|;
// extern const string |>+>|;
// extern const string |>->|;
// extern const string |>+>>|;
// extern const string |>->>|;
// extern const string |->|;
extern const string composition;
extern const string binary_inter;
extern const string restriction_head;
extern const string semicolon;
// extern const string |<+|;
// extern const string |<-|;
extern const string domain_subtraction;
extern const string domain_restriction;
// extern const string |><|;
extern const string parallel_product;
extern const string binary_union;
extern const string restriction_tail;
extern const string concatenate;
extern const string range_restriction;
extern const string range_subtraction;
extern const string image;
extern const string apply;
extern const string prj1;
extern const string prj2;
extern const string iterate;
// extern const string |const|;
extern const string rank;  // ?
// extern const string |+f|;
// extern const string |-f|;
// extern const string |*f|;
// extern const string |fdiv|;

// Comparison Operators
extern const string mem;
extern const string subset;
extern const string strict_subset;
// extern const string |<=f|;
// extern const string |<f|;
// extern const string |>=f|;
// extern const string |>f|;

// Unary Expression Operators
extern const string imax;
extern const string imin;
extern const string rmax;
extern const string rmin;
extern const string card;
extern const string dom;
extern const string ran;
extern const string POW;
extern const string POW1;
extern const string FIN;
extern const string FIN1;
extern const string inter;
extern const string bunion;
extern const string seq;
extern const string seq1;
extern const string iseq;
extern const string iseq1;
extern const string inverse;
extern const string size;
extern const string perm;
extern const string first;
extern const string last;
extern const string id;
extern const string closure;
extern const string closure1;
extern const string tail;
extern const string front;
extern const string reverse;
extern const string rev;
extern const string conc;
extern const string succ;
extern const string pred;
extern const string rel;
extern const string fnc;
extern const string real;
extern const string floor;
extern const string ceiling;
// Expression N-ary Operators
// string SEQ (%1) %1)
// string SET (%1) %1)

}  // namespace baxioms

#endif
