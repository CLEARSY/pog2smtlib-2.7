/******************************* CLEARSY **************************************
This file is part of b2smtlib

Copyright (C) 2024 CLEARSY (contact@clearsy.com)

b2smtlib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License version 3 as published by
the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/#include <map>
#include <string>
using std::string;

#include "axiom_templates.h"
#include <expr.h>

namespace baxioms {

AxiomInstantiator::AxiomInstantiator() {
    types_suffix_number = {{BType::INT, 0}, {BType::REAL, 1}};
    axiom_dependencies = {
        {"interval", {"mem"}}, // (string type)
        {"INT", {"mem"}},
        {"INTEGER", {"mem"}},
        {"NAT", {"mem"}},
        {"NAT1", {"mem"}},
        {"NATURAL", {"mem"}},
        {"NATURAL1", {"mem"}},
        {"FLOAT", {"mem"}},
        {"MaxInt", {}},
        {"MinInt", {}},
        {"STRING", {"mem"}},
        {"REAL", {"mem"}},

        // Binary Expression Operators
        {"set_eq", {"mem"}},
        {"set_prod", {}}, // (string typel, string typer);
        {"set_diff", {"mem"}},
        {"iexp", {}},
        {"rexp", {}},
        {"|+->|", {}},  // (string typel, string typer);
        {"|+->>|", {}}, // (string typel, string typer);
        {"|-->|", {}},  // (string typel, string typer);
        {"|-->>|", {}}, // (string typel, string typer);
        {"|<->|", {}},  // (string typel, string typer);
        {"|>+>|", {}},  // (string typel, string typer);
        {"|>->|", {}},  // (string typel, string typer);
        {"|>+>>|", {}}, // (string typel, string typer);
        {"|>->>|", {}}, // (string typel, string typer);
        {"|->|", {}},   // (string typel, string typer);
        {"composition", {}},
        {"binary_inter", {}}, // (string type);
        {"restriction_head", {}},
        {"semicolon", {}},
        {"|<+|", {}},
        {"|<-|", {}},
        {"domain_subtraction", {}},
        {"domain_restriction", {}},
        {"|><|", {}},
        {"parallel_product", {}},
        {"binary_union", {}},
        {"restriction_tail", {}},
        {"concatenate", {}},
        {"range_restriction", {}},
        {"range_subtraction", {}},
        {"image", {}},
        {"apply", {}},
        {"prj1", {"mem"}},
        {"prj2", {"mem"}},
        {"iterate", {}},
        {"|const|", {}},
        {"rank", {}}, // ?
        {"|+f|", {}},
        {"|-f|", {}},
        {"|*f|", {}},
        {"|fdiv|", {}},

        // Comparison Operators
        {"mem", {}},                   // (string type);
        {"subset", {"mem"}},           // (string type);
        {"strict_subset", {"subset"}}, // (string type);
        {"|<=f|", {}},
        {"|<f|", {}},
        {"|>=f|", {}},
        {"|>f|", {}},

        // Unary Expression Operators
        {"imax", {"mem"}},
        {"imin", {"mem"}},
        {"rmax", {"mem"}},
        {"rmin", {"mem"}},
        {"card", {""}}, // (string type);
        {"dom", {}},    // (string typel, string typer);
        {"ran", {}},    // (string typel, string typer);
        {"POW", {"mem"}},
        {"POW1", {"mem", "POW"}},
        {"FIN", {}},      // (string type);
        {"FIN1", {}},     // (string type);
        {"union", {}},    // (string type);
        {"inter", {}},    // (string type);
        {"seq", {}},      // (string type);
        {"seq1", {}},     // (string type);
        {"iseq", {}},     // (string type);
        {"iseq1", {}},    // (string type);
        {"inverse", {}},  // (string type);
        {"size", {}},     // (string type);
        {"perm", {}},     // (string type);
        {"first", {}},    // (string type);
        {"last", {}},     // (string type);
        {"id", {}},       // (string type);
        {"closure", {}},  // (string typel, string typer);
        {"closure1", {}}, // (string typel, string typer);
        {"tail", {}},     // (string type);
        {"front", {}},    // (string type);
        {"reverse", {}},  // (string type);
        {"rev", {}},      // (string type);
        {"conc", {}},     // (string type);
        {"succ", {}},
        {"pred", {}},
        {"rel", {}},
        {"fnc", {}},
        // string real(Int) Real)     ; utiliser la fonction to_real
        // string floor (Real) Int)    ; utiliser la fonction to_int
        {"ceiling", {}}
        // Expression N-ary Operators
        // string SEQ (%1) %1)
        // string SET (%1) %1)
    };
}

string AxiomInstantiator::getTypeSuffixString(const BType &type) {
    try {
        int res = types_suffix_number.at(type);
        return "_" + std::to_string(res);
    } catch (const std::out_of_range) {
        int res = types_suffix_number.size();
        types_suffix_number[type] = res;
        return "_" + std::to_string(res);
    }
};

void getDependenciesAux(const std::map<string, std::vector<string>> dep_graph,
                        const string symbol, std::vector<string> &res) {
    for (auto dep : dep_graph.at(symbol))
        getDependenciesAux(dep_graph, dep, res);
    res.push_back(symbol);
}

std::vector<string> AxiomInstantiator::getDependencies(const string axiom) {
    std::vector<string> res = {};
    getDependenciesAux(axiom_dependencies, axiom, res);
    return res;
}

const string sortP = R"(
(declare-sort P 1)
)";

const string sortC = R"(
(declare-datatype C (par (T1 T2) ((maplet (fst T1) (snd T2)))))
)";

const string interval = R"(
(declare-fun interval%2 (%1 %1) (P %1))

(assert (forall ((lb %1) (ub %1) (x %1))
  (= (mem%2 x (interval%2 lb ub)) (and (<= lb x) (<= x ub)))
))
)";

const string INT = R"(
(declare-const INT (P Int))

(assert (forall ((x Int)) (= (mem_0 x INT)
  (and (<= MinInt x) (<= x MaxInt)))
))
)";

const string INTEGER = R"(
(declare-const INTEGER (P Int))

(assert (forall ((x Int))
  (mem_0 x INTEGER)
))
)";

const string NAT = R"(
(declare-const NAT (P Int))

(assert (forall ((x Int))
  (= (mem_0 x NAT) (and (<= 0 x) (<= x MaxInt)))
))
)";

const string NAT1 = R"(
(declare-const NAT1 (P Int))\n

(assert (forall ((x Int))
  (= (mem_0 x NAT1) (and (<= 1 x) (<= x MaxInt)))
))
)";

const string NATURAL = R"(
(declare-const NATURAL (P Int))

(assert (forall ((x Int))
  (= (mem_0 x NATURAL) (<= 0 x))
))
)";

const string NATURAL1 = R"(
(declare-const NATURAL1 (P Int))

(assert (forall ((x Int))
  (= (mem_0 x NATURAL1) (<= 1 x))
))
)";

const string FLOAT = R"(
(declare-const FLOAT (P Float32))

(assert (forall ((x Float32)) (mem%1 x FLOAT)))
)";

const string MaxInt = R"(
(define-fun MaxInt () Int 2147483647)
)";

const string MinInt = R"(
(define-fun MinInt () Int (- 2147483648))
)";

const string STRING = R"(
(declare-const STRING (P String))

(assert (forall ((x String)) (mem%1 x STRING)))
)";

const string REAL = R"(
(declare-const REAL (P Real))

(assert (forall (x Real) (mem_1 x REAL)))
)";

// Binary Expression Operators
const string set_eq = R"(
(declare-fun set_eq%4 (%3 %3) Bool)

(assert (forall ((S1 %3) (S2 %3))
  (=
    (set_eq%4 S1 S2)
    (forall ((x %1)) (= (mem%2 x S1) (mem%2 x S2)))
  )
))
)";

const string set_prod = R"(
(declare-fun set_prod%2%4 ((P %1) (P %3)) (P (C %1 %3)))

(assert (forall ((s1 (P %1)) (s2 (P %3)) (x %1) (y %3))
  (=
    (mem%5 (maplet x y) (set_prod s1 s2))
    (and (mem%2 x s1) (mem%4 y s2))
  )
))
)"; ///@todo

const string set_diff = R"(
(declare-fun set_diff%4 (%3 %3) %3)

(assert (forall ((S1 %3) (S2 %3) (x %1))
  (=
    (mem%2 x (set_diff%4 S1 S2))
    (and (mem%2 x S1) (not (mem%2 x S2)))
  )
))
)";

const string iexp = R"_(
(declare-fun iexp (Int Int) Int)
(assert (!
  (forall ((x Int))
    (!
      (=> (not (= x 0)) (= (iexp x 0) 1))
      :pattern ((iexp x 0))
    )
  )
  :named |iexp_axiom_1|
))
(assert (!
  (forall ((x Int) (n Int))
    (!
      (=> (>= n 1) (= (iexp x n) (* x (iexp x (- n 1)))))
      :pattern ((iexp x n))
    )
  )
  :named |iexp_axiom_2|
))
)_";

const string rexp = R"_(
(declare-fun iexp (Int Int) Int)
(assert (!
  (forall ((x Int))
    (!
      (=> (not (= x 0)) (= (iexp x 0) 1))
      :pattern ((iexp x 0))
    )
   )
  :named |iexp_axiom_1|
))

(assert (!
  (forall ((x Int) (n Int))
    (!
      (=> (>= n 1) (= (iexp x n) (* x (iexp x (- n 1)))))
      :pattern ((iexp x n))
    )
  )
  :named |iexp_axiom_2|
))
)_";

// const string |+->| = "; TODO";
// const string |+->>| = "; TODO";
// const string |-->| = "; TODO";
// const string |-->>| = "; TODO";
// const string |<->| = "; TODO";
// const string |>+>| = "; TODO";
// const string |>->| = "; TODO";
// const string |>+>>| = "; TODO";
// const string |>->>| = "; TODO";
// const string |->| = "; TODO";
const string composition = "; TODO";

const string binary_inter = R"(
(declare-fun binary_inter%4 (%3 %3) %3)

(assert (forall ((x %1) (e1 %3) (e2 %3))
  (=
    (mem%2 x (binary_inter%4 e1 e2))
    (and (mem%2 x e1) (mem%2 x e2))
  )
))
)";

const string restriction_head = "; TODO";
const string semicolon = "; TODO";
// const string |<+| = "; TODO";
// const string |<-| = "; TODO";
const string domain_subtraction = "; TODO";
const string domain_restriction = "; TODO";
// const string |><| = "; TODO";
const string parallel_product = "; TODO";

const string binary_union = R"(
(declare-fun binary_union%4 (%3 %3) %3)

(assert (forall ((x %1) (e1 %3) (e2 %3))
  (=
    (mem%2 x (binary_union%4 e1 e2))
    (or (mem%2 x e1) (mem%2 x e2))
  )
))
)";

const string restriction_tail = "; TODO";
const string concatenate = "; TODO";
const string range_restriction = "; TODO";
const string range_subtraction = "; TODO";
const string image = "; TODO";

const string apply = R"(
(declare-fun apply%3 ((P (C %1 %2)) %1) %2)

(assert (forall ((R (P (C %1 %2))) (x %1) (y %2))
  (=
    (= (apply%3 R x) y)
    (mem%4 (maplet x y) R)
  )
))
)";

const string prj1 = R"(
(declare-fun prj1%2%4 ((P %1) (P %3)) (P (C (C %1 %3) %1)))

(assert (forall ((e1 %1) (e2 %3) (e3 %1) (s1 (P %1)) (s2 (P %3)))
  (=
    (mem%5 (maplet (maplet e1 e2) e3) (prj1%2%4 s1 s2))
    (and
      (mem%2 e1 s1)
      (mem%4 e2 s2)
      (= e3 (fst (maplet e1 e2)))
    )
  )
))
)";

const string prj2 = R"(
(declare-fun prj2%2%4 ((P %1) (P %3)) (P (C (C %1 %3) %1)))

(assert (forall ((e1 %1) (e2 %3) (e3 %3) (s1 (P %1)) (s2 (P %3)))
  (=
    (mem%5 (maplet (maplet e2 e2) e3) (prj1%2%4 s1 s2))
    (and
      (mem%2 e1 s1)
      (mem%4 e2 s2)
      (= e3 (snd (maplet e2 e2)))
    )
  )
))
)";

const string iterate = "; TODO";
// const string |const| = "; TODO";
const string rank = "; TODO"; // ?
// const string |+f| = "; TODO";
// const string |-f| = "; TODO";
// const string |*f| = "; TODO";
// const string |fdiv| = "; TODO";

// Comparison Operators
const string mem = R"(
(declare-fun mem%2 (%1 (P %1)) Bool)

(declare-const empty%2 (P %1))

(assert (forall ((x %1))
  (not (mem%2 x empty%2))
))
)";

const string subset = R"(
(declare-fun subset%2 ((P %1) (P %1)) Bool)

(assert (forall ((s1 (P %1)) (s2 (P %1)) (x %1))
  (=
    (subset%2 s1 s2)
    (=> (mem%2 x s1) (mem%2 x s2))
  )
))
)";

const string strict_subset = R"(
(declare-fun strict_subset%2 ((P %1) (P %1)) Bool)

(assert (forall ((s1 (P %1)) (s2 (P %1)) (x %1))
  (=
    (strict_subset%2 s1 s2)
    (and
      (subset s1 s2)
      (exists ((x %i))
      (and (mem%2 x s2) (not (mem%2 x s1))))
    )
  )
))
)";

// const string |<=f| = "; TODO";
// const string |<f| = "; TODO";
// const string |>=f| = "; TODO";
// const string |>f| = "; TODO";

// Unary Expression Operators
const string imax = R"_(
(declare-fun imax ((P Int)) Int)

(assert (
  forall ((e (P Int)) (m Int) (x Int))
  (=
    (= m (imax e))
    (and (mem_0 m e) (>= m x))
  )
))
)_";

const string imin = R"_(
(declare-fun imin ((P Int)) Int)

(assert (
  forall ((e (P Int)) (m Int) (x Int))
  (=
    (= m (imin e))
    (and (mem_0 m e) (<= m x))
  )
))
)_";

const string rmax = R"_(
(declare-fun rmax ((P Real)) Real)

(assert (
  forall ((e (P Real)) (m Real) (x Real))
  (=
    (= m (rmax e)
    (and (mem_1 m e) (>= m x))
  )
))
)_";

const string rmin = R"_(
(declare-fun rmin ((P Real)) Real)

(assert (
  forall ((e (P Real)) (m Real) (x Real))
  (=
    (= m (rmin e))
    (and (mem_1 m e) (<= m x))
  )
))
)_";

const string card = "; TODO";

const string dom = R"(
(declare-fun dom%4 (P (C %1 %2)) (P %1))

(assert (forall ((R (P (C %1 %2))) (e %1))
  (=
    (mem%3 e (dom%4 R))
    (exists ((x %2)) (mem%5 (maplet e x) R))
  )
))
)";

const string ran = R"(
(declare-fun ran%4 (P (C %1 %2)) (P %2))

(assert (forall ((R (P (C %1 %2))) (e %2))
  (=
    (mem%3 e (ran%4 R))
    (exists ((x %1)) (mem%5 (maplet x e) R))
  )
))
)";

const string POW = R"(
(declare-fun POW%4 (%3) (P %3))

(assert (forall ((x %3) (e %3))
  (=
    (mem%4 x (POW%4 e))
    (forall ((t %1)) (=> (mem%2 t x) (mem%2 t e)))
  )
))
)";

const string POW1 = R"_(
(declare-fun POW1%4 (%3) (P %3))

(assert (forall ((x %3) (e %3))
  (=
    (mem%4 x (POW1%4 e))
    (and
      (mem%4 x (POW%4 s))
      (exists ((y %1)) (mem%2 y (POW1%4 e)))
    )
  )
))
)_";

const string FIN = "; TODO";
const string FIN1 = "; TODO";

const string inter = R"(
(declare-fun inter%4 (%3) %1)

(assert (forall ((e %1) (S %3))
  (=
    (mem%2 e (inter%4 S))
    (forall ((x %1)) (=> (mem%2 x S) (mem%2 e x)))
  )
))
)";

const string bunion = R"(
(declare-fun union%4 (%3) %1)

(assert (forall ((e %1) (S %3))
  (=
    (mem%2 e (union%4 S))
    (exists ((x %1)) (and (mem%2 x S) (mem%2 e x)))
  )
))
)";

const string seq = "; TODO";
const string seq1 = "; TODO";
const string iseq = "; TODO";
const string iseq1 = "; TODO";
const string inverse = "; TODO";
const string size = "; TODO";
const string perm = "; TODO";
const string first = "; TODO";

const string last = "; TODO";

const string id = R"(
(declare-fun id%2 ((P %1)) (P (C %1 %1)))

(assert (forall ((x %1) (y %1) (S (P %1)))
  (=
    (mem%3 (maplet x y) (id%2 S))
    (and (= x y) (mem%4 x S))
  )
))
)";

const string closure = "; TODO";
const string closure1 = "; TODO";
const string tail = "; TODO";
const string front = "; TODO";
const string reverse = "; TODO";
const string rev = "; TODO";

const string conc = R"(
(declare-fun conc ((C (U V)) C(V W)))

(assert (forall ((x (C (U W)))
  (r (C (U V))) (s (C (V W)))) (= (mem ) ()
))
)";
///@todo

const string succ = R"(
(declare-const succ (P (C Int Int)))

(assert (forall ((n Int) (m Int))
  (=
    (mem%1 (maplet n m) succ)
    (= n (+ m 1))
  )
))
)";

const string pred = R"(
(declare-const pred (P (C Int Int)))

(assert (forall ((n Int) (m Int))
  (=
    (mem%1 (maplet n m) pred)
    (= n (- m 1))
  )
))
)";

const string rel = "; TODO";
const string fnc = "; TODO";

const string real = R"(
(declare-const real (P (C Int Real)))

(assert (forall ((x Int) (y Real))
  (=
    (mem%1 (maplet x y) real)
    (= (to_real x) y)
  )
))
)";

const string floor = R"(
(declare-const floor (P (C Real Int)))

(assert (forall ((x Real) (y Int))
  (=
    (mem%1 (maplet x y) floor)
    (= (to_int x) y)
  )
))
)";

const string ceiling = R"(
(declare-const ceiling (P (C Real Int)))

(assert (forall ((x Real) (y Int))
  (=>
    (is_int x)
    (=
      (mem%1 (maplet x y) (ceiling))
      (= (to_int x) y)
    )
  )
))

(assert (forall ((x Real) (y Int))
  (=>
    (not (is_int x))
    (=
      (mem%1 (maplet x y) (ceiling))
      (= (+ 1 (to_int x)) y)
    )
  )
))
)";

// Expression N-ary Operators
// const string SEQ (%1) %1)
// const string SET (%1) %1)

} // namespace baxioms
