# Coverage

## Introduction

This document presents the coverage of the language of B proof obligation files in the so-called POG format.

We consider several layers of coverage, in increasing order :

* not covered : the tool fails to encode proof obligations containing the construct.
* syntactic coverage : the tool produces an SMTLIB-2.7 construct that represents the B construct, but not the theory elements that would let a SMT solver prove a valid proof obligation containing the construct.
* semantic coverage : the tool produces an SMTLIB-2.7 construct that represents the B construct, and the theory elements that would let a SMT solver prove a valid proof obligation containing the construct.

Coverage is justified based on the test bench of the tool. For each construct, the corresponding tests are identified.

## 3 Types

### 3.2 Types

* INTEGER
  * semantic coverage: type_INTEGER
* REAL
  * semantic coverage: type_REAL
* FLOAT
  * no coverage
* BOOL
  * semantic coverage: type_BOOL
* STRING
  * semantic coverage: type_STRING
* Ident (Abstract set)
  * semantic coverage: type_abstract_set
* Ident (Enumerated set)
  * semantic coverage: type_enumerated_set
* Power
  * semantic coverage: type_power
* Product
  * semantic coverage: type_product
* Struct
  * semantic coverage: type_struct

## 4 Predicates

### 4.1 Propositions

* Conjunction
  * semantic coverage: propositions
* Negation
  * semantic coverage: propositions
* Disjunction
  * semantic coverage: propositions
* Implication
  * semantic coverage: propositions
* Equivalence
  * semantic coverage: propositions

### 4.2 Quantified Predicates

* Universal quantifier
  * semantic coverage: forall_1, forall_2
* Existential quantifier
  * semantic coverage: exists_1, exists_2

### 4.3 Equality Predicates

* Equal to
  * semantic coverage: equal, expr_comparison_1, expr_comparison_2
* Unequal to (actually unequal is not a POG operator since it is replaced by the negation of an equality)
  * semantic coverage: unequal

### 4.4 Belonging Predicates

* Belonging
  * semantic coverage: belonging_predicate_1, belonging_predicate_2
* Non belonging
  * semantic coverage: non_belonging_predicate_1

### 4.5 Inclusion Predicates

* Inclusion
  * semantic coverage: inclusion_1, inclusion_2
* Strict inclusion
  * semantic coverage: strict_inclusion_1, strict_inclusion_2
* Non inclusion
  * semantic coverage: non_inclusion_1
* Strict non inclusion
  * semantic coverage: non_strict_inclusion_1

### 4.6 Numbers Comparison Predicates

* Less than or equal to
  * semantic coverage: less_than_or_equal_to
* Strictly less than
  * semantic coverage: strictly_less_than
* Greater than or equal to
  * semantic coverage: greater_than_or_equal_to
* Strictly greater than
  * semantic coverage: strictly_greater_than

## 5. Expressions

### 5.1 Primary Expressions

* Data
* Renaming data
* The specific value of a data item
* Expression in brackets
* Character string

### 5.2 Boolean Expressions

* value of true
  * semantic coverage: true_1
* value of false
  * semantic coverage: false_1
* conversion of a predicate into a Boolean expression
  * semantic coverage: bool_1, bool_2

### 5.3 Arithmetical Expressions

* The largest implementable integer
* The smallest implementable integer
* Addition
* Difference, and also unary minus
* Product
* Integer division
* Modulo
* Power of
* Successor
* Predecessor
* Floor function
* Ceiling function
* Conversion from Z to ℝ

### 5.4 Arithmetical Expressions (continued)

* Maximum
* Minimum
* Cardinal
* Sum of arithmetical expressions
* Product of arithmetical expressions

### 5.5 Expressions of Couples

* Binary correspondence (maplet)

### 5.6 Building Sets

* Empty-set
* Set of relative integers
* Set of integers
* Set of non null integers
* Set of implementable integers
* Set of non null implementable integers
* Set of implementable relative integers
* Set of real numbers
* Set of floating numbers
* Set of Boolean values
* Set of character strings

### 5.7 Set List Expressions

* Cartesian product
* Set of sub-sets (power-set)
* Set of non empty sub-sets
* Set of finite sub-sets
* Set of non empty finite sub-sets
* Set defined in comprehension
* Set defined in extension
* Interval

### 5.8 Set List Expressions (continued)

* Difference
* Union
* Intersection
* Generalized union
* Generalized intersection
* Quantified union
* Quantified intersection

### 5.9 Record expressions

* Set of records
* record in extension
* access to a record field (quote operator)

### 5.10 Sets of Relations

* Sets of relations

### 5.11 Expressions of Relations

* Identity
* Reverse
* First projection
* Second projection
* Composition
* Direct product
* Parallel product

### 5.12 Expressions of Relations (continued)

* Iteration
* Transitive and reflexive closure
* Transitive closure

### 5.13 Expressions of Relations (continued)

* Domain
* Range
* Image

### 5.14 Expressions of Relations (continued)

* Restriction in the domain
* Subtraction in the domain
* Restriction in the range
* Subtraction in the range
* Overwrite

### 5.15 Sets of Functions

* Partial functions
* Total functions
* Partial injections
* Total injections
* Partial surjections
* Total surjections
* Total bijections

### 5.16 Expressions of Functions

* Lambda-expression
* Evaluation of the function
* Transformed into a function
* Transformed into a relation

### 5.17 Sets of Sequences

* Sequences
* Non empty sequences
* Injective sequences
* Injective non empty sequences
* Permutations
* Empty sequence
* Sequence in extension

### 5.18 Sequence Expressions

* Size
* First element
* Last element
* Front
* Tail
* Reverse

### 5.19 Sequence Expressions (continued)

* Concatenation
* Insert in front
* Insert at tail
* Restrict in front
* Restrict at tail
* General concatenation
