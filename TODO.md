# To continue the work on b2smtlib

## Code Structure

The b2smtlib code is divided into three main modules:

- `smtlib`, which contains the translation functions.
  During the traversal of the POG to be translated, a decls object (of the PreludeBuilder class) is maintained. This object is responsible for providing the "prelude," which includes the definition and axiomatization of function symbols.

- `PreludeBuilder`, the class responsible for creating the prelude.
  PreludeBuilder returns the names of the symbols to use and updates the set of required definitions. These axioms are generated using schemas from axiom_templates.

- `axiom_templates`, which contains the templates for axioms and their dependencies.

## Remaining Work

Here are some development directions to complete and enhance the b2smtlib code.

### Dependencies Between Axioms and Polymorphic Symbols

Currently, to handle dependencies between definitions (e.g., defining one symbol requires the definition of one or more others), we use `baxioms::AxiomInstantiator::axiom_dependencies`. However, this representation does not account for the types used with these axioms.
For instance, dom is a function `P (C U V) -> P U`. But to use it, we need `mem` (:, in B) for the type `U` (a function of type `U`, `(P U) -> Bool`).

One approach is to manually add the definitions.
This is done for specific cases, such as using `addAxiom` in getAxiomatisation. This eliminates the need for a data structure to manage the dependency graph.

If a data structure is used to represent dependencies, it must handle the types associated with symbols and allow us to express types in relation to one another. For example, for `dom`, we must express that `(dom, P (C U V))` depends on `(mem, U)`, where `U` and `V` are arbitrary types.

It’s also worth noting that some symbols are not polymorphic (e.g., `pred` or `NATURAL` are monomorphic but depend on mem for the types `C Int Int` and `Int`, respectively). This needs to be managed as well.

### Using BAST Enums

Reduce the use of strings and rely more on enum values (e.g., `Expr::BinaryOp`, etc.) in calls, such as in prelude_builder::addSymbol, `prelude_builder::getAxiomatisation`, and `SmtFunDecl::addAxiom`.

### Reduce external dependencies

For formatting axioms (and axiom schemas), replace `QString` with an alternative.

For filesystem access, replace `QDir`, `QFile` etc. with `std::filesystem`.

Note that there is still a dependency on Qt within `POGLoader`.

### Adding Triggers to Axioms

This requires skolemization of formulas.
It might involve generating fresh variable names for existentially quantified formulas.

For writing triggers, Defourné’s thesis presents a strategy (see Section 5.3).

### N-ary Expressions: SET and SEQ

These are currently unsupported. The `SET` (enumerated set) and `SEQ` (sequence) symbols are remnants of pog2smt.

For enumerated sets, one possibility is to add a set name (as is done for comprehension-defined sets) and include membership axioms. For example, translating:

> myset = {1, 2, 3, 4}

into:

> (declare-const myset (P Int))
>
> (declare-fun mem_0 (Int (P Int)) Bool)
>
> (assert (forall ((x Int)) (= (mem_0 x myset) (or (= x 1) (= x 2) (= x 3) (= x 4)))))

For sequences, one option is to build the associated enumerated set:

> [5, 3, 6] -> {(1 |-> 5), (2 |-> 3), (3 |-> 6)}

### Comprehension-Defined Sets

The implementation for comprehension-defined sets (QuantifiedSet) is incomplete.
