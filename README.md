# B2SMTLIB

![Build & Test](https://github.com/CLEARSY/b2smtlib/actions/workflows/cmake-multi-platform.yml/badge.svg)
![Code format](https://github.com/CLEARSY/b2smtlib/actions/workflows/clang-format-check.yml/badge.svg)

B2SMTLIB is a translator from pog to SMT-LIB 2.6.

## To do list

- For a pure typing predicate such as `xx: INTEGER`, the signature contains `:_<INT>` and `INTEGER`, which entails that all
  the prerequisites of `INTEGER` are pulled. **We do not want this**
- BAST does not read the `RichTypeInfos` table from the POG file when it exists. We need to add this feature, which includes
  reading the `richtypref` attribute when available instead of the `typref` attribute.
- Refactorize symbol name generation so that smtSymbol functions are called to fill the templates from the derived classes
  of `BConstruct`.
- Have `POGsignatures` be a member of `POGtranslations` maybe?
- Cover the full list of B expression operators.

## Usage

```sh
b2smtlib -i <input.pog> -o <output>
```

## Compilation

To compile the project with CMake:

```sh
cmake -B build
cmake --build build
```

## Testing

To test the project (after compilation), run the following commands:

```sh
cd build
ctest
```

## Specification Coverage

[x] Predefined Types
[ ] User-defined Types
    [ ] Abstract Sets
    [ ] Enumerated Sets
    Il faut être capable de charger un fichier POG qui contient des informations de type riches (richTypeInfos).
[x] Powerset Types
[x] Cartesian Product Types
[ ] Record
[x] Belonging Predicates
[x] Equality Predicates
    [x] Set Equality
[ ] Inclusion Predicates
    [x] Inclusion
    [ ] Strict Inclusion
[x] Boolean Expressions
[ ] Arithmetical Expressions I
    [x] MAXINT
    [x] MININT
    [x] +
    [x] -
    [x] *
    [x] /
    [ ] mod
    [ ] **
    [ ] succ
    [ ] pred
    [x] floor
    [x] ceiling
    [x] real
[ ] Arithmetical Expressions II
[ ] Generalized Product
[x] Expression of Couples
[ ] Building Sets
[ ] Set List Expressions
[ ] Set List Expressions (Continued)
[ ] Record Expressions
[ ] Sets of Relations
[ ] Expressions of Relations I
[ ] Expressions of Relations II
[ ] Expressions of Relations III
[ ] Expressions of Relations IV
[ ] Sets of Functions
[ ] Expressions of Functions
[ ] Sets of Sequences
[ ] Sequences Expressions I
[ ] Sequences Expressions II

## Contributing

We welcome external contributors to b2smtlib!

Please carefully read the CONTRIBUTING.md file in this repository in case you consider contributing.

## Licensing

This code is distributed under the license: "GNU GENERAL PUBLIC LICENSE, Version 3".
See the LICENSE file in this repository.
