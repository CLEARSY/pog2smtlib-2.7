# pog2smtlib-2.7

[![License](https://img.shields.io/badge/license-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0.en.html)

![Build & Test](https://github.com/CLEARSY/b2smtlib/actions/workflows/cmake-multi-platform.yml/badge.svg)
![Code format](https://github.com/CLEARSY/b2smtlib/actions/workflows/clang-format-check.yml/badge.svg)

`pog2smtlib-2.7` is a translator from pog to SMT-LIB 2.6.

## Usage

```sh
pog2smtlib27 -i <input.pog> -o <output>
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

## Contributing

We welcome external contributors to `pog2smtlib-2.7`!

Please carefully read the CONTRIBUTING.md file in this repository in case you consider contributing.

## Licensing

This code is distributed under the license: "GNU GENERAL PUBLIC LICENSE, Version 3".
See the LICENSE file in this repository.

## Acknowledgments

This project is developed and maintained by [CLEARSY](https://www.clearsy.com/). It has been partly financed by the [Agence Nationale de la Recherche](https://anr.fr) grant ANR-21-CE25-0010 for the
[BLaSST](https://anr.fr/Project-ANR-21-CE25-0010) project (Enhancing B Language Reasoners with SAT and SMT Techniques).

