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
