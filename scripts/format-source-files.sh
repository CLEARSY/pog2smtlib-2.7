#!/bin/bash
find src/pog2smtlib-2.7 \( -name '*.cpp' -o -name '*.h' \) -exec clang-format-19 -i -style=file {} \;

