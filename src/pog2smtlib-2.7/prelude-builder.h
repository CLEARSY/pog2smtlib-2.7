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
******************************************************************************/
#ifndef PRELUDE_BUILDER_H
#define PRELUDE_BUILDER_H

#include <string>
#include <vector>
using std::string;

#include "axiom-templates.h"
#include "pog.h"
#include "pred.h"

namespace preludebuilder {

/**
 * class `SmtADT` represents ADTs in SMT-LIB.
 * ADTs are charactrized by their name, arity, sort parameter names, constructor
 * name, and selectors names. We do not use testers.
 */
struct SmtADT {
  string name;
  size_t arity;
  std::vector<string> sort_params;
  string constructor_name;
  std::vector<string> selectors;

  string getDeclaration() const {
    string res = "(declare-datatype " + name;

    // add sort parameters
    if (sort_params.size() > 0) {
      res += " (par ";
      for (string param : sort_params) res += param + " ";
      res += ")";
    }

    // add constructor
    res += (constructor_name == "" ? " (" : "((") + constructor_name;
    for (auto field : selectors) res += " (" + field + ")";
    res += constructor_name == "" ? "))" : ")))";
    return res;
  };

  string getName() const { return name; };
};

class PreludeBuilder {
 public:
  PreludeBuilder();

  /** Return the prelude declaration  */
  string getPrelude() const;

  /** Updates declaration with necessary axioms and return the symbol name to
   *  use.
   */
  string addSymbol(const string symb);
  string addSymbol(const string symb, const BType &type);
  string addSymbol(const string symb, const BType &ltype, const BType &rtype);
  /** Add an ADT corresponding to BType and return its name. */
  string addADTSymbol(const BType &type);
  /** Add a sort of given name and arity */
  string addSort(const string &name, int arity);
  /** Add a comprehension set of predicate pred and type t, and return its
   * name */
  string addComprehensionSet(const Expr::QuantifiedSet &s, const string varname,
                             const BType &t, const string pred);
  /** Add an ADT corresponding to an enumerated set. */
  string addEnumADT(const pog::Set &s);

  /** Returns the SMT-LIB string corresponding to a type. */
  string BTypeToSMTString(const BType &type);

 private:
  SmtADT SmtADTFromBType(const BType &type);
  std::vector<string> declarations;
  std::vector<SmtADT> adtSymbols;
  // decl est instanciee
  void addDeclaration(const string decl);

  // return instantiated axiom for `symbol`
  string getAxiomatisation(const string symbol);
  string getAxiomatisation(const string symbol, const BType &type);
  string getAxiomatisation(const string symbol, const BType &typel,
                           const BType &typer);

  int comprehension_sets;
  baxioms::AxiomInstantiator axiom_generator;
};

}  // namespace preludebuilder

#endif
