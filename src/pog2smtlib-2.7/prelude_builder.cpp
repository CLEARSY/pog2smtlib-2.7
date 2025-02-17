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
#include <iostream>
#include <map>
#include <stack>
#include <string>
using std::string;
#include <vector>

#include "pog.h"
#include "pred.h"
#include "prelude_builder.h"

namespace preludebuilder {

static int count = 0;

SmtADT PreludeBuilder::SmtADTFromBType(const BType &t) {
  SmtADT res;
  switch (t.getKind()) {
    case BType::Kind::EnumeratedSet: {
      BType::EnumeratedSet est = t.toEnumeratedSetType();
      res.name = "enumerated_set_" + est.getName();
      res.arity = 0;
      res.constructor_name = "";
      res.selectors = {};
      for (auto fd : est.getContent()) res.selectors.push_back(fd);

      break;
    }
    case BType::Kind::Struct: {
      BType::RecordType rt = t.toRecordType();
      res.name = "struct_" + std::to_string(count);
      res.arity = 0;
      res.constructor_name = res.name;
      res.selectors = {};
      for (auto fd : rt.fields) {
        string str = fd.first + " " + BTypeToSMTString(fd.second);
        res.selectors.push_back(str);
      }
      break;
    }
    default: {
      assert(false);
    }
  }

  return res;
};

bool operator==(SmtADT const &lhs, SmtADT const &rhs) {
  return lhs.arity == rhs.arity && lhs.sort_params == rhs.sort_params &&
         rhs.selectors == lhs.selectors;
}

/**
 * @brief BTypeToSMTString builds the string of an SMT sort for BType `t`.
 * @param t
 * @return
 */
string PreludeBuilder::BTypeToSMTString(const BType &t) {
  switch (t.getKind()) {
    case BType::Kind::INTEGER:
      return "Int";
    case BType::Kind::BOOLEAN:
      return "Bool";
    case BType::Kind::FLOAT:
      return "Float32";
    case BType::Kind::REAL:
      return "Real";
    case BType::Kind::STRING:
      return "String";
    case BType::Kind::ProductType:
      return "(C " + BTypeToSMTString(t.toProductType().lhs) + " " +
             BTypeToSMTString(t.toProductType().rhs) + ")";
    case BType::Kind::PowerType:
      return "(P " + BTypeToSMTString(t.toPowerType().content) + ")";
    case BType::Kind::Struct:
      return addADTSymbol(t);
    case BType::Kind::AbstractSet: {
      auto &st = t.toAbstractSetType();
      return st.getName();
    }
    case BType::Kind::EnumeratedSet: {
      SmtADT adt = SmtADTFromBType(t);
      return adt.getName();
    }
  }
  // unreachable
  assert(false);
  return string();
}

PreludeBuilder::PreludeBuilder() {
  baxioms::AxiomInstantiator axiom_generator = baxioms::AxiomInstantiator();
  declarations = {baxioms::sortP, baxioms::sortC};
  adtSymbols = {};
  comprehension_sets = 0;
};  // namespace preludebuilder

string PreludeBuilder::getAxiomatisation(const string symb) {
  if (symb == "INT") {
    addSymbol("mem", BType::INT);
    return baxioms::INT;
  } else if (symb == "INTEGER") {
    addSymbol("mem", BType::INT);
    return baxioms::INTEGER;
  } else if (symb == "NAT") {
    addSymbol("mem", BType::INT);
    return baxioms::NAT;
  } else if (symb == "NAT1") {
    addSymbol("mem", BType::INT);
    return baxioms::NAT1;
  } else if (symb == "NATURAL") {
    addSymbol("mem", BType::INT);
    return baxioms::NATURAL;
  } else if (symb == "NATURAL1") {
    addSymbol("mem", BType::INT);
    return baxioms::NATURAL1;
  } else if (symb == "REAL") {
    addSymbol("mem", BType::REAL);
    return baxioms::REAL;
  } else if (symb == "FLOAT") {
    addSymbol("mem", BType::FLOAT);
    return QString(baxioms::FLOAT.c_str())
        .arg(axiom_generator.getTypeSuffixString(BType::FLOAT).c_str())
        .toStdString();
  } else if (symb == "STRING") {
    addSymbol("mem", BType::STRING);
    return QString(baxioms::STRING.c_str())
        .arg(axiom_generator.getTypeSuffixString(BType::STRING).c_str())
        .toStdString();
  } else if (symb == "MaxInt")
    return baxioms::MaxInt;
  else if (symb == "MinInt")
    return baxioms::MinInt;
  else if (symb == "iexp")
    return baxioms::iexp;
  else if (symb == "rexp")
    return baxioms::rexp;
  else if (symb == "imin") {
    addSymbol("mem", BType::INT);
    return baxioms::imin;
  } else if (symb == "imax") {
    addSymbol("mem", BType::INT);
    return baxioms::imax;
  } else if (symb == "rmin") {
    addSymbol("mem", BType::REAL);
    return baxioms::rmin;
  } else if (symb == "rmax") {
    addSymbol("mem", BType::REAL);
    return baxioms::rmax;
  } else if (symb == "pred") {
    BType intint = BType::PROD(BType::INT, BType::INT);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", intint);
    return QString(baxioms::pred.c_str())
        .arg(axiom_generator.getTypeSuffixString(intint).c_str())
        .toStdString();
  } else if (symb == "succ") {
    BType intint = BType::PROD(BType::INT, BType::INT);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", intint);
    return QString(baxioms::succ.c_str())
        .arg(axiom_generator.getTypeSuffixString(intint).c_str())
        .toStdString();
  } else if (symb == "real") {
    BType restype = BType::PROD(BType::INT, BType::REAL);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", restype);
    return QString(baxioms::real.c_str())
        .arg(axiom_generator.getTypeSuffixString(restype).c_str())
        .toStdString();
  } else if (symb == "floor") {
    BType restype = BType::PROD(BType::REAL, BType::INT);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", restype);
    return QString(baxioms::floor.c_str())
        .arg(axiom_generator.getTypeSuffixString(restype).c_str())
        .toStdString();
  } else if (symb == "ceiling") {
    BType restype = BType::PROD(BType::REAL, BType::INT);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", restype);
    return QString(baxioms::ceiling.c_str())
        .arg(axiom_generator.getTypeSuffixString(restype).c_str())
        .toStdString();
  } else {
    return "; TODO";
  }
}

string PreludeBuilder::getAxiomatisation(const string axiom,
                                         const BType &type) {
  if (axiom == "mem")
    return QString(baxioms::mem.c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  else if (axiom == "set_eq") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::set_eq.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "set_diff") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::set_diff.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "interval")
    return QString(baxioms::interval.c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  else if (axiom == "subset")
    return QString(baxioms::subset.c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  else if (axiom == "strict_subset")
    return QString(baxioms::strict_subset.c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  else if (axiom == "POW") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::POW.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "POW1") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::POW1.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "binary_union") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::binary_union.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "binary_inter") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::binary_inter.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "union") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::bunion.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "inter") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    return QString(baxioms::inter.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .arg(BTypeToSMTString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .toStdString();
  } else if (axiom == "apply") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    BType ltype = inty.toProductType().lhs;
    BType rtype = inty.toProductType().rhs;
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", inty);
    return QString(baxioms::apply.c_str())
        .arg(BTypeToSMTString(ltype).c_str())
        .arg(BTypeToSMTString(rtype).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .toStdString();
  } else if (axiom == "ran") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    BType ltype = inty.toProductType().lhs;
    BType rtype = inty.toProductType().rhs;
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", inty);
    return QString(baxioms::ran.c_str())
        .arg(BTypeToSMTString(ltype).c_str())
        .arg(BTypeToSMTString(rtype).c_str())
        .arg(axiom_generator.getTypeSuffixString(ltype).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .toStdString();
  } else if (axiom == "dom") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    BType ltype = inty.toProductType().lhs;
    BType rtype = inty.toProductType().rhs;
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", inty);
    return QString(baxioms::dom.c_str())
        .arg(BTypeToSMTString(ltype).c_str())
        .arg(BTypeToSMTString(rtype).c_str())
        .arg(axiom_generator.getTypeSuffixString(rtype).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .toStdString();
  } else if (axiom == "id") {
    assert(type.getKind() == BType::Kind::PowerType);
    BType inty = type.toPowerType().content;
    BType ctype = BType::PROD(inty, inty);
    ///@todo comment gérer cette dépendance à mem avec un autre type ?
    addSymbol("mem", ctype);
    addSymbol("mem", inty);
    return QString(baxioms::id.c_str())
        .arg(BTypeToSMTString(inty).c_str())
        .arg(axiom_generator.getTypeSuffixString(type).c_str())
        .arg(axiom_generator.getTypeSuffixString(ctype).c_str())
        .arg(axiom_generator.getTypeSuffixString(inty).c_str())
        .toStdString();
  } else {
    return "; TODO " + axiom;
  }
}

string PreludeBuilder::getAxiomatisation(const string axiom, const BType &typel,
                                         const BType &typer) {
  if (axiom == "prj1") {
    const BType t = BType::PROD(typel, typer);

    return QString(baxioms::mem.c_str())
               .arg(BTypeToSMTString(t).c_str())
               .arg(axiom_generator.getTypeSuffixString(t).c_str())
               .toStdString() +
           QString(baxioms::prj1.c_str())
               .arg(BTypeToSMTString(typel).c_str())
               .arg(axiom_generator.getTypeSuffixString(typel).c_str())
               .arg(BTypeToSMTString(typer).c_str())
               .arg(axiom_generator.getTypeSuffixString(typer).c_str())
               .arg(axiom_generator.getTypeSuffixString(t).c_str())
               .toStdString();
  } else if (axiom == "prj2") {
    const BType t = BType::PROD(typel, typer);

    return QString(baxioms::mem.c_str())
               .arg(BTypeToSMTString(t).c_str())
               .arg(axiom_generator.getTypeSuffixString(t).c_str())
               .toStdString() +
           QString(baxioms::prj2.c_str())
               .arg(BTypeToSMTString(typel).c_str())
               .arg(axiom_generator.getTypeSuffixString(typel).c_str())
               .arg(BTypeToSMTString(typer).c_str())
               .arg(axiom_generator.getTypeSuffixString(typer).c_str())
               .arg(axiom_generator.getTypeSuffixString(t).c_str())
               .toStdString();
  } else {
    return "; TODO " + axiom;
  }
}

string PreludeBuilder::addSymbol(const string symb) {
  // add symb to declarations
  std::vector<string> deps = axiom_generator.getDependencies(symb);
  for (auto axiom_schema : deps) {
    string instancied_axiom = getAxiomatisation(axiom_schema);
    addDeclaration(instancied_axiom);
  }
  return symb;
};

string PreludeBuilder::addSymbol(const string symb, const BType &type) {
  // add symb to declarations
  std::vector<string> deps = axiom_generator.getDependencies(symb);
  for (auto axiom_schema : deps) {
    string instancied_axiom = getAxiomatisation(axiom_schema, type);
    addDeclaration(instancied_axiom);
  }
  return symb + axiom_generator.getTypeSuffixString(type);
};

string PreludeBuilder::addSymbol(const string symb, const BType &typel,
                                 const BType &typer) {
  // add symb to declarations
  std::vector<string> deps = axiom_generator.getDependencies(symb);
  for (auto axiom_schema : deps) {
    string instancied_axiom = getAxiomatisation(axiom_schema, typel, typer);
    addDeclaration(instancied_axiom);
  }
  return symb + axiom_generator.getTypeSuffixString(typel);
};

string PreludeBuilder::addADTSymbol(const BType &type) {
  SmtADT adt = SmtADTFromBType(type);
  for (auto &it : adtSymbols) {
    if (it == adt) return it.getName();
  };
  adtSymbols.push_back(adt);
  addDeclaration(adt.getDeclaration());
  return adt.getName();
}

string PreludeBuilder::addEnumADT(const pog::Set &s) {
  SmtADT adt;
  adt.name = "enumerated_set_" + s.setName.name.show();
  adt.arity = 0;
  adt.constructor_name = "";
  adt.selectors = {};
  for (auto e : s.elts) adt.selectors.push_back(e.name.show());
  adtSymbols.push_back(adt);
  addDeclaration(adt.getDeclaration());
  return adt.getName();
}

string PreludeBuilder::addSort(const string &name, int arity) {
  string res_name = "aset_" + name;
  addDeclaration("(declare-sort " + res_name + " " + std::to_string(arity) +
                 ")");
  return res_name;
}

string PreludeBuilder::addComprehensionSet(const Expr::QuantifiedSet &,
                                           const string varname, const BType &t,
                                           const string pred) {
  string set_name = "cset_" + std::to_string(comprehension_sets++);
  addDeclaration("(declare-const " + set_name + " (P " + BTypeToSMTString(t) +
                 "))");

  string quant = "forall ((" + varname + " " + BTypeToSMTString(t) + "))";

  addDeclaration("(assert (" + quant + "\n  (=\n    (mem" +
                 axiom_generator.getTypeSuffixString(t) + " " + varname + " " +
                 set_name + ")\n    " + pred + "\n  )\n))");
  return set_name;
}

void PreludeBuilder::addDeclaration(const string decl) {
  for (size_t i = 0; i < declarations.size(); i++)
    if (decl == declarations.at(i)) return;
  declarations.push_back(decl);
}

string PreludeBuilder::getPrelude() const {
  string res = "";
  for (string d : declarations) res += d + "\n";
  return res;
}

}  // namespace preludebuilder
