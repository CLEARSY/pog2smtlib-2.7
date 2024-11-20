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
#include "smtlib.h"
#include "prelude_builder.h"
#include "utils.h"

#include "exprDesc.h"
#include "predDesc.h"
#include <QFileInfo>
#include <fstream>
#include <iostream>
#include <map>
#include <set>

namespace smtlib {

class SmtFunDecl {
public:
    SmtFunDecl(smtlib::Logic logic) : logic{logic} {};
    std::string addConstant(const Expr &e);
    std::string addFunction(int nbParams);
    std::string addAxiom(const std::string str);
    std::string addAxiom(const std::string symbol, const BType &type);
    std::string addAxiom(const std::string symbol, const BType &typel,
                         const BType &typer);
    std::string addSort(const std::string &name);
    std::string AddEnumeratedSet(const pog::Set &s);
    std::string addComprehensionSet(const Expr::QuantifiedSet &p,
                                    const string s);
    std::string typeToString(const BType &type);
    const std::map<std::string, std::string> &getSmtLibDeclarations() const {
        return smtLibDeclarations;
    };
    const std::string getAxioms() const { return prelude.getPrelude(); }
    smtlib::Logic getLogic() const { return logic; };

private:
    smtlib::Logic logic;
    std::set<std::string> fieldNames = {};
    std::map<Expr, std::string> cSymbols = {};
    std::vector<std::pair<std::string, int>> fSymbols = {};
    std::map<std::string, std::string> smtLibDeclarations = {};
    preludebuilder::PreludeBuilder prelude = preludebuilder::PreludeBuilder();
};

std::string varNameToString(const VarName &v) {
    // TODO: compatible avec counter-example reader ?
    switch (v.kind()) {
    case VarName::Kind::NoSuffix:
        return v.prefix();
    case VarName::Kind::WithSuffix:
        return v.prefix() + "$" + std::to_string(v.suffix());
    case VarName::Kind::FreshId:
    case VarName::Kind::Tmp:
        assert(false);
    }
    assert(false); // unreachable
}

///@todo Gérer des expressions de plusieurs types
std::string getExprType(smtlib::Logic logic) {
    return "U";
    switch (logic) {
    case smtlib::Logic::UF:
    case smtlib::Logic::QF_UF:
        return "U";
    case smtlib::Logic::UFNIA:
    case smtlib::Logic::QF_UFNIA:
        return "Int";
    case smtlib::Logic::UFNRA:
    case smtlib::Logic::QF_UFNRA:
        return "Real";
    };
    assert(false); // unreachable
};

std::string SmtFunDecl::AddEnumeratedSet(const pog::Set &f) {
    return prelude.addEnumADT(f);
}

string SmtFunDecl::addSort(const std::string &name) {
    return prelude.addSort(name, 0);
}

string SmtFunDecl::addComprehensionSet(const Expr::QuantifiedSet &p,
                                       const string s) {
    string vname =
        addConstant(Expr::makeIdent(p.vars.at(0).name, p.vars.at(0).type));
    return prelude.addComprehensionSet(p, vname, p.vars.at(0).type, s);
}

string SmtFunDecl::addAxiom(const std::string symbol) {
    return prelude.addSymbol(symbol);
}

string SmtFunDecl::addAxiom(const std::string symbol, const BType &type) {
    return prelude.addSymbol(symbol, type);
}

string SmtFunDecl::addAxiom(const std::string symbol, const BType &typel,
                            const BType &typer) {
    return prelude.addSymbol(symbol, typel, typer);
}

string SmtFunDecl::typeToString(const BType &type) {
    return prelude.BTypeToSMTString(type);
}

std::string SmtFunDecl::addConstant(const Expr &e) {
    auto it = cSymbols.find(e);
    if (it == cSymbols.end()) {
        std::string s;
        if (e.getTag() == Expr::EKind::Id)
            s = "g_" + varNameToString(e.getId()) + "_" +
                std::to_string(cSymbols.size());
        else
            s = "e" + std::to_string(cSymbols.size());
        cSymbols[e.copy()] = s;
        smtLibDeclarations[s] =
            "(declare-const " + s + " " + typeToString(e.getType()) + ")";
        return s;
    } else {
        return it->second;
    }
};

///@todo toujours nécessaire avec les structs en ADT ?
std::string SmtFunDecl::addFunction(int nbParams) {
    std::string res = "f" + std::to_string(fSymbols.size());
    fSymbols.push_back({res, nbParams});
    ///@todo types
    std::string type = getExprType(logic);
    std::string args = "";
    for (int i = 0; i < nbParams; i++)
        args += " " + type;
    smtLibDeclarations[res] =
        "(declare-fun " + res + " (" + args + " ) " + type + ")";
    return res;
};

std::string unaryExprOpToSmtString(const Expr::UnaryExpr &e,
                                   SmtFunDecl &decls) {
    switch (e.op) {
    case Expr::UnaryOp::IMinus:
    case Expr::UnaryOp::RMinus:
        return "-";
    case Expr::UnaryOp::IMaximum:
        return decls.addAxiom("imax");
    case Expr::UnaryOp::RMaximum:
        return decls.addAxiom("rmax");
    case Expr::UnaryOp::IMinimum:
        return decls.addAxiom("imin");
    case Expr::UnaryOp::RMinimum:
        return decls.addAxiom("rmin");
    case Expr::UnaryOp::Cardinality:
        return "card";
    case Expr::UnaryOp::Domain:
        return decls.addAxiom("dom", e.content.getType());
    case Expr::UnaryOp::Range:
        return decls.addAxiom("ran", e.content.getType());
    case Expr::UnaryOp::Subsets:
        return decls.addAxiom("POW", e.content.getType());
    case Expr::UnaryOp::Non_Empty_Subsets:
        return decls.addAxiom("POW1", e.content.getType());
    case Expr::UnaryOp::Finite_Subsets:
        return decls.addAxiom("FIN", e.content.getType());
    case Expr::UnaryOp::Non_Empty_Finite_Subsets:
        return decls.addAxiom("FIN1", e.content.getType());
    case Expr::UnaryOp::Union:
        return decls.addAxiom("union", e.content.getType());
    case Expr::UnaryOp::Intersection:
        return decls.addAxiom("inter", e.content.getType());
    case Expr::UnaryOp::Sequences:
        return "seq";
    case Expr::UnaryOp::Non_Empty_Sequences:
        return "seq1";
    case Expr::UnaryOp::Injective_Sequences:
        return "iseq";
    case Expr::UnaryOp::Non_Empty_Injective_Sequences:
        return "iseq1";
    case Expr::UnaryOp::Inverse:
        return "inverse";
    case Expr::UnaryOp::Size:
        return "size";
    case Expr::UnaryOp::Permutations:
        return "perm";
    case Expr::UnaryOp::First:
        return "first";
    case Expr::UnaryOp::Last:
        return "last";
    case Expr::UnaryOp::Identity:
        return decls.addAxiom("id", e.content.getType());
    case Expr::UnaryOp::Closure:
        return "closure";
    case Expr::UnaryOp::Transitive_Closure:
        return "closure1";
    case Expr::UnaryOp::Tail:
        return "tail";
    case Expr::UnaryOp::Front:
        return "front";
    case Expr::UnaryOp::Reverse:
        return "reverse";
    case Expr::UnaryOp::Concatenation:
        return "conc";
    case Expr::UnaryOp::Rel:
        return "rel";
    case Expr::UnaryOp::Fnc:
        return "fnc";
    case Expr::UnaryOp::Real:
        return decls.addAxiom("real");
    case Expr::UnaryOp::Floor:
        return decls.addAxiom("floor");
    case Expr::UnaryOp::Ceiling:
        return decls.addAxiom("ceiling");
    case Expr::UnaryOp::Tree:
    case Expr::UnaryOp::Btree:
    case Expr::UnaryOp::Top:
    case Expr::UnaryOp::Sons:
    case Expr::UnaryOp::Prefix:
    case Expr::UnaryOp::Postfix:
    case Expr::UnaryOp::Sizet:
    case Expr::UnaryOp::Mirror:
    case Expr::UnaryOp::Left:
    case Expr::UnaryOp::Right:
    case Expr::UnaryOp::Infix:
    case Expr::UnaryOp::Bin:
        throw SmtLibException("Tree constructs not supported.");
    };
    assert(false); // unreachable
};

std::string binaryExprOpToSmtString(const Expr::BinaryExpr &e,
                                    SmtFunDecl &decls) {
    switch (e.op) {
    case Expr::BinaryOp::IAddition:
    case Expr::BinaryOp::RAddition:
        return "+";
    case Expr::BinaryOp::FAddition:
        return "|+f|";
    case Expr::BinaryOp::IDivision:
        return "div";
    case Expr::BinaryOp::RDivision:
        return "/";
    case Expr::BinaryOp::FDivision:
        return "fdiv";
    case Expr::BinaryOp::Modulo:
        return "mod";
    case Expr::BinaryOp::ISubtraction:
    case Expr::BinaryOp::RSubtraction:
        return "-";
    case Expr::BinaryOp::FSubtraction:
        return "|-f|";
    case Expr::BinaryOp::Set_Difference:
        return decls.addAxiom("set_diff", e.lhs.getType());
    case Expr::BinaryOp::IMultiplication:
    case Expr::BinaryOp::RMultiplication:
        return "*";
    case Expr::BinaryOp::FMultiplication:
        return "|*f|";
    case Expr::BinaryOp::Cartesian_Product:
        return "set_prod";
    case Expr::BinaryOp::IExponentiation:
        return decls.addAxiom("iexp");
    case Expr::BinaryOp::RExponentiation:
        return decls.addAxiom("rexp");
    case Expr::BinaryOp::Mapplet:
        return "maplet";
    case Expr::BinaryOp::Partial_Functions:
        return "|+->|";
    case Expr::BinaryOp::Partial_Surjections:
        return "|+->>|";
    case Expr::BinaryOp::Total_Functions:
        return "|-->|";
    case Expr::BinaryOp::Total_Surjections:
        return "|-->>|";
    case Expr::BinaryOp::Head_Insertion:
        return "|->|";
    case Expr::BinaryOp::Interval:
        return decls.addAxiom("interval", e.lhs.getType());
    case Expr::BinaryOp::Intersection:
        return decls.addAxiom("binary_inter", e.lhs.getType());
    case Expr::BinaryOp::Head_Restriction:
        return "restriction_head";
    case Expr::BinaryOp::Composition:
        return "composition";
    case Expr::BinaryOp::Surcharge:
        return "|<+|";
    case Expr::BinaryOp::Relations:
        return "|<->|";
    case Expr::BinaryOp::Tail_Insertion:
        return "|<-|";
    case Expr::BinaryOp::Domain_Subtraction:
        return "domain_subtraction";
    case Expr::BinaryOp::Domain_Restriction:
        return "domain_restriction";
    case Expr::BinaryOp::Partial_Injections:
        return "|>+>|";
    case Expr::BinaryOp::Total_Injections:
        return "|>->|";
    case Expr::BinaryOp::Partial_Bijections:
        return "|>+>>|";
    case Expr::BinaryOp::Total_Bijections:
        return "|>->>|";
    case Expr::BinaryOp::Direct_Product:
        return "|><|";
    case Expr::BinaryOp::Parallel_Product:
        return "parallel_product";
    case Expr::BinaryOp::Union:
        return decls.addAxiom("binary_union", e.lhs.getType());
    case Expr::BinaryOp::Tail_Restriction:
        return "restriction_tail";
    case Expr::BinaryOp::Concatenation:
        return "concatenate";
    case Expr::BinaryOp::Range_Restriction:
        return "range_restriction";
    case Expr::BinaryOp::Range_Subtraction:
        return "range_subtraction";
    case Expr::BinaryOp::Image:
        return "image";
    case Expr::BinaryOp::Application:
        return decls.addAxiom("apply", e.lhs.getType());
    case Expr::BinaryOp::First_Projection:
        return decls.addAxiom("prj1", e.lhs.getType(), e.rhs.getType());
    case Expr::BinaryOp::Second_Projection:
        return decls.addAxiom("prj2", e.lhs.getType(), e.rhs.getType());
    case Expr::BinaryOp::Iteration:
        return "iterate";
    case Expr::BinaryOp::Const:
    case Expr::BinaryOp::Rank:
    case Expr::BinaryOp::Father:
    case Expr::BinaryOp::Subtree:
    case Expr::BinaryOp::Arity:
        throw SmtLibException("ppTrans: tree constructs not supported.");
    };
    assert(false); // unreachable
};

std::string exprToSmtLib(const Expr &f, SmtFunDecl &decls,
                         const std::set<VarName> &bv,
                         std::set<std::string> &used_ids);

/**
 * @brief predToSmtLib builds the string of an SMT predicate representing f
 * @param f
 * @param decls
 * @param bv
 * @param used_ids
 * @return
 */
std::string predToSmtLib(const Pred &f, SmtFunDecl &decls,
                         const std::set<VarName> &bv,
                         std::set<std::string> &used_ids) {
    switch (f.getTag()) {
    case Pred::PKind::True: {
        return "true";
    }
    case Pred::PKind::False: {
        return "false";
    }
    case Pred::PKind::Equivalence: {
        const Pred::Equivalence &p = f.toEquivalence();
        return "(= " + predToSmtLib(p.lhs, decls, bv, used_ids) + " " +
               predToSmtLib(p.rhs, decls, bv, used_ids) + ")";
    }
    case Pred::PKind::Implication: {
        const Pred::Implication &p = f.toImplication();
        return "(=> " + predToSmtLib(p.lhs, decls, bv, used_ids) + " " +
               predToSmtLib(p.rhs, decls, bv, used_ids) + ")";
    }
    case Pred::PKind::ExprComparison: {
        const Pred::ExprComparison &p = f.toExprComparison();
        if (p.op == Pred::ComparisonOp::Membership) {
            if (p.rhs.getTag() == Expr::EKind::BinaryExpr) {
                const Expr::BinaryExpr &rhs = p.rhs.toBinaryExpr();
                if (rhs.op == Expr::BinaryOp::Interval)
                    return "(" + decls.addAxiom("mem", p.lhs.getType()) + " " +
                           exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                           exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
            } else if (p.rhs.getTag() == Expr::EKind::NaryExpr) {
                const Expr::NaryExpr &rhs = p.rhs.toNaryExpr();
                if (rhs.op == Expr::NaryOp::Set) {
                    // a: {x,y,z} ----> a=x or a=y or a=z
                    std::string a = exprToSmtLib(p.lhs, decls, bv, used_ids);
                    if (rhs.vec.size() == 0)
                        return "false";
                    else if (rhs.vec.size() == 1)
                        return "(= " + a + " " +
                               exprToSmtLib(rhs.vec.at(0), decls, bv,
                                            used_ids) +
                               ")";
                    else {
                        std::string accu = "(or";
                        for (auto &e : rhs.vec)
                            accu += " (= " + a + " " +
                                    exprToSmtLib(e, decls, bv, used_ids) + ")";
                        return accu + ")";
                    }
                }
            }
        }

        switch (p.op) {
        case Pred::ComparisonOp::Equality: {
            std::string symb =
                (p.lhs.getType().getKind() == BType::Kind::PowerType)
                    ? decls.addAxiom("set_eq", p.lhs.getType())
                    : "=";
            return "(" + symb + " " + exprToSmtLib(p.lhs, decls, bv, used_ids) +
                   " " + exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
        case Pred::ComparisonOp::Membership:
            return "(" + decls.addAxiom("mem", p.lhs.getType()) + " " +
                   exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";

        case Pred::ComparisonOp::Subset:
            return "(" + decls.addAxiom("subset", p.lhs.getType()) + " " +
                   exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";

        case Pred::ComparisonOp::Strict_Subset:
            return "(" + decls.addAxiom("strict_subset", p.lhs.getType()) +
                   " " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";

        case Pred::ComparisonOp::Ige:
        case Pred::ComparisonOp::Rge: {
            return "(>= " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
        case Pred::ComparisonOp::Fge:
            return "(|>=f| " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";

        case Pred::ComparisonOp::Igt:
        case Pred::ComparisonOp::Rgt: {
            return "(> " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
        case Pred::ComparisonOp::Fgt:
            return "(|>f| " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        case Pred::ComparisonOp::Rlt:
        case Pred::ComparisonOp::Ilt: {
            return "(< " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
        case Pred::ComparisonOp::Flt:
            return "(|<f| " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        case Pred::ComparisonOp::Rle:
        case Pred::ComparisonOp::Ile: {
            return "(<= " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
        case Pred::ComparisonOp::Fle:
            return "(|<=f| " + exprToSmtLib(p.lhs, decls, bv, used_ids) + " " +
                   exprToSmtLib(p.rhs, decls, bv, used_ids) + ")";
        }
    }
    case Pred::PKind::Negation: {
        const Pred::NegationPred &p = f.toNegation();
        return "(not " + predToSmtLib(p.operand, decls, bv, used_ids) + ")";
    }
    case Pred::PKind::Conjunction: {
        const Pred::Conjunction &p = f.toConjunction();
        if (p.operands.size() == 0)
            return "true";
        if (p.operands.size() == 1)
            return predToSmtLib(p.operands.at(0), decls, bv, used_ids);
        std::string accu;
        for (auto &e : p.operands) {
            accu += " " + predToSmtLib(e, decls, bv, used_ids);
        }
        return "(and" + accu + ")";
    }
    case Pred::PKind::Disjunction: {
        const Pred::Disjunction &p = f.toDisjunction();
        if (p.operands.size() == 0)
            return "false";
        if (p.operands.size() == 1)
            return predToSmtLib(p.operands.at(0), decls, bv, used_ids);
        std::string accu;
        for (auto &e : p.operands) {
            accu += " " + predToSmtLib(e, decls, bv, used_ids);
        }
        return "(or" + accu + ")";
    }
    case Pred::PKind::Forall: {
        const Pred::Forall &p = f.toForall();
        std::string vs;
        auto &vars = p.vars;
        std::set<VarName> bv2 = bv;
        for (auto &v : vars) {
            vs += "(l_" + varNameToString(v.name) + " " +
                  decls.typeToString(v.type) + ")";
            bv2.insert(v.name);
        }
        return "(forall (" + vs + ") " +
               predToSmtLib(p.body, decls, bv2, used_ids) + ")";
    }
    case Pred::PKind::Exists: {
        const Pred::Exists &p = f.toExists();
        std::string vs;
        auto &vars = p.vars;
        std::set<VarName> bv2 = bv;
        for (auto &v : vars) {
            vs += "(l_" + varNameToString(v.name) + " " +
                  decls.typeToString(v.type) + ")";
            bv2.insert(v.name);
        }
        return "(exists (" + vs + ") " +
               predToSmtLib(p.body, decls, bv2, used_ids) + ")";
    }
    };
    assert(false); // unreachable
};

std::string exprToSmtLib(const Expr &f, SmtFunDecl &decls,
                         const std::set<VarName> &bv,
                         std::set<std::string> &used_ids) {
    switch (f.getTag()) {
    case Expr::EKind::BOOL:
        return "Bool";
    case Expr::EKind::FALSE:
        return "false";
    case Expr::EKind::TRUE:
        return "true";
    case Expr::EKind::INT:
        return decls.addAxiom("INT");
    case Expr::EKind::INTEGER:
        return decls.addAxiom("INTEGER");
    case Expr::EKind::NAT:
        return decls.addAxiom("NAT");
    case Expr::EKind::NAT1:
        return decls.addAxiom("NAT1");
    case Expr::EKind::NATURAL:
        return decls.addAxiom("NATURAL");
    case Expr::EKind::NATURAL1:
        return decls.addAxiom("NATURAL1");
    case Expr::EKind::FLOAT:
        return decls.addAxiom("FLOAT");
    case Expr::EKind::MaxInt:
        return decls.addAxiom("MaxInt");
    case Expr::EKind::MinInt:
        return decls.addAxiom("MinInt");
    case Expr::EKind::STRING:
        return decls.addAxiom("STRING");
    case Expr::EKind::REAL:
        return decls.addAxiom("REAL");
    case Expr::EKind::Successor:
        return decls.addAxiom("succ");
    case Expr::EKind::Predecessor:
        return decls.addAxiom("pred");

    case Expr::EKind::Record_Field_Access: {
        const Expr::RecordAccessExpr &e = f.toRecordAccess();
        return "(" + e.label + " " + exprToSmtLib(e.rec, decls, bv, used_ids) +
               ")";
    }

    case Expr::EKind::BinaryExpr: {
        const Expr::BinaryExpr &e = f.toBinaryExpr();
        std::string op_str = binaryExprOpToSmtString(e, decls);
        return "(" + op_str + " " + exprToSmtLib(e.lhs, decls, bv, used_ids) +
               " " + exprToSmtLib(e.rhs, decls, bv, used_ids) + ")";
    }

    case Expr::EKind::NaryExpr: {
        const Expr::NaryExpr &e = f.toNaryExpr();
        if (e.vec.size() == 0)
            return "empty";

        bool is_first = true;
        std::string accu;
        for (auto &ee : e.vec) {
            if (is_first) {
                accu = exprToSmtLib(ee, decls, bv, used_ids);
                is_first = false;
            } else {
                accu = "(maplet " + exprToSmtLib(ee, decls, bv, used_ids) +
                       " " + accu + ")";
            }
        }
        switch (e.op) {
        case Expr::NaryOp::Set:
            return "(SET " + accu + ")";
        case Expr::NaryOp::Sequence:
            return "(SEQ " + accu + ")";
        };
    }

    case Expr::EKind::BooleanExpr:
        return "(" + predToSmtLib(f.toBooleanExpr(), decls, bv, used_ids) + ")";

    case Expr::EKind::EmptySet:
        return "empty";

    case Expr::EKind::Id: {
        VarName v = f.getId();
        if (bv.find(v) != bv.end())
            return "l_" + varNameToString(v);
        std::string s = decls.addConstant(f);
        used_ids.insert(s);
        return s;
    }

    case Expr::EKind::IntegerLiteral: {
        const std::string lit = f.getIntegerLiteral();
        if (lit.at(0) == '-')
            return "(- " + lit.substr(1, std::string::npos) + ")";
        else
            return lit;
    }

    case Expr::EKind::RealLiteral: {
        auto &d = f.getRealLiteral();
        return d.integerPart + "." + d.fractionalPart;
    }
    case Expr::EKind::UnaryExpr: {
        const Expr::UnaryExpr &e = f.toUnaryExpr();
        return "(" + unaryExprOpToSmtString(e, decls) + " " +
               exprToSmtLib(e.content, decls, bv, used_ids) + ")";
    }

    case Expr::EKind::QuantifiedSet: {
        const Pred &cond = f.toQuantifiedSet().cond;
        string pred = predToSmtLib(cond, decls, bv, used_ids);
        return decls.addComprehensionSet(f.toQuantifiedSet(), pred);
    }
    case Expr::EKind::QuantifiedExpr:
    case Expr::EKind::StringLiteral:
    case Expr::EKind::Struct:
    case Expr::EKind::Record:
    case Expr::EKind::Record_Field_Update: {
        if (bv.size() == 0) {
            std::string s = decls.addConstant(f);
            used_ids.insert(s);
            return s;
        }
        std::set<VarName> fv;
        for (auto &v : f.getFreeVars()) {
            if (bv.find(v) != bv.end())
                fv.insert(v);
        }
        if (fv.size() == 0) {
            std::string s = decls.addConstant(f);
            used_ids.insert(s);
            return s;
        }

        std::string vars;
        for (auto &v : fv)
            vars += " l_" + varNameToString(v);
        std::string f = decls.addFunction(fv.size());
        used_ids.insert(f);
        return "(" + f + vars + ")";
    };
    case Expr::EKind::TernaryExpr: {
        throw SmtLibException("Tree constructs not supported.");
    }
    };
    assert(false); // unreachable
}

// déclarer un set ?
std::string setToSmtLib(const pog::Set &f, SmtFunDecl &decls,
                        std::set<std::string> &used_ids) {
    std::string id =
        decls.addConstant(Expr::makeIdent(f.setName.name, f.setName.type));
    used_ids.insert(id);

    if (f.elts.size() == 0) {
        // abstract set
        return decls.addSort(f.setName.name.show());
    } else {
        // enumerated set
        return decls.AddEnumeratedSet(f);
    }
}

// Version non incrementale
using translation_t = std::pair<std::string, std::set<std::string>>;

translation_t defToSmtLib(SmtFunDecl &decls,
                          const std::vector<pog::Define> &vec,
                          const std::string &d) {
    int pos = -1;
    for (int i = 0; i < vec.size(); i++) {
        if (vec[i].name == d) {
            pos = i;
            break;
        }
    }
    assert(pos >= 0);
    std::string fm;
    int nbChildren = 0;
    std::set<std::string> used_ids;
    for (const auto &c : vec[pos].contents) {
        if (std::holds_alternative<pog::Set>(c)) {
            // Ce sont les abstract sets
            fm += " " + setToSmtLib(std::get<pog::Set>(c), decls, used_ids);
        } else {
            fm += " " + predToSmtLib(std::get<Pred>(c), decls, {}, used_ids);
        }
        nbChildren++;
    }
    switch (nbChildren) {
    case 0:
        return {"; Definition " + vec[pos].name + " = true", used_ids};
    case 1:
        return {"; Definition " + vec[pos].name + "\n(assert " + fm + ")",
                used_ids};
    default:
        return {"; Definition " + vec[pos].name + "\n(assert (and" + fm + "))",
                used_ids};
    }
}

void merge(std::set<std::string> &set, const std::set<std::string> &to_insert) {
    for (auto &e : to_insert)
        set.insert(e);
}

/**
 * @brief writeNonIncrOutput outputs a non-incremental SMT2 script to file
 * @param decls
 * @param defines
 * @param globalHyps
 * @param used_ids0
 * @param localHyps
 * @param localHyps_tr
 * @param groupTag
 * @param groupId PO group index in the source POG file
 * @param goalId simple goal index in the source POG file
 * @param sg
 * @param baseName base name of the output file
 */
void writeNonIncrOutput(SmtFunDecl &decls,
                        const std::vector<std::string> &defines,
                        const std::vector<std::string> &globalHyps,
                        const std::set<std::string> &used_ids0,
                        const std::vector<Pred> &localHyps,
                        std::map<int, translation_t> &localHyps_tr,
                        const std::string &groupTag, int groupId, int goalId,
                        const pog::PO &sg, const std::string &filename,
                        bool produce_model) {
    std::set<std::string> used_ids{used_ids0};
    for (auto &ref : sg.localHypsRef) {
        auto it = localHyps_tr.find(ref);
        if (it != localHyps_tr.end()) {
            merge(used_ids, it->second.second);
        } else {
            std::set<std::string> used_ids2;
            std::string s =
                predToSmtLib(localHyps[ref - 1], decls, {}, used_ids2);
            localHyps_tr[ref] = {s, used_ids2};
            merge(used_ids, used_ids2);
        }
    }
    std::string goal = predToSmtLib(sg.goal, decls, {}, used_ids);

    std::ofstream out;
    out.open(filename);
    out << "(set-option :print-success false)\n";
    if (produce_model)
        out << "(set-option :produce-models true)\n";
    out << "(set-logic ALL)\n";
    out << "; PO " << groupId << " " << goalId << " \n";
    out << "; Group " << groupTag << "\n";
    out << "; Tag " << sg.tag << "\n";
    out << "; Prelude\n";
    out << decls.getAxioms();
    out << "; Opaque formulas\n";
    for (auto &s : used_ids)
        out << decls.getSmtLibDeclarations().find(s)->second << std::endl;
    out << "; Defines\n";
    for (auto &d : defines)
        out << d << "\n";
    out << "; Global hypotheses\n";
    for (auto &hyp : globalHyps)
        out << "(assert " << hyp << ")\n";
    out << "; Local hypotheses\n";
    for (auto &ref : sg.localHypsRef)
        out << "(assert " << localHyps_tr.find(ref)->second.first << ")\n";
    out << "; Goal\n";
    out << "(assert (not " << goal << "))\n";
    out << "(check-sat)\n";
    if (produce_model)
        out << "(get-model)\n";
    out << "(exit)";
    out.close();
}

/**
 * @brief prepareNonIncrOutput
 * @param decls
 * @param all_defines
 * @param all_defines_tr
 * @param group
 * @param used_ids
 * @param defines
 * @param globalHyps
 */
void prepareNonIncrOutput(SmtFunDecl &decls,
                          const std::vector<pog::Define> &all_defines,
                          std::map<std::string, translation_t> &all_defines_tr,
                          const pog::POGroup &group,
                          std::set<std::string> &used_ids,
                          std::vector<std::string> &defines,
                          std::vector<std::string> &globalHyps) {
    // Defines
    for (auto &d : group.definitions) {
        if (d == "B definitions")
            continue;
        auto it{all_defines_tr.find(d)};
        if (it != all_defines_tr.end()) {
            defines.push_back(it->second.first);
            merge(used_ids, it->second.second);
        } else {
            auto s{defToSmtLib(decls, all_defines, d)};
            all_defines_tr[d] = s;
            defines.push_back(s.first);
            merge(used_ids, s.second);
        }
    }
    // Global hypotheses
    for (auto &hyp : group.hyps)
        globalHyps.push_back(predToSmtLib(hyp, decls, {}, used_ids));
}

/**
 * @brief saveSmtLibFileNonIncrGroup sucessively converts to SMT2 and save to
 * file the given goals from group.
 * @param decls
 * @param all_defines
 * @param all_defines_tr
 * @param groupId index of the PO group in the source POG file
 * @param group
 * @param goals indices of the selected goals in the source POG file, or nil.
 * @param baseName
 */
void saveSmtLibFileNonIncrGroupSome(
    SmtFunDecl &decls, const std::vector<pog::Define> &all_defines,
    std::map<std::string, translation_t> &all_defines_tr, int groupId,
    const pog::POGroup &group, const std::vector<int> goals,
    const std::string &baseName, bool produce_model) {
    std::set<std::string> used_ids;
    std::vector<std::string> defines;
    std::vector<std::string> globalHyps;
    prepareNonIncrOutput(decls, all_defines, all_defines_tr, group, used_ids,
                         defines, globalHyps);

    // Simple goals
    std::map<int, translation_t> localHyps_tr;
    std::string prefix{utils::absoluteBasename(baseName) + "_" +
                       std::to_string(groupId) + "_"};
    for (auto i : goals) {
        std::string filename{prefix + std::to_string(i) + ".smt2"};
        writeNonIncrOutput(decls, defines, globalHyps, used_ids,
                           group.localHyps, localHyps_tr, group.tag, groupId, i,
                           group.simpleGoals[i], filename, produce_model);
    }
}

/**
 * @brief saveSmtLibFileNonIncrGroup sucessively converts to SMT2 and save
 * to file the given goals from group.
 * @param decls
 * @param all_defines
 * @param all_defines_tr
 * @param groupId index of the PO group in the source POG file
 * @param group
 * @param goals indices of the selected goals in the source POG file, or
 * nil.
 * @param baseName
 */
void saveSmtLibFileNonIncrGroupAll(
    SmtFunDecl &decls, const std::vector<pog::Define> &all_defines,
    std::map<std::string, translation_t> &all_defines_tr, int groupId,
    const pog::POGroup &group, const std::string &baseName,
    bool produce_model) {
    std::set<std::string> used_ids;
    // Defines
    std::vector<std::string> defines;
    std::vector<std::string> globalHyps;
    prepareNonIncrOutput(decls, all_defines, all_defines_tr, group, used_ids,
                         defines, globalHyps);

    // Simple goals
    std::map<int, translation_t> localHyps_tr;
    std::string prefix{utils::absoluteBasename(baseName) + "_" +
                       std::to_string(groupId) + "_"};
    for (int i = 0; i < group.simpleGoals.size(); i++) {
        std::string filename{prefix + std::to_string(i) + ".smt2"};
        writeNonIncrOutput(decls, defines, globalHyps, used_ids,
                           group.localHyps, localHyps_tr, group.tag, groupId, i,
                           group.simpleGoals[i], filename, produce_model);
    }
}

void saveSmtLibFileNonIncrOne(Logic logic, const pog::Pog &pog, int groupId,
                              int goalId, const std::string &output,
                              bool produce_model) {
    using std::map;
    using std::set;
    using std::string;
    using std::to_string;
    using std::vector;

    SmtFunDecl decls(logic);
    const vector<pog::Define> &all_defines{pog.defines};
    map<string, translation_t> all_defines_tr;
    const pog::POGroup &group{pog.pos[groupId]};
    set<string> used_ids;
    vector<string> defines;
    vector<string> globalHyps;

    prepareNonIncrOutput(decls, all_defines, all_defines_tr, group, used_ids,
                         defines, globalHyps);
    string filename{utils::absoluteBasename(output) + "_" + to_string(groupId) +
                    "_" + to_string(goalId) + ".po2"};

    map<int, translation_t> localHyps_tr;
    writeNonIncrOutput(decls, defines, globalHyps, used_ids, group.localHyps,
                       localHyps_tr, group.tag, groupId, goalId,
                       group.simpleGoals[goalId], filename, produce_model);
}

// Version incrementale

std::string simpleGoalToSmtLib(const pog::PO &sg, SmtFunDecl &decls) {
    std::set<std::string> dummy;
    if (sg.localHypsRef.size() == 0)
        return predToSmtLib(sg.goal, decls, {}, dummy);

    if (sg.localHypsRef.size() == 1)
        return "(=> lh_" + std::to_string(sg.localHypsRef[0]) + " " +
               predToSmtLib(sg.goal, decls, {}, dummy) + ")";

    std::string accu = "(and";
    for (const auto &ref : sg.localHypsRef)
        accu += " lh_" + std::to_string(ref);
    return "(=> " + accu + ") " + predToSmtLib(sg.goal, decls, {}, dummy) + ")";
}

void writeSmtLibFileIncr(Logic logic, const pog::Pog &pog,
                         const std::string &filename, SmtFunDecl &decls,
                         const std::vector<Po> &pos, bool produce_model) {
    // Define Tags
    std::vector<std::string> defines;
    for (const auto &def : pog.defines) {
        std::string fm;
        int nbChildren = 0;
        for (const auto &c : def.contents) {
            std::set<std::string> dummy;
            if (std::holds_alternative<pog::Set>(c)) {
                fm += " " + setToSmtLib(std::get<pog::Set>(c), decls, dummy);
            } else {
                fm += " " + predToSmtLib(std::get<Pred>(c), decls, {}, dummy);
            }
            nbChildren++;
        }
        switch (nbChildren) {
        case 0:
            defines.push_back("(define-fun |def_" + def.name +
                              "| () Bool true)");
            break;
        case 1:
            defines.push_back("(define-fun |def_" + def.name + "| () Bool " +
                              fm + ")");
            break;
        default:
            defines.push_back("(define-fun |def_" + def.name +
                              "| () Bool (and" + fm + "))");
        }
    }

    std::ofstream out;
    out.open(filename);

    out << "(set-option :print-success false)\n";
    if (produce_model)
        out << "(set-option :produce-models true)\n";
    out << "(set-logic ALL)\n";
    out << "; Prelude\n";
    out << decls.getAxioms();
    out << "; Opaque formulas\n";
    for (auto &d : decls.getSmtLibDeclarations())
        out << d.second << "\n";
    out << "; Defines\n";
    for (auto &d : defines)
        out << d << "\n";
    for (Po po : pos) {
        out << "; PO group " << po.group << " \n";
        if (pos.size() > 1)
            out << "(push 1)\n";
        for (auto &def : po.definitions)
            out << "(assert |def_" << def << "|)\n";
        for (auto &hyp : po.hypotheses)
            out << "(assert " << hyp << ")\n";
        for (int i = 0; i < po.localHypotheses.size(); ++i)
            out << "(define-fun lh_" << (i + 1) << " () Bool "
                << po.localHypotheses[i] << ")\n";
        for (auto &sg : po.simpleGoals) {
            out << "; PO " << sg.first << " in group " << po.group << "\n";
            if (po.simpleGoals.size() > 1)
                out << "(push 1)\n";
            out << "(assert (not " << sg.second << "))\n";
            out << "(check-sat)\n";
            if (produce_model)
                out << "(get-model)\n";
            if (po.simpleGoals.size() > 1)
                out << "(pop 1)\n";
        }
        if (pos.size() > 1)
            out << "(pop 1)\n";
    }
    out << "(exit)";
    out.close();
}

void saveSmtLibFileIncrSome(Logic logic, const pog::Pog &pog,
                            const goal_selection_t &goals,
                            const std::string &filename, bool produce_model) {
    SmtFunDecl decls{logic};
    std::vector<Po> pos;

    for (int group = 0; group < pog.pos.size(); ++group) {
        auto it{goals.find(group)};
        if (it == goals.end())
            continue;
        auto &simple_goal_ids{it->second};
        if (simple_goal_ids.size() == 0)
            continue;
        const pog::POGroup &po = pog.pos[group];
        smtlib::Po smtPo;
        smtPo.group = group;
        smtPo.definitions = po.definitions;

        for (const auto &h : po.hyps) {
            std::set<std::string> dummy;
            smtPo.hypotheses.push_back(predToSmtLib(h, decls, {}, dummy));
        }

        for (const auto &h : po.localHyps) {
            std::set<std::string> dummy;
            smtPo.localHypotheses.push_back(predToSmtLib(h, decls, {}, dummy));
        }

        auto simple_goal_it{std::begin(simple_goal_ids)};
        for (int i = 0; i < po.simpleGoals.size(); i++) {
            if (simple_goal_it == simple_goal_ids.end())
                break;
            if (i == *simple_goal_it) {
                smtPo.simpleGoals.push_back(
                    {i + 1, simpleGoalToSmtLib(po.simpleGoals[i], decls)});
                ++simple_goal_it;
            }
        }
        pos.push_back(smtPo);
    }
    writeSmtLibFileIncr(logic, pog, filename, decls, pos, produce_model);
}

void saveSmtLibFileIncr(Logic logic, const pog::Pog &pog,
                        const std::string &filename, const bool produce_model) {
    SmtFunDecl decls{logic};
    std::vector<Po> pos;

    for (int group = 0; group < pog.pos.size(); ++group) {
        const pog::POGroup &po = pog.pos[group];
        smtlib::Po smtPo;
        smtPo.group = group;
        smtPo.definitions = po.definitions;

        for (const auto &h : po.hyps) {
            std::set<std::string> dummy;
            smtPo.hypotheses.push_back(predToSmtLib(h, decls, {}, dummy));
        }

        for (const auto &h : po.localHyps) {
            std::set<std::string> dummy;
            smtPo.localHypotheses.push_back(predToSmtLib(h, decls, {}, dummy));
        }

        for (int i = 0; i < po.simpleGoals.size(); i++) {
            smtPo.simpleGoals.push_back(
                {i + 1, simpleGoalToSmtLib(po.simpleGoals[i], decls)});
        }
        pos.push_back(smtPo);
    }
    writeSmtLibFileIncr(logic, pog, filename, decls, pos, produce_model);
}

void saveSmtLibFileNonIncr(Logic logic, const pog::Pog &pog,
                           const std::string &output, bool produce_model) {
    std::map<std::string, translation_t> all_defines_tr;
    SmtFunDecl decls(logic);
    for (int i = 0; i < pog.pos.size(); i++) {
        const int groupId{i};
        saveSmtLibFileNonIncrGroupAll(decls, pog.defines, all_defines_tr,
                                      groupId, pog.pos[groupId], output,
                                      produce_model);
    }
}
} // namespace smtlib
