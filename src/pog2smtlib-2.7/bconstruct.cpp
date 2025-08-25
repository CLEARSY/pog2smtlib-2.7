/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2025
  pog2smtlib-2.7 is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/
#include "bconstruct.h"

#include <fmt/core.h>

#include <functional>
#include <string>

#include "btype-symbols.h"
#include "btype.h"
#include "pred.h"
#include "signature.h"

namespace BConstruct {

using std::make_pair;
using std::make_shared;
using std::pair;
using std::shared_ptr;
using std::string;
using std::unordered_map;
using std::vector;

void Factory::index(shared_ptr<Abstract> construct) {
  construct->m_index = m_index.size();
  m_index.push_back(construct);
}

template <typename T> shared_ptr<Abstract> Factory::get(shared_ptr<T>& m) {
  if (m != nullptr) {
    return m;
  }
  m = std::make_shared<T>();
  index(m);
  return m;
}

template <typename T>
shared_ptr<Abstract> Factory::get(
    unordered_map<shared_ptr<const BType>, shared_ptr<T>, Factory::BTypeHash>&
        m,
    const BType& t) {
  shared_ptr<const BType> pt = std::make_shared<const BType>(t);
  auto it = m.find(pt);
  if (it != m.end()) {
    return it->second;
  }
  auto construct = std::make_shared<T>(t);
  m[pt] = construct;
  return construct;
}

template <typename T>
shared_ptr<Abstract> Factory::get(
    unordered_map<pair<shared_ptr<const BType>, shared_ptr<const BType>>,
                  shared_ptr<T>, Factory::BinaryBTypeHash>& m,
    const BType& tl, const BType& tr) {
  pair<shared_ptr<const BType>, shared_ptr<const BType>> pt =
      make_pair(make_shared<const BType>(tl), make_shared<const BType>(tr));
  auto it = m.find(pt);
  if (it != m.end()) {
    return it->second;
  }
  auto construct = make_shared<T>(tl, tr);
  m[pt] = construct;
  return construct;
}

template <typename T>
shared_ptr<Abstract> Factory::get(
    unordered_map<pair<pair<shared_ptr<const BType>, shared_ptr<const BType>>,
                       shared_ptr<const BType>>,
                  shared_ptr<T>, Factory::TernaryBTypeHash>& m,
    const BType& fst, const BType& snd, const BType& thd) {
  pair<pair<shared_ptr<const BType>, shared_ptr<const BType>>,
       shared_ptr<const BType>>
      pt = make_pair(make_pair(make_shared<const BType>(fst),
                               make_shared<const BType>(snd)),
                     make_shared<const BType>(thd));
  auto it = m.find(pt);
  if (it != m.end()) {
    return it->second;
  }
  auto construct = make_shared<T>(fst, snd, thd);
  m[pt] = construct;
  return construct;
}

template <typename T>
shared_ptr<Abstract> Factory::get(
    unordered_map<
        pair<pair<pair<shared_ptr<const BType>, shared_ptr<const BType>>,
                  shared_ptr<const BType>>,
             shared_ptr<const BType>>,
        shared_ptr<T>, Factory::NaryBTypeHash>& m,
    const BType& fst, const BType& snd, const BType& thd, const BType& fth) {
  pair<pair<pair<shared_ptr<const BType>, shared_ptr<const BType>>,
            shared_ptr<const BType>>,
       shared_ptr<const BType>>
      pt = make_pair(make_pair(make_pair(make_shared<const BType>(fst),
                                         make_shared<const BType>(snd)),
                               make_shared<const BType>(thd)),
                     make_shared<const BType>(fth));
  auto it = m.find(pt);
  if (it != m.end()) {
    return it->second;
  }
  auto construct = make_shared<T>(fst, snd, thd, fth);
  m[pt] = construct;
  return construct;
}

shared_ptr<Abstract> Factory::get(const struct Data& dt) {
  shared_ptr<const struct Data> pt = std::make_shared<const struct Data>(dt);
  auto it = m_data.find(pt);
  if (it != m_data.end()) {
    return it->second;
  }
  auto construct = std::make_shared<BConstruct::Expression::Data>(dt);
  m_data[pt] = construct;
  return construct;
}

/*
shared_ptr<Abstract> Factory::Type(const BType& t) {
  shared_ptr<const BType> pt = std::make_shared<const BType>(t);
  unordered_map<shared_ptr<const BType>,
                std::shared_ptr<BConstruct::Type::Type>, BTypeHash>& um =
      m_Types;
  auto it = um.find(pt);
  if (it != um.end()) {
    return it->second;
  }
  auto construct = std::make_shared<BConstruct::Type::Type>(t);
  um[pt] = construct;
  return construct;
}
*/

/* Type */

shared_ptr<Abstract> Factory::Type(const BType& t) {
  return get<BConstruct::Predicate::SetMembership>(m_SetMemberships, t);
}

shared_ptr<Abstract> Factory::PowerSet() {
  return get<BConstruct::Type::PowerSet>(m_PowerSet);
}

shared_ptr<Abstract> Factory::CartesianProduct() {
  return get<BConstruct::Type::CartesianProduct>(m_CartesianProduct);
}

/* Predicate */

shared_ptr<Abstract> Factory::SetMembership(const BType& t) {
  return get<BConstruct::Predicate::SetMembership>(m_SetMemberships, t);
}

shared_ptr<Abstract> Factory::Equality(const BType& t) {
  return get<BConstruct::Predicate::Equality>(m_Equalities, t);
}

shared_ptr<Abstract> Factory::Inclusion(const BType& t) {
  return get<BConstruct::Predicate::Inclusion>(m_Inclusions, t);
}

shared_ptr<Abstract> Factory::StrictInclusion(const BType& t) {
  return get<BConstruct::Predicate::StrictInclusion>(m_StrictInclusions, t);
}

shared_ptr<Abstract> Factory::NumberComparison() {
  return get<BConstruct::Predicate::NumberComparison>(m_NumberComparison);
}

/* 5.1 Primary Expressions */

shared_ptr<Abstract> Factory::BooleanExpression() {
  return get<BConstruct::Expression::BooleanExpression>(m_BooleanExpression);
}

shared_ptr<Abstract> Factory::Data(const struct Data& data) {
  return get(data);
}

/* 5.3 Arithmetical Expressions 1 */

shared_ptr<Abstract> Factory::Maxint() {
  return get<BConstruct::Expression::Maxint>(m_Maxint);
}

shared_ptr<Abstract> Factory::Minint() {
  return get<BConstruct::Expression::Minint>(m_Minint);
}

shared_ptr<Abstract> Factory::Addition() {
  return get<BConstruct::Expression::Addition>(m_Addition);
}

shared_ptr<Abstract> Factory::Subtraction() {
  return get<BConstruct::Expression::Subtraction>(m_Subtraction);
}

shared_ptr<Abstract> Factory::Multiplication() {
  return get<BConstruct::Expression::Multiplication>(m_Multiplication);
}

shared_ptr<Abstract> Factory::IntegerDivision() {
  return get<BConstruct::Expression::IntegerDivision>(m_IntegerDivision);
}

shared_ptr<Abstract> Factory::Floor() {
  return get<BConstruct::Expression::Floor>(m_Floor);
}

shared_ptr<Abstract> Factory::Ceiling() {
  return get<BConstruct::Expression::Ceiling>(m_Ceiling);
}

shared_ptr<Abstract> Factory::ToReal() {
  return get<BConstruct::Expression::ToReal>(m_ToReal);
}

shared_ptr<Abstract> Factory::Succ() {
  return get<BConstruct::Expression::Succ>(m_Succ);
}

shared_ptr<Abstract> Factory::Predecessor() {
  return get<BConstruct::Expression::Predecessor>(m_Predecessor);
}

/* 5.4 Arithmetical Expressions (continued) */

shared_ptr<Abstract> Factory::Max() {
  return get<BConstruct::Expression::Max>(m_Max);
}

shared_ptr<Abstract> Factory::Min() {
  return get<BConstruct::Expression::Min>(m_Min);
}

shared_ptr<Abstract> Factory::Cardinals() {
  return get<BConstruct::Expression::Cardinals>(m_Cardinals);
}

shared_ptr<Abstract> Factory::Card(const BType& t) {
  return get<BConstruct::Expression::Card>(m_Cards, t);
}

shared_ptr<Abstract> Factory::GeneralizedSum() {
  return get<BConstruct::Expression::GeneralizedSum>(m_GeneralizedSum);
}

shared_ptr<Abstract> Factory::GeneralizedProduct() {
  return get<BConstruct::Expression::GeneralizedProduct>(m_GeneralizedProduct);
}

/* 5.5 Expression of Couples */

shared_ptr<Abstract> Factory::Maplet() {
  return get<BConstruct::Expression::Maplet>(m_Maplet);
}

/* 5.6 Building Sets */

shared_ptr<Abstract> Factory::Integer() {
  return get<BConstruct::Expression::Integer>(m_Integer);
}

shared_ptr<Abstract> Factory::Real() {
  return get<BConstruct::Expression::Real>(m_Real);
}

shared_ptr<Abstract> Factory::Bool() {
  return get<BConstruct::Expression::Bool>(m_Bool);
}

shared_ptr<Abstract> Factory::EmptySet(const BType& t) {
  return get<BConstruct::Expression::EmptySet>(m_EmptySets, t);
}

shared_ptr<Abstract> Factory::Natural() {
  return get<BConstruct::Expression::Natural>(m_Natural);
}

shared_ptr<Abstract> Factory::Natural1() {
  return get<BConstruct::Expression::Natural1>(m_Natural1);
}

shared_ptr<Abstract> Factory::Nat() {
  return get<BConstruct::Expression::Nat>(m_Nat);
}

shared_ptr<Abstract> Factory::Nat1() {
  return get<BConstruct::Expression::Nat1>(m_Nat1);
}

shared_ptr<Abstract> Factory::Int() {
  return get<BConstruct::Expression::Int>(m_Int);
}

/* 5.7 Set List Expressions */

shared_ptr<Abstract> Factory::PowerSet(const BType& t) {
  return get<BConstruct::Expression::PowerSet>(m_PowerSets, t);
}

shared_ptr<Abstract> Factory::PowerSet1(const BType& t) {
  return get<BConstruct::Expression::PowerSet1>(m_PowerSet1s, t);
}

shared_ptr<Abstract> Factory::Interval() {
  return get<BConstruct::Expression::Interval>(m_Interval);
}

shared_ptr<Abstract> Factory::ExpressionCartesianProduct(const BType& t1,
                                                         const BType& t2) {
  return get<BConstruct::Expression::CartesianProduct>(
      m_ExpressionCartesianProducts, t1, t2);
}

shared_ptr<Abstract> Factory::Set(const BType& t) {
  return get<BConstruct::Expression::Set>(m_Sets, t);
}

shared_ptr<Abstract> Factory::Fin(const BType& t) {
  return get<BConstruct::Expression::Fin>(m_Fins, t);
}

shared_ptr<Abstract> Factory::Fin1(const BType& t) {
  return get<BConstruct::Expression::Fin1>(m_Fin1s, t);
}

/* 5.8 Set List Expressions (continued) */

shared_ptr<Abstract> Factory::Difference(const BType& t) {
  return get<BConstruct::Expression::Difference>(m_Differences, t);
}

shared_ptr<Abstract> Factory::Union(const BType& t) {
  return get<BConstruct::Expression::Union>(m_Unions, t);
}

shared_ptr<Abstract> Factory::Intersection(const BType& t) {
  return get<BConstruct::Expression::Intersection>(m_Intersections, t);
}

shared_ptr<Abstract> Factory::GeneralizedIntersection(const BType& t) {
  return get<BConstruct::Expression::GeneralizedIntersection>(
      m_GeneralizedIntersections, t);
}

shared_ptr<Abstract> Factory::GeneralizedUnion(const BType& t) {
  return get<BConstruct::Expression::GeneralizedUnion>(m_GeneralizedUnions, t);
}

shared_ptr<Abstract> Factory::Quantified_Union(const BType& lhs,
                                               const BType& rhs) {
  return get<BConstruct::Expression::Quantified_Union>(m_Quantified_Unions, lhs,
                                                       rhs);
}

shared_ptr<Abstract> Factory::Quantified_Intersection(const BType& lhs,
                                                      const BType& rhs) {
  return get<BConstruct::Expression::Quantified_Intersection>(
      m_Quantified_Intersections, lhs, rhs);
}

/* 5.10 Set of Relations */

shared_ptr<Abstract> Factory::Relation(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Relation>(m_Relations, lhs, rhs);
}

shared_ptr<Abstract> Factory::Total_Relation(const BType& lhs,
                                             const BType& rhs) {
  return get<BConstruct::Expression::Total_Relation>(m_Total_Relations, lhs,
                                                     rhs);
}

/* 5.11 Expressions of Relations */

shared_ptr<Abstract> Factory::Identity(const BType& t) {
  return get<BConstruct::Expression::Identity>(m_Identitys, t);
}

shared_ptr<Abstract> Factory::Reverse(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Reverse>(m_Reverses, lhs, rhs);
}

shared_ptr<Abstract> Factory::Prj1(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Prj1>(m_Prj1s, lhs, rhs);
}

shared_ptr<Abstract> Factory::Prj2(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Prj2>(m_Prj2s, lhs, rhs);
}

shared_ptr<Abstract> Factory::Composition(const BType& fst, const BType& snd,
                                          const BType& thd) {
  return get<BConstruct::Expression::Composition>(m_Compositions, fst, snd,
                                                  thd);
}

shared_ptr<Abstract> Factory::Direct_Product(const BType& fst, const BType& snd,
                                             const BType& thd) {
  return get<BConstruct::Expression::Direct_Product>(m_Direct_Products, fst,
                                                     snd, thd);
}

shared_ptr<Abstract> Factory::Parallel_Product(const BType& fst,
                                               const BType& snd,
                                               const BType& thd,
                                               const BType& fth) {
  return get<BConstruct::Expression::Parallel_Product>(m_Parallel_Products, fst,
                                                       snd, thd, fth);
}

/* 5.12 Expressions of Relations */

shared_ptr<Abstract> Factory::Iteration(const BType& t) {
  return get<BConstruct::Expression::Iteration>(m_Iterations, t);
}

shared_ptr<Abstract> Factory::Closure(const BType& t) {
  return get<BConstruct::Expression::Closure>(m_Closures, t);
}

shared_ptr<Abstract> Factory::Closure1(const BType& t) {
  return get<BConstruct::Expression::Closure1>(m_Closure1s, t);
}

/* 5.13 Expressions of Relations */

shared_ptr<Abstract> Factory::Domain(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Domain>(m_Domains, lhs, rhs);
}

shared_ptr<Abstract> Factory::Range(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Range>(m_Ranges, lhs, rhs);
}

shared_ptr<Abstract> Factory::Image(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Image>(m_Images, lhs, rhs);
}

/* 5.14 Expressions of Relations */

shared_ptr<Abstract> Factory::Restriction_Domain(const BType& lhs,
                                                 const BType& rhs) {
  return get<BConstruct::Expression::Restriction_Domain>(m_Restriction_Domains,
                                                         lhs, rhs);
}

shared_ptr<Abstract> Factory::Subtraction_Domain(const BType& lhs,
                                                 const BType& rhs) {
  return get<BConstruct::Expression::Subtraction_Domain>(m_Subtraction_Domains,
                                                         lhs, rhs);
}

shared_ptr<Abstract> Factory::Restriction_Range(const BType& lhs,
                                                const BType& rhs) {
  return get<BConstruct::Expression::Restriction_Range>(m_Restriction_Ranges,
                                                        lhs, rhs);
}

shared_ptr<Abstract> Factory::Subtraction_Range(const BType& lhs,
                                                const BType& rhs) {
  return get<BConstruct::Expression::Subtraction_Range>(m_Subtraction_Ranges,
                                                        lhs, rhs);
}

shared_ptr<Abstract> Factory::Overwrite(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Overwrite>(m_Overwrites, lhs, rhs);
}

/* 5.15 Sets of Functions */

shared_ptr<Abstract> Factory::Injection(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Injection>(m_Injections, lhs, rhs);
}

shared_ptr<Abstract> Factory::Surjection(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Surjection>(m_Surjections, lhs, rhs);
}

shared_ptr<Abstract> Factory::Bijection(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Bijection>(m_Bijections, lhs, rhs);
}

shared_ptr<Abstract> Factory::Function(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Function>(m_Functions, lhs, rhs);
}

shared_ptr<Abstract> Factory::Partial_Function(const BType& lhs,
                                               const BType& rhs) {
  return get<BConstruct::Expression::Partial_Function>(m_Partial_Functions, lhs,
                                                       rhs);
}

shared_ptr<Abstract> Factory::Total_Function(const BType& lhs,
                                             const BType& rhs) {
  return get<BConstruct::Expression::Total_Function>(m_Total_Functions, lhs,
                                                     rhs);
}

shared_ptr<Abstract> Factory::Partial_Injection(const BType& lhs,
                                                const BType& rhs) {
  return get<BConstruct::Expression::Partial_Injection>(m_Partial_Injections,
                                                        lhs, rhs);
}

shared_ptr<Abstract> Factory::Total_Injection(const BType& lhs,
                                              const BType& rhs) {
  return get<BConstruct::Expression::Total_Injection>(m_Total_Injections, lhs,
                                                      rhs);
}

shared_ptr<Abstract> Factory::Partial_Surjection(const BType& lhs,
                                                 const BType& rhs) {
  return get<BConstruct::Expression::Partial_Surjection>(m_Partial_Surjections,
                                                         lhs, rhs);
}

shared_ptr<Abstract> Factory::Total_Surjection(const BType& lhs,
                                               const BType& rhs) {
  return get<BConstruct::Expression::Total_Surjection>(m_Total_Surjections, lhs,
                                                       rhs);
}

shared_ptr<Abstract> Factory::Total_Bijection(const BType& lhs,
                                              const BType& rhs) {
  return get<BConstruct::Expression::Total_Bijection>(m_Total_Bijections, lhs,
                                                      rhs);
}

/* 5.16 Expressions of Functions */

shared_ptr<Abstract> Factory::Evaluation(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Evaluation>(m_Evaluations, lhs, rhs);
}

shared_ptr<Abstract> Factory::Transformed_Into_Function(const BType& lhs,
                                                        const BType& rhs) {
  return get<BConstruct::Expression::Transformed_Into_Function>(
      m_Transformed_Into_Functions, lhs, rhs);
}

shared_ptr<Abstract> Factory::Transformed_Into_Relation(const BType& lhs,
                                                        const BType& rhs) {
  return get<BConstruct::Expression::Transformed_Into_Relation>(
      m_Transformed_Into_Relations, lhs, rhs);
}

shared_ptr<Abstract> Factory::Lambda(const BType& lhs, const BType& rhs) {
  return get<BConstruct::Expression::Lambda>(m_Lambdas, lhs, rhs);
}

/* 5.17 Set of Sequences */

shared_ptr<Abstract> Factory::Seq(const BType& t) {
  return get<BConstruct::Expression::Seq>(m_Seqs, t);
}

shared_ptr<Abstract> Factory::Seq1(const BType& t) {
  return get<BConstruct::Expression::Seq1>(m_Seq1s, t);
}

shared_ptr<Abstract> Factory::Injective_Seq(const BType& t) {
  return get<BConstruct::Expression::Injective_Seq>(m_Injective_Seqs, t);
}

shared_ptr<Abstract> Factory::Injective_Seq1(const BType& t) {
  return get<BConstruct::Expression::Injective_Seq1>(m_Injective_Seq1s, t);
}

shared_ptr<Abstract> Factory::Perm(const BType& t) {
  return get<BConstruct::Expression::Perm>(m_Perms, t);
}

shared_ptr<Abstract> Factory::EmptySeq(const BType& t) {
  return get<BConstruct::Expression::EmptySeq>(m_EmptySeqs, t);
}

/* 5.18 Expressions of Sequences */

shared_ptr<Abstract> Factory::Size(const BType& t) {
  return get<BConstruct::Expression::Size>(m_Sizes, t);
}

shared_ptr<Abstract> Factory::First(const BType& t) {
  return get<BConstruct::Expression::First>(m_Firsts, t);
}

shared_ptr<Abstract> Factory::Last(const BType& t) {
  return get<BConstruct::Expression::Last>(m_Lasts, t);
}

shared_ptr<Abstract> Factory::Front(const BType& t) {
  return get<BConstruct::Expression::Front>(m_Fronts, t);
}

shared_ptr<Abstract> Factory::Tail(const BType& t) {
  return get<BConstruct::Expression::Tail>(m_Tails, t);
}

shared_ptr<Abstract> Factory::Rev(const BType& t) {
  return get<BConstruct::Expression::Rev>(m_Revs, t);
}

/* 5.19 Expressions of Sequences */

shared_ptr<Abstract> Factory::Concatenation(const BType& t) {
  return get<BConstruct::Expression::Concatenation>(m_Concatenations, t);
}

shared_ptr<Abstract> Factory::Insert_In_Front(const BType& t) {
  return get<BConstruct::Expression::Insert_In_Front>(m_Insert_In_Fronts, t);
}

shared_ptr<Abstract> Factory::Insert_At_Tail(const BType& t) {
  return get<BConstruct::Expression::Insert_At_Tail>(m_Insert_At_Tails, t);
}

shared_ptr<Abstract> Factory::Restrict_In_Front(const BType& t) {
  return get<BConstruct::Expression::Restrict_In_Front>(m_Restrict_In_Fronts,
                                                        t);
}

shared_ptr<Abstract> Factory::Restrict_At_Tail(const BType& t) {
  return get<BConstruct::Expression::Restrict_At_Tail>(m_Restrict_At_Tails, t);
}

shared_ptr<Abstract> Factory::General_Concatenation(const BType& t) {
  return get<BConstruct::Expression::General_Concatenation>(
      m_General_Concatenations, t);
}

size_t Factory::size() { return m_index.size(); }

shared_ptr<Abstract> Factory::at(size_t index) { return m_index.at(index); }

inline size_t hash_combine_size_t(size_t combine, size_t seed) {
  return seed ^ (combine + 0x9e3779b9 + (seed << 6) + (seed >> 2));
}

size_t Abstract::hash_combine(size_t seed) const {
  return hash_combine_size_t(this->hash(), seed);
}

const std::string Abstract::NoScript{};
const std::set<std::shared_ptr<Abstract>> Abstract::NoPrerequisites;

size_t Uniform::hash_special() const {
  return std::hash<std::string>{}(std::string(m_label));
}

string Uniform::to_string() const { return std::string(m_label); }

size_t UnaryBType::hash_special() const {
  return m_type->hash_combine(std::hash<std::string>{}(std::string(m_label)));
}

string UnaryBType::to_string() const {
  return fmt::format("{}_<{}>", m_label, m_type->to_string());
}

size_t BinaryBType::hash_special() const {
  return m_type2->hash_combine(
      m_type1->hash_combine(std::hash<std::string>{}(std::string(m_label))));
}

string BinaryBType::to_string() const {
  return fmt::format("{}_<{}, {}>", m_label, m_type1->to_string(),
                     m_type2->to_string());
}

size_t TernaryBType::hash_special() const {
  return m_type3->hash_combine(m_type2->hash_combine(
      m_type1->hash_combine(std::hash<std::string>{}(std::string(m_label)))));
}

string TernaryBType::to_string() const {
  return fmt::format("{}_<{}, {}, {}>", m_label, m_type1->to_string(),
                     m_type2->to_string(), m_type3->to_string());
}

size_t NaryBType::hash_special() const {
  return m_type4->hash_combine(m_type3->hash_combine(m_type2->hash_combine(
      m_type1->hash_combine(std::hash<std::string>{}(std::string(m_label))))));
}

string NaryBType::to_string() const {
  return fmt::format("{}_<{}, {}, {}, {}>", m_label, m_type1->to_string(),
                     m_type2->to_string(), m_type3->to_string(),
                     m_type4->to_string());
}

}  // namespace BConstruct
