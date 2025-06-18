#include "bconstruct.h"

#include <fmt/core.h>

#include <source_location>
#include <string>

#include "btype-symbols.h"
#include "btype.h"
#include "pred.h"
#include "signature.h"

namespace BConstruct {

using std::pair;
using std::shared_ptr;
using std::string;
using std::unordered_map;
using std::vector;

void Factory::index(shared_ptr<Abstract> construct) {
  construct->m_index = m_index.size();
  m_index.push_back(construct);
}

template <typename T>
shared_ptr<Abstract> Factory::get(shared_ptr<T>& m) {
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

shared_ptr<Abstract> Factory::Type(const BType& t) {
  return get<BConstruct::Predicate::SetMembership>(m_SetMemberships, t);
}

shared_ptr<Abstract> Factory::PowerSet() {
  return get<BConstruct::Type::PowerSet>(m_PowerSet);
}

shared_ptr<Abstract> Factory::CartesianProduct() {
  return get<BConstruct::Type::CartesianProduct>(m_CartesianProduct);
}

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

shared_ptr<Abstract> Factory::Data(const struct Data& data) {
  return get(data);
}

shared_ptr<Abstract> Factory::BooleanExpression() {
  return get<BConstruct::Expression::BooleanExpression>(m_BooleanExpression);
}

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

}  // namespace BConstruct