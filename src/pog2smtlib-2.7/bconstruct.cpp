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

#include "bconstruct-private.h"
#include "btype-symbols.h"
#include "btype.h"
#include "pred.h"
#include "signature.h"

std::string toString(const BConstruct::Context &context) {
  std::vector<std::string> args;
  for (const auto &c : context) {
    args.push_back(c->to_string());
  }
  return fmt::format("[{}]", fmt::join(args, " "));
}

size_t BinaryBTypeHash::operator()(const BinaryBType &p) const {
  return p.second->hash_combine(p.first->hash_combine(0));
}

bool BinaryBTypeEqual::operator()(const BinaryBType &lhs,
                                  const BinaryBType &rhs) const {
  return BTypeEqual()(lhs.first, rhs.first) &&
         BTypeEqual()(lhs.second, rhs.second);
}

size_t TernaryBTypeHash::operator()(const TernaryBType &p) const {
  return p.at(2)->hash_combine(p.at(1)->hash_combine(p.at(0)->hash_combine(0)));
}

bool TernaryBTypeEqual::operator()(const TernaryBType &lhs,
                                   const TernaryBType &rhs) const {
  return BTypeEqual()(lhs.at(0), rhs.at(0)) &&
         BTypeEqual()(lhs.at(1), rhs.at(1)) &&
         BTypeEqual()(lhs.at(2), rhs.at(2));
}

size_t QuadrupleBTypeHash::operator()(const QuadrupleBType &p) const {
    {return p.at(3) -> hash_combine(p.at(2)->hash_combine(
        p.at(1)->hash_combine(p.at(0)->hash_combine(0))));
}
}
;
bool QuadrupleBTypeEqual::operator()(const QuadrupleBType &lhs,
                                     const QuadrupleBType &rhs) const {
  return BTypeEqual()(lhs.at(0), rhs.at(0)) &&
         BTypeEqual()(lhs.at(1), rhs.at(1)) &&
         BTypeEqual()(lhs.at(2), rhs.at(2)) &&
         BTypeEqual()(lhs.at(3), rhs.at(3));
}

namespace BConstruct {

using std::make_pair;
using std::make_shared;
using std::pair;
using std::shared_ptr;
using std::string;
using std::unordered_map;
using std::vector;

std::size_t PtrHash::operator()(
    const std::shared_ptr<BConstruct::Abstract> &t) const {
  return std::hash<uint64_t>()(t.get()->index());
}

bool PtrCompare::operator()(
    const std::shared_ptr<BConstruct::Abstract> &a,
    const std::shared_ptr<BConstruct::Abstract> &b) const {
  return a.get()->index() < b.get()->index();
}

bool PtrEqual::operator()(
    const std::shared_ptr<BConstruct::Abstract> &a,
    const std::shared_ptr<BConstruct::Abstract> &b) const {
  return a.get()->index() == b.get()->index();
}

void Factory::index(shared_ptr<Abstract> construct) {
  static constexpr bool debug_me = false;
  if (debug_me) {
    std::cerr << fmt::format("Factory::index {} {}\n", construct->to_string(),
                             m_index.size());
  }
  construct->m_index = m_index.size();
  m_index.push_back(construct);
}

template <typename T> shared_ptr<Abstract> Factory::get(shared_ptr<T> &m) {
  if (m != nullptr) {
    return m;
  }
  m = std::make_shared<T>();
  index(m);
  return m;
}

/* 4. Predicate */

shared_ptr<Abstract> Factory::NumberComparison() {
  return get<BConstruct::Predicate::NumberComparison>(m_NumberComparison);
}

/* 5.1 Primary Expressions */

shared_ptr<Abstract> Factory::BooleanExpression() {
  return get<BConstruct::Expression::BooleanExpression>(m_BooleanExpression);
}

/* 5.3 Arithmetical Expressions 1 */

shared_ptr<Abstract> Factory::Addition() {
  return get<BConstruct::Expression::Addition>(m_Addition);
}

shared_ptr<Abstract> Factory::Subtraction() {
  return get<BConstruct::Expression::Subtraction>(m_Subtraction);
}

shared_ptr<Abstract> Factory::Multiplication() {
  return get<BConstruct::Expression::Multiplication>(m_Multiplication);
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
const PreRequisites Abstract::NoPrerequisites;

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

size_t QuaternaryBType::hash_special() const {
  return m_type4->hash_combine(m_type3->hash_combine(m_type2->hash_combine(
      m_type1->hash_combine(std::hash<std::string>{}(std::string(m_label))))));
}

string QuaternaryBType::to_string() const {
  return fmt::format("{}_<{}, {}, {}, {}>", m_label, m_type1->to_string(),
                     m_type2->to_string(), m_type3->to_string(),
                     m_type4->to_string());
}

}  // namespace BConstruct
