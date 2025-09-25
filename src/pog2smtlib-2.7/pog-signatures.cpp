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
#include "pog-signatures.h"

#include <cstddef>

#include "cc-compatibility.h"

string POGSignatures::to_string() const {
  string result;
  result.append("POGSignatures\n");
  result.append("  m_defines\n");
  for (const auto &p : m_defines) {
    result.append(fmt::format("    {}: {}\n", p.first, p.second.to_string()));
  }
  result.append("  m_groups\n");
  for (const auto &g : m_groups) {
    if (g.has_value()) {
      const POGroupSignatures sig = g.value();
      if (sig.common.has_value()) {
        result.append("    - common: ");
        result.append(sig.common.value().to_string());
        result.append("\n");
      }
      result.append("    - localHyps\n");
      for (const auto &v : sig.localHyps) {
        if (v.has_value()) {
          result.append("      - ");
          result.append(v.value().to_string());
          result.append("\n");
        } else {
          result.append("      - (?)\n");
        }
      }
      result.append("    - goals\n");
      for (const auto &v : sig.goals) {
        if (v.has_value()) {
          result.append("      - ");
          result.append(v.value().to_string());
          result.append("\n");
        } else {
          result.append("      - (?)\n");
        }
      }
    }
  }
  return result;
}

POGSignatures::POGSignatures(const pog::pog &pog)
    : m_defines{}, m_groups{pog.pos.size(), std::nullopt}, m_pog(pog) {}

const Signature &POGSignatures::getDefineSignature(const std::string &name) {
  auto it = m_defines.find(name);
  if (it != m_defines.end()) {
    return it->second;
  }
  size_t i = 0;
  for (; i < m_pog.defines.size(); ++i) {
    if (name == m_pog.defines.at(i).name) break;
  }
  const auto &def = m_pog.defines.at(i);
  Signature signature;

  // B definitions should not be included in the signature
  if (name == "B definitions") goto insert;

  for (const auto &elem : def.contents) {
    const Pred *pred = std::get_if<Pred>(&elem);
    if (pred != nullptr) {
      signature += predicateSignature(*pred);
    }
  }

insert:
  m_defines.insert(std::make_pair(name, std::move(signature)));
  return m_defines.find(name)->second;
}

void POGSignatures::initGroupSignatures(size_t group) {
  const pog::POGroup &pogroup = m_pog.pos.at(group);
  if (m_groups.at(group) == std::nullopt) {
    POGroupSignatures groupSignatures;
    Signature commonSignature;
    for (auto defName : pogroup.definitions) {
      commonSignature += getDefineSignature(defName);
    }
    for (const auto &hyp : pogroup.hyps) {
      commonSignature += predicateSignature(hyp);
    }
    groupSignatures.common = commonSignature;
    groupSignatures.localHyps.resize(pogroup.localHyps.size(), std::nullopt);
    m_groups.at(group) = groupSignatures;
  }
}

const Signature &POGSignatures::ofLocalHyp(size_t group, size_t localHyp) {
  initGroupSignatures(group);
  if (m_groups.at(group)->localHyps.at(localHyp) == std::nullopt) {
    m_groups.at(group)->localHyps.at(localHyp) =
        predicateSignature(m_pog.pos.at(group).localHyps.at(localHyp));
  }
  const Signature &result = m_groups.at(group)->localHyps.at(localHyp).value();
  return result;
}

const Signature POGSignatures::ofGoal(const goal_t &goal) {
  const auto &group = goal.first;
  const auto &sgoal = goal.second;
  Signature result;

  initGroupSignatures(group);
  const POGroupSignatures &groupSignatures = m_groups.at(group).value();
  result += groupSignatures.common.value();
  for (const auto lhypRef :
       m_pog.pos.at(group).simpleGoals.at(sgoal).localHypsRef) {
    if (!(0 < lhypRef))
      throw std::runtime_error(
          "local hypothesis reference should be strictly positive");
    result += ofLocalHyp(group, lhypRef - 1);
  }
  Signature goalSig =
      predicateSignature(m_pog.pos.at(group).simpleGoals.at(sgoal).goal);
  result += goalSig;
  return result;
}

const Signature &POGSignatures::ofGroup(size_t group) {
  initGroupSignatures(group);
  return m_groups.at(group)->common.value();
}