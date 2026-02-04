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
    POGroupSignatures signatures;
    signatures.common = std::nullopt;
    signatures.localHyps.resize(pogroup.localHyps.size(), std::nullopt);
    m_groups.at(group) = signatures;
  }
}

const Signature &POGSignatures::ofHypothesis(size_t group, size_t hypothesis) {
  if (m_groups.at(group)->hypotheses.at(hypothesis) == std::nullopt) {
    m_groups.at(group)->hypotheses.at(hypothesis) =
        predicateSignature(m_pog.pos.at(group).hyps.at(hypothesis));
  }
  const Signature &result =
      m_groups.at(group)->hypotheses.at(hypothesis).value();
  return result;
}

const Signature &POGSignatures::ofLocalHyp(size_t group, size_t localHyp) {
  if (0 == localHyp) {
    throw std::runtime_error(
        "Null local hypothesis reference, it should be strictly positive");
  }
  const size_t index = localHyp - 1;
  initGroupSignatures(group);
  if (m_groups.at(group)->localHyps.at(index) == std::nullopt) {
    m_groups.at(group)->localHyps.at(index) =
        predicateSignature(m_pog.pos.at(group).localHyps.at(index));
  }
  const Signature &result = m_groups.at(group)->localHyps.at(index).value();
  return result;
}

const Signature POGSignatures::ofGoal(const goal_t &goal) {
  const auto &group = goal.first;
  const auto &sgoal = goal.second;
  Signature result;

  initGroupSignatures(group);
  result += POGSignatures::ofGroup(group);
  for (const auto lhypRef :
       m_pog.pos.at(group).simpleGoals.at(sgoal).localHypsRef) {
    if (!(0 < lhypRef))
      throw std::runtime_error(
          "local hypothesis reference should be strictly positive");
    result += ofLocalHyp(group, lhypRef);
  }
  Signature goalSig =
      predicateSignature(m_pog.pos.at(group).simpleGoals.at(sgoal).goal);
  result += goalSig;
  return result;
}

const Signature &POGSignatures::ofGroup(size_t group) {
  initGroupSignatures(group);
  if (m_groups.at(group)->common == std::nullopt) {
    const pog::POGroup &pogroup = m_pog.pos.at(group);
    POGroupSignatures groupSignatures;
    Signature signature;
    for (auto defName : pogroup.definitions) {
      signature += getDefineSignature(defName);
    }
    for (const auto &hyp : pogroup.hyps) {
      signature += predicateSignature(hyp);
    }
    m_groups.at(group)->common = signature;
  }
  return m_groups.at(group)->common.value();
}

const Signature POGSignatures::ofSimpleGoal(const goal_t &goal) {
  const size_t group = goal.first;
  const size_t sgoal = goal.second;
  if (m_groups.at(group) == std::nullopt) {
    m_groups.at(group) = POGroupSignatures(m_pog.pos.at(group));
  }
  if (m_groups.at(group)->simpleGoals.at(sgoal) == std::nullopt) {
    m_groups.at(group)->simpleGoals.at(sgoal) =
        predicateSignature(m_pog.pos.at(group).simpleGoals.at(sgoal).goal);
  }
  return m_groups.at(group)->simpleGoals.at(sgoal).value();
}

const Signature &POGSignatures::ofGlobalHypothesis(const Pred *const pred) {
  auto it = m_global_hyps.find(pred);
  if (it != m_global_hyps.end()) {
    return it->second;
  }
  Signature signature = predicateSignature(*pred);
  auto [it2, success] = m_global_hyps.insert({pred, std::move(signature)});
  return it2->second;
}

std::set<const Pred *> POGSignatures::filterGlobalHypotheses(size_t gid,
                                                             const Data &data) {
  std::set<const Pred *> result;

  const auto &group = m_pog.pos.at(gid);
  for (const auto &definition : group.definitions) {
    size_t i = 0;
    for (; i < m_pog.defines.size(); ++i) {
      if (definition == m_pog.defines.at(i).name) break;
    }
    const auto &def = m_pog.defines.at(i);
    for (const auto &elem : def.contents) {
      const Pred *pred = std::get_if<Pred>(&elem);
      if (pred != nullptr) {
        const auto &s = predicateSignature(*pred);
        if (s.m_data.find(data) != s.m_data.end()) {
          result.insert(pred);
        }
      }
    }
  }
  return result;
}
