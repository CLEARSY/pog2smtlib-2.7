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

static constexpr bool debug_me = false;

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

void POGSignatures::initGroupSignatures(int group) {
  if (debug_me) {
    std::cerr << fmt::format("{0} group = {1}\n", FILE_NAME, group);
  };
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

const Signature &POGSignatures::ofLocalHyp(int group, int localHyp) {
  initGroupSignatures(group);
  if (m_groups.at(group)->localHyps.at(localHyp) == std::nullopt) {
    m_groups.at(group)->localHyps.at(localHyp) =
        predicateSignature(m_pog.pos.at(group).localHyps.at(localHyp));
  }
  const Signature &result = m_groups.at(group)->localHyps.at(localHyp).value();
  return result;
}

const Signature POGSignatures::ofGoal(int group, int goal) {
  Signature result;

  if (debug_me) {
    std::cerr << fmt::format("POGSignatures::ofGoal {} {} - initial\n{}\n",
                             group, goal, toString(result));
  }

  initGroupSignatures(group);
  const POGroupSignatures &groupSignatures = m_groups.at(group).value();
  result += groupSignatures.common.value();

  if (debug_me) {
    std::cerr << fmt::format("POGSignatures::ofGoal {} {} - group\n{}\n", group,
                             goal, toString(result));
  }

  for (auto lhypRef : m_pog.pos.at(group).simpleGoals.at(goal).localHypsRef) {
    result += ofLocalHyp(group, lhypRef - 1);
  }

  if (debug_me) {
    std::cerr << fmt::format(
        "POGSignatures::ofGoal {} {} - group+local hyps\n{}\n", group, goal,
        toString(result));
  }

  Signature goalSig =
      predicateSignature(m_pog.pos.at(group).simpleGoals.at(goal).goal);
  if (debug_me) {
    std::cerr << fmt::format("POGSignatures::ofGoal {} {} - goal\n{}\n", group,
                             goal, toString(goalSig));
  }
  result += goalSig;
  if (debug_me) {
    std::cerr << fmt::format(
        "POGSignatures::ofGoal {} {} - group+local hyps+goal\n{}\n", group,
        goal, toString(result));
  }
  return result;
}

const Signature &POGSignatures::ofGroup(int group) {
  if (debug_me) {
    std::cerr << fmt::format("{0} group = {1}\n", FILE_NAME, group);
  };
  initGroupSignatures(group);
  return m_groups.at(group)->common.value();
}