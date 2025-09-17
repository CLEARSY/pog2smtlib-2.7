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
/*
Manages the signatures of the different components of a POG file so
that signatures are calculated on-demand and only once.

Two different techniques are used to calculate signatures on-demand.
Either the signature is stored in a map as the value component of a pair
and is calculated only if the key is not found in the map.
Or the signature is stored as an optional and is calculated only if the
optional is null.

The relevant components of the POG files are:

- The Define elements, i.e., sequences of predicates. Each Define element has a
  name and a list of predicates. The signature of the Define element is the
  union of the signatures of the predicates in the list. It is accessed by
  the name of the Define element.
- for each Group element, the signature of the group hypotheses
- for each local hypothesis in a Group element, the signature of the hypothesis
- for each SimpleGoal element, the signature of the goal.

Then for each SimpleGoal element, the signature for the corresponding proof
obligation is the union of the following signatures:

- the referenced Define elements
- the group hypotheses in the group of the SimpleGoal
- the referenced local hypotheses
- the goal.

The Define elements are identified by their name.
The POGroup elements are identified by their position in the `pos` variable of
the `Pog`. The local hypotheses elements in a POGroup are identified by (the
position of the group) and their position in the `hyps` variable of the
corresponding POGroup object. The SimpleGoal elements are identified by (the
position of the group) and their position in the `simpleGoals` variable of the
corresponding `POGroup` object.
*/
#ifndef POG_SIGNATURES_H
#define POG_SIGNATURES_H

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "pog.h"
#include "signature.h"

using std::map;
using std::optional;
using std::string;
using std::vector;

class POGSignatures {
 public:
  map<string, Signature> m_defines;
  struct POGroupSignatures {
    optional<Signature>
        common;  /// @brief signature of Define and Hypothesis elements
    vector<optional<Signature>> localHyps;
    vector<optional<Signature>> goals;
  };
  vector<optional<POGroupSignatures>> m_groups;

  explicit POGSignatures(const pog::pog& pog);
  POGSignatures(const POGSignatures& other) = delete;
  ~POGSignatures() = default;

  const Signature ofGoal(int group, int goal);
  /** @brief the signature of all common elements of the group of PO
   * @param group the index of the group in the POG
   * @returns the signature of all the referenced 'Define' elements
   * and of all the 'Hypothesis' elements
   */
  const Signature& ofGroup(int group);
  const Signature& ofLocalHyp(int group, int localHyp);

  string to_string() const;

 private:
  const pog::pog& m_pog;

  /** @brief computes the signatures of the different elements of a POGroup
   * @param group the position of the POGroup in the POG file
   *
   * @details
   * computes:
   * - defines: the signature of the predicates in the Define elements
   * referenced by `definitions`
   * - hyps : the signature of the predicates in `hyps`.
   */
  void initGroupSignatures(int group);

  const Signature& getDefineSignature(const std::string& name);
  const Signature& getLocalHypSignature(int group, int lhypRef);
};

#endif  // POG_SIGNATURES_H
