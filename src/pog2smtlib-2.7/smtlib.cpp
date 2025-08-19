/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2024-2025
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
#include "smtlib.h"

#include <fstream>
#include <iostream>
#include <map>
#include <set>

#include "exprDesc.h"
#include "pog-signatures.h"
#include "pog-translation.h"
#include "predDesc.h"
#include "signature.h"
#include "translate-signature.h"
#include "utils.h"

static void translateAndSave([[maybe_unused]] POGSignatures &pogSignatures,
                             POGTranslations &pogTranslation, int group,
                             size_t goal, const std::string &filePrefix,
                             bool setProduceUnsatCore, bool setProduceModel) {
  using std::map;
  using std::set;
  using std::string;
  using std::to_string;
  using std::vector;

  string filename{fmt::format("{}_{}_{}.po2", filePrefix, group, goal)};

  // Signature signature = pogSignatures.ofGoal(group, goal);

  string result;
  // result.append(translate(signature));
  result.append(pogTranslation.ofGoal(group, goal));

  std::ofstream out;
  out.open(filename);
  out << "(set-option :print-success false)\n";
  if (setProduceUnsatCore) {
    out << "(set-option :produce-unsat-cores true)\n";
  }
  if (setProduceModel) {
    out << "(set-option :produce-models true)\n";
  }
  out << "(set-logic HO_ALL)\n";
  out << result;
  out << "(check-sat)\n";
  if (setProduceUnsatCore) {
    out << "(get-unsat-core)\n";
  }
  if (setProduceModel) {
    out << "(get-model)\n";
  }
  out << "(exit)\n";
  out.close();
}

void saveSmtLibFile(const pog::pog &pog, const std::string &output,
                    bool setProduceUnsatCore, bool setProduceModel) {
  POGSignatures pogSignatures(pog);
  POGTranslations pogTranslation(pog, pogSignatures);
  const string filePrefix = utils::absoluteBasename(output);
  for (int group = 0; group < static_cast<int>(pog.pos.size()); ++group) {
    for (int goal = 0;
         goal < static_cast<int>(pog.pos.at(group).simpleGoals.size());
         ++goal) {
      translateAndSave(pogSignatures, pogTranslation, group, goal, filePrefix,
                       setProduceUnsatCore, setProduceModel);
    }
  }
}

void saveSmtLibFileOne(const pog::pog &pog, int group, size_t goal,
                       const std::string &output, bool setProduceUnsatCore,
                       bool setProduceModel) {
  POGSignatures pogSignatures(pog);
  POGTranslations pogTranslation(pog, pogSignatures);
  const string filePrefix = utils::absoluteBasename(output);
  translateAndSave(pogSignatures, pogTranslation, group, goal, filePrefix,
                   setProduceUnsatCore, setProduceModel);
}
