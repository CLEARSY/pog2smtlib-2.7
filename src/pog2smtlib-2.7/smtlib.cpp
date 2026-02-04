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

static void translateAndSave(POGTranslations &pogTranslation,
                             const goal_t &goal, const std::string &filePrefix,
                             const smt_options_t &options) {
  using std::map;
  using std::set;
  using std::string;
  using std::to_string;
  using std::vector;

  string filename{
      fmt::format("{}_{}_{}.po2", filePrefix, goal.first, goal.second)};

  string result;
  result.append(pogTranslation.ofGoal(goal, options.reduce_po_set,
                                      options.reduce_po,
                                      options.direct_deduction));

  std::ofstream out;
  out.open(filename);
  out << "(set-option :print-success false)\n";
  if (options.produce_unsat_core) {
    out << "(set-option :produce-unsat-cores true)\n";
  }
  if (options.produce_model) {
    out << "(set-option :produce-models true)\n";
  }
  out << "(set-logic HO_ALL)\n";
  out << result;
  out << "(check-sat)\n";
  if (options.produce_unsat_core) {
    out << "(get-unsat-core)\n";
  }
  if (options.produce_model) {
    out << "(get-model)\n";
  }
  out << "(exit)\n";
  out.close();
}

void saveSmtLibFile(const pog::pog &pog, const std::string &output,
                    const smt_options_t &options) {
  POGSignatures pogSignatures(pog);
  POGTranslations pogTranslation(pog, pogSignatures);
  const string filePrefix = utils::absoluteBasename(output);
  for (size_t group = 0; group < pog.pos.size(); ++group) {
    for (size_t goal = 0; goal < pog.pos.at(group).simpleGoals.size(); ++goal) {
      translateAndSave(pogTranslation, {group, goal}, filePrefix, options);
    }
  }
}

void saveSmtLibFileOne(const pog::pog &pog, const goal_t &goal,
                       const std::string &output,
                       const smt_options_t &options) {
  POGSignatures pogSignatures(pog);
  POGTranslations pogTranslation(pog, pogSignatures);
  const string filePrefix = utils::absoluteBasename(output);
  translateAndSave(pogTranslation, goal, filePrefix, options);
}
