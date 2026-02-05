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
#include <algorithm>
#include <cstdlib>  // For EXIT_FAILURE
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

#include "pog-signatures.h"
#include "pog.h"
#include "smtlib.h"
#include "tinyxml2.h"
#include "translate-signature.h"

static void display_help() {

  static const std::string HELP =
      R"(Translates Atelier B proof obligation file to SMT-LIB format.

pog2smtlib-2.7 OPTIONS -i input_file -o output

  input_file is the path of a file in POG format.
  output is used to form the name of the output file(s).
  OPTIONS are:
  -n      Non incremental mode (one file per PO).
  -a N M  Selects the N-th Simple_Goal child element from the M-th
          Proof_Obligation element in the input for translation.
  -m, --model
          Adds the SMT option get-model to the output file(s)
  -u, --unsat-core
          Adds the SMT option get-unsat-core to the output file(s)
  -l, --logic
          Sets the option of the set-logic in the produced SMT files,
          the default value being ALL.
  -rp N, --reduce-po N
          Include only predicates in Lasso(N) (0 <=N), with Lasso 
          built with the free symbols in the Simple_Goal element and
          the corresponding Local_Hyp elements.
  -dd, --direct-deduction
          Modifies the --reduce-po to seed the lasso with the free
          symbols in the Simple_Goal element only.
  -h, --help
          Prints this help.
)";

  std::cout << HELP;
}

[[maybe_unused]] static void classifyGoals(const goal_index_t &goals,
                                           goal_selection_t &sgoals) {
  for (auto &goal : goals) {
    if (sgoals.find(goal.first) == sgoals.end()) {
      sgoals.insert({goal.first, {}});
    }
    sgoals.at(goal.first).push_back(goal.second);
  }
  for (auto &sgoal : sgoals) {
    std::sort(sgoal.second.begin(), sgoal.second.end(),
              [](size_t i, size_t j) { return i < j; });
  }
}

static size_t argtoul(const char *arg) {
  size_t result;
  try {
    result = std::stoul(arg);
  } catch (const std::invalid_argument &e) {
    std::cerr << "Invalid argument " << arg
              << " (non-negative integer expected)" << std::endl;
    return EXIT_FAILURE;
  } catch (const std::out_of_range &e) {
    std::cerr << "Invalid argument " << arg << " (too large)" << std::endl;
    return EXIT_FAILURE;
  }
  return result;
}

int main(int argc, char **argv) {
  char *input{nullptr};
  char *output{nullptr};
  goal_index_t goals;
  smt_options_t smt_options;

  // process mandatory arguments
  if (argc < 5) {
    display_help();
    return EXIT_FAILURE;
  }
  if (strcmp(argv[argc - 4], "-i") != 0) {
    display_help();
    return EXIT_FAILURE;
  }
  input = argv[argc - 3];
  if (strcmp(argv[argc - 2], "-o") != 0) {
    display_help();
    return EXIT_FAILURE;
  }
  output = argv[argc - 1];
  // process optional arguments
  int arg = 1;
  const int argstop = argc - 4;  // the last four arguments are mandatory
  while (arg < argstop) {
    if (strcmp(argv[arg], "-a") == 0) {
      if (arg + 2 < argstop) {
        const size_t group = argtoul(argv[arg + 1]);
        const size_t goal = argtoul(argv[arg + 2]);
        goals.push_back(std::make_pair(group, goal));
        arg += 3;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-h") == 0 or
               strcmp(argv[arg], "--help") == 0) {
      display_help();
      arg += 1;
    } else if (strcmp(argv[arg], "-m") == 0 or
               strcmp(argv[arg], "--model") == 0) {
      smt_options.produce_model = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-u") == 0 or
               strcmp(argv[arg], "--unsat-core") == 0) {
      smt_options.produce_unsat_core = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-l") == 0 or
               strcmp(argv[arg], "--logic") == 0) {
      if (arg + 1 < argstop) {
        smt_options.logic = std::string(argv[arg + 1]);
        arg += 2;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-rp") == 0 or
               strcmp(argv[arg], "--reduce-po") == 0) {
      if (arg + 1 < argstop) {
        const size_t n = argtoul(argv[arg + 1]);
        smt_options.reduce_po_set = true;
        smt_options.reduce_po = n;
        arg += 2;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-dd") == 0 or
               strcmp(argv[arg], "--direct-deduction") == 0) {
      smt_options.direct_deduction = true;
      arg += 1;
    } else {
      display_help();
      return EXIT_FAILURE;
    }
  }

  if (input == nullptr || output == nullptr) {
    display_help();
    return EXIT_FAILURE;
  }

  if (smt_options.direct_deduction && !smt_options.reduce_po_set) {
    std::cerr << "Error: --direct-deduction requires --reduce-po to be set"
              << std::endl;
    return EXIT_FAILURE;
  }

  std::filesystem::path inputPath(input);
  std::string extension = inputPath.extension().string();

  if (extension != ".pog") {
    std::cout << "Input file is not a pog file." << std::endl;
    return EXIT_FAILURE;
  }

  std::ifstream infile(input);  // Open the file using std::ifstream constructor

  if (!infile.is_open()) {  // Check if the file was successfully opened
    std::cout << "Error: Cannot open input file.\n";
    exit(EXIT_FAILURE);
  }

  tinyxml2::XMLDocument doc;
  tinyxml2::XMLError loadResult = doc.LoadFile(input);
  if (loadResult != tinyxml2::XML_SUCCESS) {
    std::cout << "Error loading XML file: " << doc.ErrorStr() << std::endl;
    infile.close();  // Close the file before exiting
    exit(EXIT_FAILURE);
  }

  pog::pog pog = pog::read(doc);
  // POGSignatures pogSignatures(pog);
  // for (size_t group = 0; group < pog.pos.size(); ++group) {
  //   for (size_t goal = 0; goal < pog.pos[group].simpleGoals.size(); ++goal) {
  //     Signature sig = pogSignatures.ofGoal(group, goal);
  //   }
  // }

  /* The presence of -a parameters indicates that
   * b2smtlib is used as a writer tool in a proof mechanism:
   * only one file is produced. */
  if (1 <= goals.size()) {
    for (const auto &goal : goals) {
      saveSmtLibFileOne(pog, goal, output, smt_options);
    }
  } else {
    saveSmtLibFile(pog, output, smt_options);
  }
  return EXIT_SUCCESS;
}
