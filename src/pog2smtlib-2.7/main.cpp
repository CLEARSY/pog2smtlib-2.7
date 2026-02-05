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
#include <fmt/core.h>

#include <algorithm>
#include <cstdlib>  // For EXIT_FAILURE
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

#include "pog-signatures.h"
#include "pog.h"
#include "smtlib.h"
#include "tinyxml2.h"
#include "translate-signature.h"
#include "version.h"

static std::string thanks() {
  return std::string(
      "Partly financed by French National Research Agency through project "
      "ANR-21-CE25-0010\n"
      "(Enhancing B Language Reasoners with SAT and SMT Techniques – "
      "BLaSST).\n");
}

static void display_version() {
  std::cout << fmt::format("{} ({})\n{}\n{}\n", POG2SMTLIB27_VERSION,
                           POG2SMTLIB27_SHA, POG2SMTLIB27_COPYRIGHT, thanks());
}

static void display_help(std::ostream &oss = std::cerr) {

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
  -rpX, --lasso
          Include only predicates in the fixed point of Lasso
          (exclusve with option --reduce-po).
  -dd, --direct-deduction
          Modifies the --reduce-po to seed the lasso with the free
          symbols in the Simple_Goal element only.
  -v, --version
          Prints version information.
  -h, --help
          Prints this help.
)";

  oss << HELP;
}

static void parse_options(int argc, char **argv, char *&input, char *&output,
                          goal_index_t &goals, smt_options_t &smt_options);

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

  parse_options(argc, argv, input, output, goals, smt_options);

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

static void parse_options(int argc, char **argv, char *&input, char *&output,
                          goal_index_t &goals, smt_options_t &smt_options) {
  // allow --version only
  if (argc == 2 &&
      (strcmp(argv[1], "-v") == 0 || strcmp(argv[1], "--version") == 0)) {
    display_version();
    exit(EXIT_SUCCESS);
  }
  // allow --help only
  if (argc == 2 &&
      (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0)) {
    display_help(std::cout);
    exit(EXIT_SUCCESS);
  }
  // process mandatory arguments
  if (argc < 5) {
    display_help();
    exit(EXIT_FAILURE);
  }
  if (strcmp(argv[argc - 4], "-i") != 0) {
    display_help();
    exit(EXIT_FAILURE);
  }
  input = argv[argc - 3];
  if (strcmp(argv[argc - 2], "-o") != 0) {
    display_help();
    exit(EXIT_FAILURE);
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
        exit(EXIT_FAILURE);
      }
    } else if (strcmp(argv[arg], "-h") == 0 ||
               strcmp(argv[arg], "--help") == 0) {
      display_help(std::cout);
      arg += 1;
    } else if (strcmp(argv[arg], "-m") == 0 ||
               strcmp(argv[arg], "--model") == 0) {
      smt_options.produce_model = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-u") == 0 ||
               strcmp(argv[arg], "--unsat-core") == 0) {
      smt_options.produce_unsat_core = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-l") == 0 ||
               strcmp(argv[arg], "--logic") == 0) {
      if (arg + 1 < argstop) {
        smt_options.logic = std::string(argv[arg + 1]);
        arg += 2;
      } else {
        display_help();
        exit(EXIT_FAILURE);
      }
    } else if (strcmp(argv[arg], "-rp") == 0 ||
               strcmp(argv[arg], "--reduce-po") == 0) {
      if (arg + 1 < argstop && !smt_options.reduce_po_lasso) {
        const size_t n = argtoul(argv[arg + 1]);
        smt_options.reduce_po_set = true;
        smt_options.reduce_po_lasso = false;
        smt_options.reduce_po_depth = n;
        arg += 2;
      } else {
        display_help();
        exit(EXIT_FAILURE);
      }
    } else if (strcmp(argv[arg], "-rpX") == 0 ||
               strcmp(argv[arg], "--lasso") == 0) {
      if (!smt_options.reduce_po_set || smt_options.reduce_po_lasso) {
        smt_options.reduce_po_set = true;
        smt_options.reduce_po_lasso = true;
        arg += 2;
      } else {
        display_help();
        exit(EXIT_FAILURE);
      }
    } else if (strcmp(argv[arg], "-dd") == 0 ||
               strcmp(argv[arg], "--direct-deduction") == 0) {
      smt_options.direct_deduction = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-v") == 0 ||
               strcmp(argv[arg], "--version") == 0) {
      display_version();
      arg += 1;
    } else {
      display_help();
      exit(EXIT_FAILURE);
    }
  }

  if (input == nullptr || output == nullptr) {
    display_help();
    exit(EXIT_FAILURE);
  }

  if (smt_options.direct_deduction && !smt_options.reduce_po_set) {
    std::cerr << "Error: --direct-deduction requires --reduce-po to be set"
              << std::endl;
    exit(EXIT_FAILURE);
  }
}
