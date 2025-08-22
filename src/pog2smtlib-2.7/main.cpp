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
#include <vector>

#include "pog-signatures.h"
#include "pog.h"
#include "smtlib.h"
#include "tinyxml2.h"
#include "translate-signature.h"

static void display_help() {
  std::cout << "Translates Atelier B proof obligation file to SMT-LIB format."
            << std::endl
            << "\tpog2smtlib-2.7 -i file.pog -o file.smt2" << std::endl
            << "\tpog2smtlib-2.7 -n [-a N1 M1 -a N2 M2 ... -a Nk Mk] [-m] -i "
               "file.pog -o file.smt2"
            << std::endl
            << "\t\t-n" << std::endl
            << "\t\t\tNon incremental mode (one file per PO)" << std::endl
            << "\t\t-a N M" << std::endl
            << "\t\t\tselects the N-th Simple_Goal child element from the M-th "
               "Proof_Obligation"
            << std::endl
            << "\t\t\telement for translation" << std::endl
            << "\t\t-i FILE" << std::endl
            << "\t\t\tspecifies the path for the input file" << std::endl
            << "\t\t-o FILE" << std::endl
            << "\t\t\tspecifies the path for the output file" << std::endl
            << "\t\t-m" << std::endl
            << "\t\t\tproduces model" << std::endl
            << "\t\t-u" << std::endl
            << "\t\t\tproduces unsat core" << std::endl
            << "\t\t--output-signature FILE" << std::endl
            << "\t\t\t(for debugging only) outputs the list of monorphized "
               "operators in the proof obligation."
            << std::endl
            << "\t\t-h" << std::endl
            << "\t\t\tprints help" << std::endl;
}

[[maybe_unused]] static void classifyGoals(
    const std::vector<std::pair<int, size_t>> &goals,
    goal_selection_t &sgoals) {
  for (auto &goal : goals) {
    if (sgoals.find(goal.first) == sgoals.end()) {
      sgoals.insert({goal.first, {}});
    }
    sgoals.at(goal.first).push_back(goal.second);
  }
  for (auto &sgoal : sgoals) {
    std::sort(sgoal.second.begin(), sgoal.second.end(),
              [](int i, int j) { return i < j; });
  }
}

int main(int argc, char **argv) {
  char *input{nullptr};
  char *output{nullptr};
  std::vector<std::pair<int, size_t>> goals;
  [[maybe_unused]] bool incr = true;
  [[maybe_unused]] bool produce_model = false;
  [[maybe_unused]] bool produce_unsat_core = false;
  [[maybe_unused]] bool output_signature = false;
  [[maybe_unused]] char *output_signature_file{nullptr};

  int arg = 1;
  while (arg < argc) {
    if (strcmp(argv[arg], "-a") == 0) {
      if (arg + 2 < argc) {
        goals.push_back(
            std::make_pair(atoi(argv[arg + 1]), atoi(argv[arg + 2])));
        arg += 3;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-i") == 0) {
      if (arg + 1 < argc) {
        input = argv[arg + 1];
        arg += 2;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-o") == 0) {
      if (arg + 1 < argc) {
        output = argv[arg + 1];
        arg += 2;
      } else {
        display_help();
        return EXIT_FAILURE;
      }
    } else if (strcmp(argv[arg], "-h") == 0) {
      display_help();
      arg += 1;
    } else if (strcmp(argv[arg], "-n") == 0) {
      incr = false;
      arg += 1;
    } else if (strcmp(argv[arg], "-m") == 0) {
      produce_model = true;
      arg += 1;
    } else if (strcmp(argv[arg], "-u") == 0) {
      produce_unsat_core = true;
      arg += 1;
    } else if (strcmp(argv[arg], "--output-signature") == 0) {
      output_signature = true;
      if (arg + 1 < argc) {
        output_signature_file = argv[arg + 1];
        arg += 2;
      }
    } else {
      display_help();
      return EXIT_FAILURE;
    }
  }

  if (input == nullptr || output == nullptr) {
    display_help();
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
      const int group{goal.first};
      const size_t id{goal.second};
      saveSmtLibFileOne(pog, group, id, output, produce_unsat_core,
                        produce_model);
    }
  } else {
    saveSmtLibFile(pog, output, produce_unsat_core, produce_model);
  }
  return EXIT_SUCCESS;
}
