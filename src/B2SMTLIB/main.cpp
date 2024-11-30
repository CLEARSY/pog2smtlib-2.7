/******************************* CLEARSY **************************************
This file is part of b2smtlib

Copyright (C) 2024 CLEARSY (contact@clearsy.com)

b2smtlib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License version 3 as published by
the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/
#include <algorithm>
#include <cstring>
#include <iostream>
#include <map>
#include <vector>

#include <QDomDocument>
#include <QFile>
#include <QFileInfo>
#include <QString>

#include "pog.h"
#include "smtlib.h"

static void display_help() {
    std::cout
        << "Translates Atelier B proof obligation file to SMT-LIB format."
        << std::endl
        << "\tb2smtlib -i file.pog -o file.smt2" << std::endl
        << "\tb2smtlib -n [-a N1 M1 -a N2 M2 ... -a Nk Mk] [-m] -i "
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
        << "\t\t\tShows model." << std::endl
        << "\t\t-h" << std::endl
        << "\t\t\tprints help" << std::endl;
}

static void classifyGoals(const std::vector<std::pair<int, size_t>> &goals,
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
    bool incr = true;
    bool produce_model = false;

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
        } else {
            display_help();
            return EXIT_FAILURE;
        }
    }

    if (input == nullptr || output == nullptr) {
        display_help();
        return EXIT_FAILURE;
    }

    if (QFileInfo(input).suffix() != "pog") {
        std::cout << "Input file is not a pog file." << std::endl;
        return EXIT_FAILURE;
    }

    smtlib::Logic logic = smtlib::Logic::UF;

    QFile infile;
    QDomDocument doc;
    infile.setFileName(QString(input));
    if (!infile.exists() || !infile.open(QIODevice::ReadOnly)) {
        std::cout << "Error: Cannot open input file.\n";
        exit(EXIT_FAILURE);
    }

    doc.setContent(&infile);
    infile.close();

    pog::Pog pog = pog::read(doc);

    /* The presence of -a parameters indicates that
     * b2smtlib is used as a writer tool in a proof mechanism:
     * only one file is produced. */
    if (0 < goals.size()) {
        if (incr) {
            goal_selection_t sgoals;
            classifyGoals(goals, sgoals);
            saveSmtLibFileIncrSome(logic, pog, sgoals, output, produce_model);
        } else {
            if (1 != goals.size()) {
                display_help();
                exit(EXIT_FAILURE);
            } else {
                const int groupId{goals[0].first};
                const size_t goalId{goals[0].second};
                saveSmtLibFileNonIncrOne(logic, pog, groupId, goalId, output,
                                         produce_model);
            }
        }
    }
    /* b2smtlib is used as a command line tool,
     * e.g. to produce benchmarks. */
    else {
        if (incr) {
            saveSmtLibFileIncr(logic, pog, output, produce_model);
        } else {
            saveSmtLibFileNonIncr(logic, pog, output, produce_model);
        }
    }

    return EXIT_SUCCESS;
}
