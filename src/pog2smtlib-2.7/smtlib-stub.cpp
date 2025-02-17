#include "smtlib.h"

void smtlib::saveSmtLibFileIncrSome(
    [[maybe_unused]] Logic logic, [[maybe_unused]] const pog::pog &pog,
    [[maybe_unused]] const goal_selection_t &goals,
    [[maybe_unused]] const std::string &output,
    [[maybe_unused]] bool produce_model) {}

void smtlib::saveSmtLibFileIncr([[maybe_unused]] Logic logic,
                                [[maybe_unused]] const pog::pog &pog,
                                [[maybe_unused]] const std::string &output,
                                [[maybe_unused]] bool produce_model) {}

void smtlib::saveSmtLibFileNonIncrOne(
    [[maybe_unused]] Logic logic, [[maybe_unused]] const pog::pog &pog,
    [[maybe_unused]] int groupId, [[maybe_unused]] size_t goalId,
    [[maybe_unused]] const std::string &output,
    [[maybe_unused]] bool produce_model) {}

void smtlib::saveSmtLibFileNonIncr([[maybe_unused]] Logic logic,
                                   [[maybe_unused]] const pog::pog &pog,
                                   [[maybe_unused]] const std::string &output,
                                   [[maybe_unused]] bool produce_model) {}