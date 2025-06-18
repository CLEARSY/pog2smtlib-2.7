#include "parameters.h"

#include <limits>

const std::string Parameters::MAXINT =
    std::to_string(std::numeric_limits<int32_t>::max());
const std::string Parameters::MININT =
    std::to_string(std::numeric_limits<int32_t>::min());
