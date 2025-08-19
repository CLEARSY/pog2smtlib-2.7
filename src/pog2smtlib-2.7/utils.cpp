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
#include "utils.h"

#include <filesystem>  // C++17 and later
#include <string>
namespace utils {

using std::string;

std::string absoluteBasename(const std::string &filename) {
  std::filesystem::path p(filename);
  std::string base = p.stem().string();  // Get filename without extension
  if (base.empty()) {
    base = "out";
  }
  std::filesystem::path prefix_path =
      std::filesystem::absolute(p).parent_path() / base;
  return prefix_path.string();
}

std::string absoluteFilePath(const std::string &filename) {
  std::filesystem::path p(filename);
  return std::filesystem::absolute(p).string();
}
}  // namespace utils
