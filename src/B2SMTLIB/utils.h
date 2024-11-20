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
******************************************************************************/#ifndef UTILS_H
#define UTILS_H

#include <string>

namespace utils {

using std::string;

/**
 * @brief absoluteBasename returns the full absolute path minus the file
 * extension
 * @param filename a path in the current file system
 * @return the absolute path corresponding to the given path, with the file
 * extension removed.
 */
extern string absoluteBasename(const string &filename);

/**
 * @brief absoluteName returns the full absolute path up to and including the
 * file extension
 * @param filename a path in the current file system
 * @return the absolute path corresponding to the given path.
 */
extern string absoluteFilePath(const string &filename);

} // namespace utils

#endif // UTILS_H
