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

#include <QDir>
#include <QFileInfo>
#include <QString>

namespace utils {

using std::string;

string absoluteBasename(const string &filename) {
  // The next lines build the prefix of the paths common to all files that
  // will be output: "absolutePath/baseName" The result is stored in variable
  // `prefix`. Note: The path class provided in C++17 contains all the
  // functionalities to implement the following lines. get the path up but the
  // file extension
  QFileInfo qi{QString::fromStdString(filename)};
  QString base{qi.baseName()};  // all characters in the file up to (but not
                                // including) the first '.'.
  if (base == "") base = "out";
  string prefix{QString("%1%2%3")
                    .arg(qi.absolutePath())
                    .arg(QDir::separator())
                    .arg(base)
                    .toStdString()};
  return prefix;
}

string absoluteFilePath(const string &filename) {
  QFileInfo qi{QString::fromStdString(filename)};
  return qi.absoluteFilePath().toStdString();
}

}  // namespace utils
