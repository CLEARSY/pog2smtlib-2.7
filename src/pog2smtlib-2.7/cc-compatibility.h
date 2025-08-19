/*
  This file is part of pog2smtlib-2.7
  Copyright © CLEARSY 2025
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
#ifndef CC_COMPATIBILITY_H
#define CC_COMPATIBILITY_H

#if 202002L <= __cplusplus
#include <source_location>
#define FILE_NAME std::source_location::current().file_name()
#define LINE_NUMBER std::source_location::current().line()
#else
#define FILE_NAME __FILE__
#define LINE_NUMBER __LINE__
#endif

#endif  // CC_COMPATIBILITY_H