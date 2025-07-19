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