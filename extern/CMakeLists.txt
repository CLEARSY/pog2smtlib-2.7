cmake_minimum_required(VERSION 3.11 FATAL_ERROR)

message(STATUS "fetching external dependencies")
include(FetchContent)

FetchContent_Declare(
  fmt
  GIT_REPOSITORY https://github.com/fmtlib/fmt.git
  GIT_TAG e69e5f977d458f2650bb346dadf2ad30c5320281
)

FetchContent_MakeAvailable(fmt)

add_subdirectory(POGLIB)

