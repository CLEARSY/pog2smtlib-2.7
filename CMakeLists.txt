cmake_minimum_required(VERSION 3.16)
project(pog2smtlib-2.7)

# compile command database
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# set build type if not set
if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Setting build type to 'Release' as none was specified.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Choose the type of build." FORCE)
endif()

if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  set(PROJECT_IS_TOP_LEVEL TRUE)
else()
  set(PROJECT_IS_TOP_LEVEL FALSE)
endif()

if(PROJECT_IS_TOP_LEVEL)
  foreach(submodule
      "${PROJECT_SOURCE_DIR}/extern/POGLIB")
    if(NOT EXISTS "${submodule}/CMakeLists.txt")
      message(FATAL_ERROR "Submodule ${submodule} is missing: update submodules and try again.")
      message(FATAL_ERROR "Command : git submodule update --init --recursive.")
    endif()
  endforeach(submodule)
  add_subdirectory(extern/POGLIB)
endif()

add_subdirectory(src/pog2smtlib-2.7)

if(PROJECT_IS_TOP_LEVEL)
  include (CTest)
  add_subdirectory(test)
endif()
