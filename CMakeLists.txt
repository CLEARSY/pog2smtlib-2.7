cmake_minimum_required(VERSION 3.16)
project(pog2smtlib-2.7)

# compile command database
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_EXTENSIONS OFF)

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
  set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} ${CMAKE_SOURCE_DIR}/cmake/modules)
  if(PRODUCE_COVERAGE_REPORT STREQUAL "ON")
    include(CodeCoverage)
    set(COVERAGE_EXCLUDES extern "*fmt-src*")
    setup_target_for_coverage_gcovr_html(
      NAME coverage
      EXECUTABLE ctest --test-dir ${CMAKE_BINARY_DIR}
      DEPENDENCIES pog2smtlib27
    )
  endif()
  add_subdirectory(extern/tinyxml2)
  add_subdirectory(extern/BAST)
  add_subdirectory(extern/POGLIB)
endif(PROJECT_IS_TOP_LEVEL)

foreach(submodule
    "${PROJECT_SOURCE_DIR}/extern/POGLIB")
  if(NOT EXISTS "${submodule}/CMakeLists.txt")
    message(FATAL_ERROR "Submodule ${submodule} is missing: update submodules and try again.")
    message(FATAL_ERROR "Command : git submodule update --init --recursive.")
  endif()
endforeach(submodule)

add_subdirectory(extern)

add_subdirectory(src/pog2smtlib-2.7)

if(PROJECT_IS_TOP_LEVEL)
  include (CTest)
  add_subdirectory(test)
endif()
