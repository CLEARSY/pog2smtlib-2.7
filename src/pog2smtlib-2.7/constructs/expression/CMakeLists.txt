message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib27_program_SOURCE_DIR})
set(POG2SMTLIB27_EXPRESSION_SOURCES
  ${CMAKE_CURRENT_SOURCE_DIR}/data.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/maxint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/minint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/integerdivision.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/floor.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/ceiling.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/toreal.cpp

  ${CMAKE_CURRENT_SOURCE_DIR}/emptyset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/universe.h
  ${CMAKE_CURRENT_SOURCE_DIR}/integer.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/real.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bool.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.cpp
  PARENT_SCOPE
)
