message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib27_program_SOURCE_DIR})
set(POG2SMTLIB27_EXPRESSION_SOURCES
  # 5.1 Primary Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/data.cpp

  # 5.3 Arithmetical Expressions 1
  ${CMAKE_CURRENT_SOURCE_DIR}/maxint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/minint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/integerdivision.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/floor.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/ceiling.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/toreal.cpp

  # 5.5 Expression of Couples
  ${CMAKE_CURRENT_SOURCE_DIR}/maplet.cpp

  # 5.6 Building Sets
  ${CMAKE_CURRENT_SOURCE_DIR}/emptyset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/universe.h
  ${CMAKE_CURRENT_SOURCE_DIR}/integer.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/real.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bool.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/int.cpp

  # 5.7 Set List Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.cpp

  PARENT_SCOPE
)
