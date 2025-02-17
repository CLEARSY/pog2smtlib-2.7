message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib27_program_SOURCE_DIR})
set(POG2SMTLIB27_PREDICATE_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/equality.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/inclusion.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/setmembership.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/strictinclusion.cpp
    PARENT_SCOPE
)
