message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib-2.7_program_SOURCE_DIR})
set(POG2SMTLIB27_PREDICATE_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/equality.h ${CMAKE_CURRENT_SOURCE_DIR}/equality.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/inclusion.h ${CMAKE_CURRENT_SOURCE_DIR}/inclusion.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/setmembership.h ${CMAKE_CURRENT_SOURCE_DIR}/setmembership.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/strictinclusion.h ${CMAKE_CURRENT_SOURCE_DIR}/strictinclusion.cpp
    PARENT_SCOPE
)
