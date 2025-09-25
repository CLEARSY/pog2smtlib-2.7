message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

set(POG2SMTLIB27_TYPE_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.h ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/powerset.h ${CMAKE_CURRENT_SOURCE_DIR}/powerset.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/type.h ${CMAKE_CURRENT_SOURCE_DIR}/type.cpp
    PARENT_SCOPE
)
