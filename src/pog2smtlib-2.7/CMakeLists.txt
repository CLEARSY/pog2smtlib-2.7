project(pog2smtlib27_program)
message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
# configure compilers
if(CMAKE_CXX_COMPILER_ID STREQUAL GNU OR CMAKE_CXX_COMPILER_ID MATCHES Clang$)
  add_compile_options(-Wall)
  add_compile_options(-Wextra)
  add_compile_options(-pedantic)
  add_compile_options(-Werror)
  add_compile_options(-fno-threadsafe-statics)
endif()

add_subdirectory(constructs/type)
add_subdirectory(constructs/expression)
add_subdirectory(constructs/predicate)

set(POG2SMTLIB27_HEADERS
    axiom-templates.h
    bconstruct.h
    bconstruct-utils.h
    btype-symbols.h
    cc-compatibility.h
    parameters.h
    pog-signatures.h
    pog-translation.h
    pure-typing.h
    signature.h
    smtlib.h
    symbols.h
    translate-token.h
    translate-predicate.h
    translate-signature.h
    utils.h
    )

set(POG2SMTLIB27_SOURCES
    ${POG2SMTLIB27_TYPE_SOURCES}
    ${POG2SMTLIB27_EXPRESSION_SOURCES}
    ${POG2SMTLIB27_PREDICATE_SOURCES}
    axiom-templates.cpp
    bconstruct.cpp
    btype-symbols.cpp
    main.cpp
    parameters.cpp
    pog-signatures.cpp
    pog-translation.cpp
    pure-typing.cpp
    signature.cpp
    smtlib.cpp
    symbols.cpp
    translate-token.cpp
    translate-predicate.cpp
    translate-signature.cpp
    utils.cpp
    )

message("POG2SMTLIB27_SOURCES: ${POG2SMTLIB27_SOURCES}")
include_directories(
  ${CMAKE_CURRENT_BINARY_DIR}
  ${POGLIB_SOURCE_DIR}
  ${BASTLIB_SOURCE_DIR}
  ${FMT_CXX_SOURCE_DIR}/include/
  )

add_executable(pog2smtlib27
    ${POG2SMTLIB27_SOURCES}
    ${POG2SMTLIB27_HEADERS}
    )

target_link_libraries(pog2smtlib27 PRIVATE fmt::fmt-header-only -Bstatic POGLIB BAST_LIB tinyxml2::tinyxml2)
set(pog2smtlib27_EXE ${CMAKE_CURRENT_BINARY_DIR}/pog2smtlib27 CACHE PATH "pog2smtlib27 executable")
