message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

set(B2SMTLIB_HEADERS
    utils.h
    axiom_templates.h
    prelude_builder.h
    smtlib.h
    )

set(B2SMTLIB_SOURCES
    utils.cpp
    axiom_templates.cpp
    prelude_builder.cpp
    smtlib.cpp
    main.cpp
    )

include_directories(
  ${CMAKE_CURRENT_BINARY_DIR}
  ${POGLoader_SOURCE_DIR}
  ${BASTLIB_SOURCE_DIR}
  )

add_executable(b2smtlib
    ${B2SMTLIB_SOURCES}
    ${B2SMTLIB_HEADERS}
    )

target_link_libraries(b2smtlib -Bstatic BAST_LIB POGLoader_LIB -Bdynamic Qt5::Core Qt5::Xml)
