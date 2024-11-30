project(POGLoader)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(POG_HEADERS pog.h)

set(POG_SOURCES pog.cpp)

include_directories(
    ${CMAKE_CURRENT_BINARY_DIR}
	${BAST_SOURCE_DIR}
)

add_library(POGLoader_LIB STATIC ${POG_SOURCES} ${POG_HEADERS})
include_directories(${BASTLIB_SOURCE_DIR})

target_link_libraries(POGLoader_LIB PRIVATE BAST_LIB Qt5::Core Qt5::Xml)
