include(CheckTypeSize)
include(CheckIncludeFiles)
include(CheckSymbolExists)
include(CheckLibraryExists)

cmake_minimum_required(VERSION 2.6)

project(peg-c)

set(VERSION_MAJOR "0")
set(VERSION_MINOR "1")
set(VERSION_PATCH "11")

SET(CMAKE_C_FLAGS "-Wall -Wcomment -Wsign-compare -Wformat")
SET(CMAKE_C_FLAGS_RELEASE    "${CMAKE_C_FLAGS} -O3 -g")
SET(CMAKE_C_FLAGS_DEBUG      "${CMAKE_C_FLAGS} -O0 -g3")

## Source Code settings
set(PEG_SOURCE ./src/compile.c ./src/peg.c ./src/tree.c ./src/compile2.c)

if(NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "Release")
endif()

set(INCLUDE_DIRS ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/src)
include_directories(${INCLUDE_DIRS})
string(TOUPPER ${CMAKE_BUILD_TYPE} uppercase_CMAKE_BUILD_TYPE)

add_executable(pec_c ${PEG_SOURCE})
