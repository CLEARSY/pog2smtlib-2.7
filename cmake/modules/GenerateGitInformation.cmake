find_package(Git)

# replaces GIT_REPO_SHA in file ${SRC}
# with the sha of the git project containing this file
# to produce the file ${DST}
if(GIT_EXECUTABLE)
  get_filename_component(SRC_DIR ${SRC} DIRECTORY)
  # Generate a git-rev-parse SHA from Git repository
  execute_process(
    COMMAND ${GIT_EXECUTABLE} rev-parse HEAD
    WORKING_DIRECTORY "${SRC_DIR}"
    OUTPUT_VARIABLE GIT_SHA
    RESULT_VARIABLE GIT_SHA_ERROR_CODE
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )
  if(NOT GIT_SHA_ERROR_CODE)
    set(GIT_REPO_SHA ${GIT_SHA})
  endif()
  # Generate a git-describe tag string from Git repository
  execute_process(
    COMMAND ${GIT_EXECUTABLE} describe --tags
    WORKING_DIRECTORY "${SRC_DIR}"
    OUTPUT_VARIABLE GIT_DESCRIBE_TAG
    RESULT_VARIABLE GIT_DESCRIBE_ERROR_CODE
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )
  if(NOT GIT_DESCRIBE_ERROR_CODE)
    set(GIT_REPO_TAG ${GIT_DESCRIBE_TAG})
  endif()
endif()

# Final fallback: Just use a bogus sha string and warn to the developer.
if(NOT DEFINED GIT_REPO_SHA)
  set(GIT_REPO_SHA "00000000")
  message(WARNING "Failed to determine GIT_REPO_SHA from Git. Using default version \"${GIT_REPO_SHA}\".")
endif()
if(NOT DEFINED GIT_REPO_TAG)
  set(GIT_REPO_TAG unset)
  message(WARNING "Failed to determine GIT_REPO_TAG from Git. Using default version \"${GIT_REPO_TAG}\".")
endif()

configure_file(${SRC} ${DST} @ONLY)
