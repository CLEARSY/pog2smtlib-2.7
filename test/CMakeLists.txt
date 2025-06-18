project(pog2smtlib27_tests)

# Search for a suitable shell program, so that the tests can be run under windows
# if a unix-like shell is available
find_program(TEST_SHELL
        NAMES bash sh
        PATHS env PATH)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/setenv.sh.model ${CMAKE_CURRENT_SOURCE_DIR}/setenv.sh @ONLY)

# Add a test that runs the program with the given arguments and checks the output, the error and the exit code
macro(add_cl_test id)
    add_test(NAME ${id}
             COMMAND ${TEST_SHELL} ${CMAKE_CURRENT_SOURCE_DIR}/dotest.sh ${CMAKE_CURRENT_SOURCE_DIR} ${id})
    set_tests_properties(${id} PROPERTIES FAIL_REGULAR_EXPRESSION "Test failed")
    set_tests_properties(${id} PROPERTIES PASS_REGULAR_EXPRESSION "Test passed")
    set_tests_properties(${id} PROPERTIES TIMEOUT 1)
    set_tests_properties(${id} PROPERTIES LABELS "command line")
endmacro(add_cl_test)

add_cl_test("integer_const_expr")
add_cl_test("arithmetical_expression_1")
add_cl_test("arithmetical_expression_2")
add_cl_test("arithmetical_expression_3")
add_cl_test("arithmetical_expression_4")
add_cl_test("arithmetical_expression_5")
add_cl_test("arithmetical_expression_6")
add_cl_test("arithmetical_expression_7")
add_cl_test("arithmetical_expression_10")
add_cl_test("arithmetical_expression_11")
add_cl_test("arithmetical_expression_12")
