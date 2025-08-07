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

add_cl_test("expr_comparison_1")
add_cl_test("expr_comparison_2")
add_cl_test("expr_comparison_3")
add_cl_test("expr_comparison_5")
add_cl_test("expr_comparison_6")
add_cl_test("expr_comparison_7")
add_cl_test("expr_comparison_8")
add_cl_test("expr_comparison_9")
add_cl_test("expr_comparison_10")
add_cl_test("expr_comparison_11")

# 5.1 Primary Expressions

# 5.1 Boolean Expressions

add_cl_test("boolean_expression_1")
add_cl_test("boolean_expression_2")

# 5.3 Arithmetical Expressions

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

# 5.4 Arithmetical Expressions (Continued)

# 5.5 Expression of Couples

add_cl_test("expr_couple_1")
add_cl_test("expr_couple_2")

# 5.6 Building Sets

add_cl_test("building_set_natural_1")
add_cl_test("building_set_natural_2")
add_cl_test("building_set_natural1_1")
add_cl_test("building_set_natural1_2")
add_cl_test("building_set_nat_1")
add_cl_test("building_set_nat_2")
add_cl_test("building_set_nat1_1")
add_cl_test("building_set_nat1_2")
add_cl_test("building_set_int_1")
add_cl_test("building_set_int_2")

# 5.7 Set List Expressions

add_cl_test("power_set_1")
add_cl_test("power_set_2")
add_cl_test("power_set1_1")
add_cl_test("power_set1_2")
add_cl_test("cartesian_product_1")
add_cl_test("cartesian_product_2")
add_cl_test("interval_1")
add_cl_test("interval_2")
add_cl_test("set_1")
add_cl_test("set_2")
add_cl_test("quantified_set_1")
add_cl_test("quantified_set_2")

# 5.13 Expressions of Relations

add_cl_test("domain_1")
add_cl_test("domain_2")
add_cl_test("range_1")
add_cl_test("range_2")
add_cl_test("image_1")
add_cl_test("image_2")

