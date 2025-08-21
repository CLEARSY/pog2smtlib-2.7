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

# 5.4 Arithmetical Expressions (continued)
add_cl_test("max_1")
add_cl_test("max_2")
add_cl_test("min_1")
add_cl_test("min_2")
add_cl_test("card_1")
add_cl_test("card_2")
add_cl_test("card_3")
add_cl_test("card_4")

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
add_cl_test("fin_1")
add_cl_test("fin_2")
add_cl_test("fin1_1")
add_cl_test("fin1_2")
add_cl_test("quantified_set_1")
add_cl_test("quantified_set_2")
add_cl_test("quantified_set_3")
add_cl_test("quantified_set_4")
add_cl_test("quantified_set_5")

# 5.8 Set List Expressions (continued)

add_cl_test("set_diff_1")
add_cl_test("set_diff_2")
add_cl_test("union_1")
add_cl_test("union_2")
add_cl_test("inter_1")
add_cl_test("inter_2")
add_cl_test("set_union_1")
add_cl_test("set_union_2")
add_cl_test("set_inter_1")
add_cl_test("set_inter_2")

# 5.10 Set of Relations

add_cl_test("relations_1")
add_cl_test("relations_2")

# 5.11 Expressions of Relations

add_cl_test("identity_1")
add_cl_test("identity_2")
add_cl_test("reverse_1")
add_cl_test("reverse_2")
add_cl_test("prj1_1")
add_cl_test("prj1_2")
add_cl_test("prj2_1")
add_cl_test("prj2_2")
add_cl_test("composition_1")
add_cl_test("composition_2")
add_cl_test("direct_product_1")
add_cl_test("direct_product_2")

# 5.12 Expressions of Relations

add_cl_test("iteration_1")
add_cl_test("iteration_2")
add_cl_test("closure_1")
add_cl_test("closure_2")
add_cl_test("closure1_1")
add_cl_test("closure1_2")

# 5.13 Expressions of Relations

add_cl_test("domain_1")
add_cl_test("domain_2")
add_cl_test("range_1")
add_cl_test("range_2")
add_cl_test("image_1")
add_cl_test("image_2")

# 5.13 Expressions of Relations

add_cl_test("restriction_domain_1")
add_cl_test("restriction_domain_2")
add_cl_test("subtraction_domain_1")
add_cl_test("subtraction_domain_2")
add_cl_test("restriction_range_1")
add_cl_test("restriction_range_2")
add_cl_test("subtraction_range_1")
add_cl_test("subtraction_range_2")
add_cl_test("overwrite_1")
add_cl_test("overwrite_2")
add_cl_test("overwrite_3")
add_cl_test("overwrite_4")
add_cl_test("overwrite_5")

# 5.15 Sets of Functions

add_cl_test("functions_partial_1")
add_cl_test("functions_partial_2")
add_cl_test("functions_total_1")
add_cl_test("functions_total_2")
add_cl_test("injections_partial_1")
add_cl_test("injections_partial_2")
add_cl_test("injections_total_1")
add_cl_test("injections_total_2")
add_cl_test("surjections_partial_1")
add_cl_test("surjections_partial_2")
add_cl_test("surjections_total_1")
add_cl_test("surjections_total_2")
add_cl_test("bijections_total_1")
add_cl_test("bijections_total_2")

# 5.16 Expressions of Functions

add_cl_test("lambda_1")
add_cl_test("lambda_2")
add_cl_test("lambda_3")
add_cl_test("lambda_4")
add_cl_test("application_1")
add_cl_test("application_2")
add_cl_test("fnc_1")
add_cl_test("fnc_2")
add_cl_test("rel_1")
add_cl_test("rel_2")

# 5.17 Sets of Sequences

add_cl_test("set_sequences_1")
add_cl_test("set_sequences_2")
add_cl_test("seq_1")
add_cl_test("seq_2")
add_cl_test("seq1_1")
add_cl_test("seq1_2")
add_cl_test("iseq_1")
add_cl_test("iseq_2")
add_cl_test("iseq1_1")
add_cl_test("iseq1_2")

# 5.18 Expressions of Sequences

add_cl_test("size_1")
add_cl_test("size_2")
add_cl_test("first_1")
add_cl_test("first_2")
add_cl_test("last_1")
add_cl_test("last_2")
add_cl_test("front_1")
add_cl_test("front_2")
add_cl_test("tail_1")
add_cl_test("tail_2")
add_cl_test("rev_1")
add_cl_test("rev_2")

# 5.19 Expressions of Sequences

add_cl_test("concatenation_1")
add_cl_test("concatenation_2")
add_cl_test("insert_in_front_1")
add_cl_test("insert_in_front_2")
add_cl_test("insert_at_tail_1")
add_cl_test("insert_at_tail_2")
add_cl_test("restrict_in_front_1")
add_cl_test("restrict_in_front_2")
add_cl_test("restrict_at_tail_1")
add_cl_test("restrict_at_tail_2")
add_cl_test("general_concatenation_1")
add_cl_test("general_concatenation_2")
