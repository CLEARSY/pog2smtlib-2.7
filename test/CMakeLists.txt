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
             COMMAND ${TEST_SHELL} ${CMAKE_CURRENT_SOURCE_DIR}/dotest.sh ${CMAKE_CURRENT_SOURCE_DIR} ${id} ${ARGN})
    set_tests_properties(${id} PROPERTIES FAIL_REGULAR_EXPRESSION "Test failed")
    set_tests_properties(${id} PROPERTIES PASS_REGULAR_EXPRESSION "Test passed")
    set_tests_properties(${id} PROPERTIES TIMEOUT 1)
    set_tests_properties(${id} PROPERTIES LABELS "command line")
endmacro(add_cl_test)

# Program parameters

add_cl_test("issue_clearsy_27a" "-u")
add_cl_test("issue_clearsy_27b" "-m")

add_cl_test("issue_clearsy_18_dd" "--logic HO_ALL --direct-deduction")

add_cl_test("issue_clearsy_18_0_rp0" "--logic HO_ALL --reduce-po 0")
add_cl_test("issue_clearsy_18_0_rp1" "--logic HO_ALL --reduce-po 1")
add_cl_test("issue_clearsy_18_0_ddrp0" "--logic HO_ALL --direct-deduction --reduce-po 0")
add_cl_test("issue_clearsy_18_0_ddrp1" "--logic HO_ALL --direct-deduction --reduce-po 1")

add_cl_test("issue_clearsy_18_1_rp0" "--logic HO_ALL --reduce-po 0")
add_cl_test("issue_clearsy_18_1_rp1" "--logic HO_ALL --reduce-po 1")
add_cl_test("issue_clearsy_18_1_ddrp0" "--logic HO_ALL --direct-deduction --reduce-po 0")
add_cl_test("issue_clearsy_18_1_ddrp1" "--logic HO_ALL --direct-deduction --reduce-po 1")

add_cl_test("issue_clearsy_18_2_rp0" "--logic HO_ALL --reduce-po 0")
add_cl_test("issue_clearsy_18_2_rp1" "--logic HO_ALL --reduce-po 1")
add_cl_test("issue_clearsy_18_2_ddrp0" "--logic HO_ALL --direct-deduction --reduce-po 0")
add_cl_test("issue_clearsy_18_2_ddrp1" "--logic HO_ALL --direct-deduction --reduce-po 1")

add_cl_test("issue_clearsy_18_3_rp0" "--logic HO_ALL --reduce-po 0")
add_cl_test("issue_clearsy_18_3_rp1" "--logic HO_ALL --reduce-po 1")
add_cl_test("issue_clearsy_18_3_rp2" "--logic HO_ALL --reduce-po 2")
add_cl_test("issue_clearsy_18_3_ddrp0" "--logic HO_ALL --direct-deduction --reduce-po 0")
add_cl_test("issue_clearsy_18_3_ddrp1" "--logic HO_ALL --direct-deduction --reduce-po 1")
add_cl_test("issue_clearsy_18_3_ddrp2" "--logic HO_ALL --direct-deduction --reduce-po 2")

# Non regression

add_cl_test("issue_clearsy_11" "--logic HO_ALL")
add_cl_test("issue_clearsy_14" "--logic HO_ALL")
add_cl_test("issue_clearsy_15" "--logic HO_ALL")
add_cl_test("issue_clearsy_16" "--logic HO_ALL")
add_cl_test("issue_clearsy_17a" "--logic HO_ALL")
add_cl_test("issue_clearsy_17b" "--logic HO_ALL")
add_cl_test("issue_clearsy_20" "--logic HO_ALL")
add_cl_test("issue_clearsy_23" "--logic HO_ALL")
add_cl_test("issue_clearsy_26" "--logic HO_ALL")
add_cl_test("issue_clearsy_31" "--logic HO_ALL")
add_cl_test("issue_clearsy_34" "--logic HO_ALL")
add_cl_test("issue_clearsy_41" "--logic HO_ALL")
add_cl_test("issue_clearsy_52a" "--logic HO_ALL")
add_cl_test("issue_clearsy_52b" "--logic HO_ALL")

# 3.2 Types

add_cl_test("type_INTEGER" "--logic HO_ALL")
add_cl_test("type_BOOL" "--logic HO_ALL")
add_cl_test("type_REAL" "--logic HO_ALL")
add_cl_test("type_STRING" "--logic HO_ALL")
add_cl_test("type_abstract_set" "--logic HO_ALL")
add_cl_test("type_enumerated_set" "--logic HO_ALL")
add_cl_test("type_power" "--logic HO_ALL")
add_cl_test("type_product" "--logic HO_ALL")
add_cl_test("type_struct" "--logic HO_ALL")

# 4 Predicates

# 4.1 Propositions

add_cl_test("propositions" "--logic HO_ALL")

# 4.2 Quantified Predicates

add_cl_test("forall_1" "--logic HO_ALL")
add_cl_test("forall_2" "--logic HO_ALL")
add_cl_test("exists_1" "--logic HO_ALL")
add_cl_test("exists_2" "--logic HO_ALL")

# 4.3 Equality Predicates

add_cl_test("equal" "--logic HO_ALL")
add_cl_test("unequal" "--logic HO_ALL")

add_cl_test("expr_comparison_1" "--logic HO_ALL")
add_cl_test("expr_comparison_2" "--logic HO_ALL")
add_cl_test("expr_comparison_3" "--logic HO_ALL")
add_cl_test("expr_comparison_4" "--logic HO_ALL")
add_cl_test("expr_comparison_5" "--logic HO_ALL")
add_cl_test("expr_comparison_12" "--logic HO_ALL")

# 4.4 Belonging Predicates

add_cl_test("belonging_predicate_1" "--logic HO_ALL")
add_cl_test("belonging_predicate_2" "--logic HO_ALL")
add_cl_test("non_belonging_predicate_1" "--logic HO_ALL")

# 4.5 Inclusion Predicates

add_cl_test("inclusion_1" "--logic HO_ALL")
add_cl_test("inclusion_2" "--logic HO_ALL")
add_cl_test("non_inclusion_1" "--logic HO_ALL")
add_cl_test("strict_inclusion_1" "--logic HO_ALL")
add_cl_test("strict_inclusion_2" "--logic HO_ALL")
add_cl_test("non_strict_inclusion_1" "--logic HO_ALL")

# 4.5 Number Comparison Predicates

add_cl_test("less_than_or_equal_to" "--logic HO_ALL")
add_cl_test("strictly_less_than" "--logic HO_ALL")
add_cl_test("greater_than_or_equal_to" "--logic HO_ALL")
add_cl_test("strictly_greater_than" "--logic HO_ALL")

# 5 Expressions

# 5.1 Primary Expressions

# 5.1 Boolean Expressions

add_cl_test("false_1" "--logic HO_ALL")
add_cl_test("true_1" "--logic HO_ALL")
add_cl_test("bool_1" "--logic HO_ALL")
add_cl_test("bool_2" "--logic HO_ALL")

# 5.3 Arithmetical Expressions

add_cl_test("maxint_1" "--logic HO_ALL")
add_cl_test("minint_1" "--logic HO_ALL")
add_cl_test("integer_const_expr" "--logic HO_ALL")
add_cl_test("unary_minus_1" "--logic HO_ALL")
add_cl_test("unary_minus_2" "--logic HO_ALL")
add_cl_test("unary_minus_3" "--logic HO_ALL")
add_cl_test("unary_minus_4" "--logic HO_ALL")
add_cl_test("arithmetical_expression_1" "--logic HO_ALL")
add_cl_test("arithmetical_expression_2" "--logic HO_ALL")
add_cl_test("arithmetical_expression_3" "--logic HO_ALL")
add_cl_test("arithmetical_expression_4" "--logic HO_ALL")
add_cl_test("arithmetical_expression_5" "--logic HO_ALL")
add_cl_test("arithmetical_expression_6" "--logic HO_ALL")
add_cl_test("arithmetical_expression_7" "--logic HO_ALL")
add_cl_test("arithmetical_expression_8" "--logic HO_ALL")
add_cl_test("arithmetical_expression_9" "--logic HO_ALL")
add_cl_test("arithmetical_expression_10" "--logic HO_ALL")
add_cl_test("arithmetical_expression_11" "--logic HO_ALL")
add_cl_test("arithmetical_expression_12" "--logic HO_ALL")
add_cl_test("arithmetical_expression_13" "--logic HO_ALL")
add_cl_test("arithmetical_expression_14" "--logic HO_ALL")
add_cl_test("arithmetical_expression_15" "--logic HO_ALL")
add_cl_test("arithmetical_expression_16" "--logic HO_ALL")

# 5.4 Arithmetical Expressions (continued)
add_cl_test("max_1" "--logic HO_ALL")
add_cl_test("max_2" "--logic HO_ALL")
add_cl_test("min_1" "--logic HO_ALL")
add_cl_test("min_2" "--logic HO_ALL")
add_cl_test("rmax_1" "--logic HO_ALL")
add_cl_test("rmax_2" "--logic HO_ALL")
add_cl_test("rmin_1" "--logic HO_ALL")
add_cl_test("rmin_2" "--logic HO_ALL")
add_cl_test("card_1" "--logic HO_ALL")
add_cl_test("card_2" "--logic HO_ALL")
add_cl_test("card_3" "--logic HO_ALL")
add_cl_test("card_4" "--logic HO_ALL")
add_cl_test("quantified_sum_1" "--logic HO_ALL")
add_cl_test("quantified_sum_2" "--logic HO_ALL")
add_cl_test("quantified_prod_1" "--logic HO_ALL")
add_cl_test("quantified_prod_2" "--logic HO_ALL")
add_cl_test("rquantified_sum_1" "--logic HO_ALL")
add_cl_test("rquantified_sum_2" "--logic HO_ALL")
add_cl_test("rquantified_prod_1" "--logic HO_ALL")
add_cl_test("rquantified_prod_2" "--logic HO_ALL")

# 5.5 Expression of Couples

add_cl_test("expr_couple_1" "--logic HO_ALL")
add_cl_test("expr_couple_2" "--logic HO_ALL")

# 5.6 Building Sets

add_cl_test("building_set_natural_1" "--logic HO_ALL")
add_cl_test("building_set_natural_2" "--logic HO_ALL")
add_cl_test("building_set_natural1_1" "--logic HO_ALL")
add_cl_test("building_set_natural1_2" "--logic HO_ALL")
add_cl_test("building_set_nat_1" "--logic HO_ALL")
add_cl_test("building_set_nat_2" "--logic HO_ALL")
add_cl_test("building_set_nat1_1" "--logic HO_ALL")
add_cl_test("building_set_nat1_2" "--logic HO_ALL")
add_cl_test("building_set_int_1" "--logic HO_ALL")
add_cl_test("building_set_int_2" "--logic HO_ALL")
add_cl_test("building_set_bool" "--logic HO_ALL")
add_cl_test("building_set_integer" "--logic HO_ALL")
add_cl_test("building_set_string" "--logic HO_ALL")
add_cl_test("building_set_real" "--logic HO_ALL")
add_cl_test("empty_set_1" "--logic HO_ALL")
add_cl_test("empty_set_2" "--logic HO_ALL")
add_cl_test("empty_set_3" "--logic HO_ALL")

# 5.7 Set List Expressions

add_cl_test("power_set_1" "--logic HO_ALL")
add_cl_test("power_set_2" "--logic HO_ALL")
add_cl_test("power_set1_1" "--logic HO_ALL")
add_cl_test("power_set1_2" "--logic HO_ALL")
add_cl_test("cartesian_product_1" "--logic HO_ALL")
add_cl_test("cartesian_product_2" "--logic HO_ALL")
add_cl_test("interval_1" "--logic HO_ALL")
add_cl_test("interval_2" "--logic HO_ALL")
add_cl_test("set_1" "--logic HO_ALL")
add_cl_test("set_2" "--logic HO_ALL")
add_cl_test("set_3" "--logic HO_ALL")
add_cl_test("set_4" "--logic HO_ALL")
add_cl_test("fin_1" "--logic HO_ALL")
add_cl_test("fin_2" "--logic HO_ALL")
add_cl_test("fin1_1" "--logic HO_ALL")
add_cl_test("fin1_2" "--logic HO_ALL")
add_cl_test("quantified_set_1" "--logic HO_ALL")
add_cl_test("quantified_set_2" "--logic HO_ALL")
add_cl_test("quantified_set_3" "--logic HO_ALL")
add_cl_test("quantified_set_4" "--logic HO_ALL")
add_cl_test("quantified_set_5" "--logic HO_ALL")

# 5.8 Set List Expressions (continued)

add_cl_test("set_diff_1" "--logic HO_ALL")
add_cl_test("set_diff_2" "--logic HO_ALL")
add_cl_test("union_1" "--logic HO_ALL")
add_cl_test("union_2" "--logic HO_ALL")
add_cl_test("inter_1" "--logic HO_ALL")
add_cl_test("inter_2" "--logic HO_ALL")
add_cl_test("set_union_1" "--logic HO_ALL")
add_cl_test("set_union_2" "--logic HO_ALL")
add_cl_test("set_inter_1" "--logic HO_ALL")
add_cl_test("set_inter_2" "--logic HO_ALL")
add_cl_test("quantified_union_1" "--logic HO_ALL")
add_cl_test("quantified_union_2" "--logic HO_ALL")
add_cl_test("quantified_union_3" "--logic HO_ALL")
add_cl_test("quantified_union_4" "--logic HO_ALL")
add_cl_test("quantified_union_5" "--logic HO_ALL")
add_cl_test("quantified_union_6" "--logic HO_ALL")
add_cl_test("quantified_inter_1" "--logic HO_ALL")
add_cl_test("quantified_inter_2" "--logic HO_ALL")

# 5.9 Record expressions

add_cl_test("record_1" "--logic HO_ALL")
add_cl_test("record_2" "--logic HO_ALL")
add_cl_test("record_access_1" "--logic HO_ALL")
add_cl_test("record_access_2" "--logic HO_ALL")
add_cl_test("struct_1" "--logic HO_ALL")
add_cl_test("struct_2" "--logic HO_ALL")
add_cl_test("struct_3" "--logic HO_ALL")
add_cl_test("struct_4" "--logic HO_ALL")

# 5.10 Set of Relations

add_cl_test("relations_1" "--logic HO_ALL")
add_cl_test("relations_2" "--logic HO_ALL")

# 5.11 Expressions of Relations

add_cl_test("identity_1" "--logic HO_ALL")
add_cl_test("identity_2" "--logic HO_ALL")
add_cl_test("reverse_1" "--logic HO_ALL")
add_cl_test("reverse_2" "--logic HO_ALL")
add_cl_test("prj1_1" "--logic HO_ALL")
add_cl_test("prj1_2" "--logic HO_ALL")
add_cl_test("prj2_1" "--logic HO_ALL")
add_cl_test("prj2_2" "--logic HO_ALL")
add_cl_test("composition_1" "--logic HO_ALL")
add_cl_test("composition_2" "--logic HO_ALL")
add_cl_test("direct_product_1" "--logic HO_ALL")
add_cl_test("direct_product_2" "--logic HO_ALL")
add_cl_test("parallel_product_1" "--logic HO_ALL")
add_cl_test("parallel_product_2" "--logic HO_ALL")
add_cl_test("parallel_product_3" "--logic HO_ALL")

# 5.12 Expressions of Relations

add_cl_test("iteration_1" "--logic HO_ALL")
add_cl_test("iteration_2" "--logic HO_ALL")
add_cl_test("closure_1" "--logic HO_ALL")
add_cl_test("closure_2" "--logic HO_ALL")
add_cl_test("closure1_1" "--logic HO_ALL")
add_cl_test("closure1_2" "--logic HO_ALL")

# 5.13 Expressions of Relations

add_cl_test("domain_1" "--logic HO_ALL")
add_cl_test("domain_2" "--logic HO_ALL")
add_cl_test("range_1" "--logic HO_ALL")
add_cl_test("range_2" "--logic HO_ALL")
add_cl_test("image_1" "--logic HO_ALL")
add_cl_test("image_2" "--logic HO_ALL")

# 5.13 Expressions of Relations

add_cl_test("restriction_domain_1" "--logic HO_ALL")
add_cl_test("restriction_domain_2" "--logic HO_ALL")
add_cl_test("subtraction_domain_1" "--logic HO_ALL")
add_cl_test("subtraction_domain_2" "--logic HO_ALL")
add_cl_test("restriction_range_1" "--logic HO_ALL")
add_cl_test("restriction_range_2" "--logic HO_ALL")
add_cl_test("subtraction_range_1" "--logic HO_ALL")
add_cl_test("subtraction_range_2" "--logic HO_ALL")
add_cl_test("overwrite_1" "--logic HO_ALL")
add_cl_test("overwrite_2" "--logic HO_ALL")
add_cl_test("overwrite_3" "--logic HO_ALL")
add_cl_test("overwrite_4" "--logic HO_ALL")
add_cl_test("overwrite_5" "--logic HO_ALL")

# 5.15 Sets of Functions

add_cl_test("functions_partial_1" "--logic HO_ALL")
add_cl_test("functions_partial_2" "--logic HO_ALL")
add_cl_test("functions_total_1" "--logic HO_ALL")
add_cl_test("functions_total_2" "--logic HO_ALL")
add_cl_test("injections_partial_1" "--logic HO_ALL")
add_cl_test("injections_partial_2" "--logic HO_ALL")
add_cl_test("injections_total_1" "--logic HO_ALL")
add_cl_test("injections_total_2" "--logic HO_ALL")
add_cl_test("surjections_partial_1" "--logic HO_ALL")
add_cl_test("surjections_partial_2" "--logic HO_ALL")
add_cl_test("surjections_total_1" "--logic HO_ALL")
add_cl_test("surjections_total_2" "--logic HO_ALL")
add_cl_test("bijections_total_1" "--logic HO_ALL")
add_cl_test("bijections_total_2" "--logic HO_ALL")

# 5.16 Expressions of Functions

add_cl_test("lambda_1" "--logic HO_ALL")
add_cl_test("lambda_2" "--logic HO_ALL")
add_cl_test("lambda_3" "--logic HO_ALL")
add_cl_test("lambda_4" "--logic HO_ALL")
add_cl_test("application_1" "--logic HO_ALL")
add_cl_test("application_2" "--logic HO_ALL")
add_cl_test("fnc_1" "--logic HO_ALL")
add_cl_test("fnc_2" "--logic HO_ALL")
add_cl_test("rel_1" "--logic HO_ALL")
add_cl_test("rel_2" "--logic HO_ALL")

# 5.17 Sets of Sequences

add_cl_test("set_sequences_1" "--logic HO_ALL")
add_cl_test("set_sequences_2" "--logic HO_ALL")
add_cl_test("seq_1" "--logic HO_ALL")
add_cl_test("seq_2" "--logic HO_ALL")
add_cl_test("seq1_1" "--logic HO_ALL")
add_cl_test("seq1_2" "--logic HO_ALL")
add_cl_test("iseq_1" "--logic HO_ALL")
add_cl_test("iseq_2" "--logic HO_ALL")
add_cl_test("iseq1_1" "--logic HO_ALL")
add_cl_test("iseq1_2" "--logic HO_ALL")
add_cl_test("perm_1" "--logic HO_ALL")
add_cl_test("perm_2" "--logic HO_ALL")
add_cl_test("empty_seq_1" "--logic HO_ALL")
add_cl_test("empty_seq_2" "--logic HO_ALL")

# 5.18 Expressions of Sequences

add_cl_test("size_1" "--logic HO_ALL")
add_cl_test("size_2" "--logic HO_ALL")
add_cl_test("first_1" "--logic HO_ALL")
add_cl_test("first_2" "--logic HO_ALL")
add_cl_test("last_1" "--logic HO_ALL")
add_cl_test("last_2" "--logic HO_ALL")
add_cl_test("front_1" "--logic HO_ALL")
add_cl_test("front_2" "--logic HO_ALL")
add_cl_test("tail_1" "--logic HO_ALL")
add_cl_test("tail_2" "--logic HO_ALL")
add_cl_test("rev_1" "--logic HO_ALL")
add_cl_test("rev_2" "--logic HO_ALL")

# 5.19 Expressions of Sequences

add_cl_test("concatenation_1" "--logic HO_ALL")
add_cl_test("concatenation_2" "--logic HO_ALL")
add_cl_test("insert_in_front_1" "--logic HO_ALL")
add_cl_test("insert_in_front_2" "--logic HO_ALL")
add_cl_test("insert_at_tail_1" "--logic HO_ALL")
add_cl_test("insert_at_tail_2" "--logic HO_ALL")
add_cl_test("restrict_in_front_1" "--logic HO_ALL")
add_cl_test("restrict_in_front_2" "--logic HO_ALL")
add_cl_test("restrict_at_tail_1" "--logic HO_ALL")
add_cl_test("restrict_at_tail_2" "--logic HO_ALL")
add_cl_test("general_concatenation_1" "--logic HO_ALL")
add_cl_test("general_concatenation_2" "--logic HO_ALL")
