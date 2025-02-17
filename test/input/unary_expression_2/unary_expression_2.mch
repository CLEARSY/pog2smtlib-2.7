/* unary_expression_2
 * Author:
 * Creation date: 11/04/2025
 */
MACHINE
    unary_expression_2
ASSERTIONS
    0: dom({1|->TRUE, 2|->FALSE});
    TRUE: ran({1|->TRUE, 2|->FALSE});
    (TRUE|->1): {1|->TRUE, 2|->FALSE}~;
    (1|->1): id({0})
END
