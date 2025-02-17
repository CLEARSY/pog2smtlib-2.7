/* unary_expression_1
 * Author:
 * Creation date: 11/04/2025
 */
MACHINE
    unary_expression_1
ASSERTIONS
    card({FALSE, TRUE}) = card({0, 1});
    {TRUE} : POW({FALSE,TRUE});
    {TRUE} : POW1({FALSE,TRUE});
    {TRUE} : FIN({FALSE,TRUE});
    {TRUE} : FIN1({FALSE,TRUE});
    [] : seq({0, 1});
    [] : seq1({0, 1});
    [] : iseq({0, 1});
    [] : iseq1({0, 1}) /*;
    [] : perm([0, 1])*/
END
