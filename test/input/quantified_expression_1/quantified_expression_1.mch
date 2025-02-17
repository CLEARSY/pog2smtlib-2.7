/* quantified_expression_1
 * Author:
 * Creation date: 11/04/2025
 */
MACHINE
    quantified_expression_1
ASSERTIONS
    !(xx).(xx: INTEGER & xx : 0..10 => xx + 1 < xx * xx);
    0 : {1} or !(xx).(xx: INTEGER & xx : 0..10 => xx + 1 < xx * xx);
    #(xx).(xx: REAL & xx * xx = xx + xx)
END
