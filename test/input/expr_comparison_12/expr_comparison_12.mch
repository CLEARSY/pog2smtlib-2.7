/* expr_comparison_12
 * Author:
 * Creation date: 11/04/2025
 */
MACHINE
    expr_comparison_12
SETS S1; S2
CONSTANTS
    vproduct, wproduct
PROPERTIES
    vproduct: S1 * S2 & wproduct : S1 * S2
ASSERTIONS
    vproduct = wproduct
END
