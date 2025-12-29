/* m0
 * Author:
 * Creation date: 30/10/2025
 */
MACHINE
    m0
SETS
    ANNEES
CONSTANTS
    naissance, deces
PROPERTIES
    naissance: ANNEES &
    deces: ANNEES
ASSERTIONS
    not(naissance = deces)
END
