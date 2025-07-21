MACHINE
    cartesian_product_2
CONSTANTS
    c1, c2, c3
PROPERTIES
    c1 <: INTEGER &
    c2 <: INTEGER &
    c3 <: REAL &
    c1 <: c2
ASSERTIONS
    c1 * c3 <: c2 * c3
END
