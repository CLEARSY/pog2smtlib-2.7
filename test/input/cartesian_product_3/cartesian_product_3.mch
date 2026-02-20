MACHINE
    cartesian_product_3
CONSTANTS
    s1, s2,
    c1, c2
PROPERTIES
    s1 <: INTEGER &
    s2 <: INTEGER &
    c1 : s1 &
    c2 : s2
ASSERTIONS
    c1 |-> c2 : s1 * s2
END
