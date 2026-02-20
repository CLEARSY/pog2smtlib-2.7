MACHINE
    domain_3
CONSTANTS
    s1, s2
PROPERTIES
    s1 <: INTEGER &
    s2 <: INTEGER &
    s2 /= {}
ASSERTIONS
    dom(s1 * s2) = s1
END
