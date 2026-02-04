MACHINE
    m2
CONSTANTS
    c0, c1, c2, c3
PROPERTIES
    c0 : INTEGER &
    c1 : INTEGER &
    c2 : INTEGER &
    c3 : INTEGER &
    c0 = c1 &
    c1 = c2
VARIABLES
    v0, v1, v2
INVARIANT
    v0 : INTEGER &
    v1 : INTEGER &
    v2 : INTEGER &
    v0 = c0 &
    v2 = c0 + c1
INITIALISATION
    v0, v1, v2 := 0, 0, c3
OPERATIONS
    op1 (p0, p1, p2) =
    PRE 
        p0 : INTEGER &
        p1 : INTEGER &
        p2 : INTEGER
    THEN
        v0 := v0 + p0 ||
        v1 := v1 - p1 ||
        v2 := c2 + p2
    END
END
