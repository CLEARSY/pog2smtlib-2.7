MACHINE
    m5
CONSTANTS
    c0, c1, c2, c3, c4, c5, c6
PROPERTIES
    c0 : INTEGER &
    c1 : INTEGER &
    c2 : INTEGER &
    c3 : INTEGER &
    c4 : INTEGER &
    c5 : INTEGER &
    c6 : INTEGER &
    c0 = c1 &
    c2 = c3 &
    c3 = c4+1 &
    c4 = c5+1 &
    c5 = c6+1
ASSERTIONS
    0 <= c2
END
