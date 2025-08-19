MACHINE
    fin_2
CONSTANTS
    p1, p2, p3
PROPERTIES
    p1 <: FIN(INTEGER) &
    p2 <: FIN(INTEGER) &
    p3 <: FIN(INTEGER) &
    p1 <: p2 &
    p2 <: p3
ASSERTIONS
    POW(p1) <: POW(p3)
END
