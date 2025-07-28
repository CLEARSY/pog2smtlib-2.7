MACHINE
    fin1_2
CONSTANTS
    p1, p2, p3
PROPERTIES
    p1 <: FIN1(INTEGER) &
    p2 <: FIN1(INTEGER) &
    p3 <: FIN1(INTEGER) &
    p1 <: p2 &
    p2 <: p3
ASSERTIONS
    POW(p1) <: POW(p3)
END
