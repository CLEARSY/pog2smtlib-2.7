MACHINE
    set_diff_1
CONSTANTS
    d1, d2, d3
PROPERTIES
    d1 : POW(INTEGER * POW1(INT * NAT)) &
    d2 : POW(INTEGER * POW1(INT * NAT)) &
    d3 : d1 &
    d3 : d2
ASSERTIONS
    d3 : d1 - d2
END
