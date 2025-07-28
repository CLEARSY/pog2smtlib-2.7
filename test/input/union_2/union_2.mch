MACHINE
    union_2
CONSTANTS
    vset
PROPERTIES
    vset : POW1(POW1(INTEGER)) &
    vset = { {0}, {1, 2} }
ASSERTIONS
    union(vset) = { 0, 1, 2 }
END
