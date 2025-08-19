MACHINE
    union_1
CONSTANTS
    elt,
    vset1,
    vset2
PROPERTIES
    vset1 : POW(POW(INTEGER)) &
    vset2 : POW(INTEGER) &
    vset2 : vset1 &
    elt : vset2
ASSERTIONS
    elt /: union(vset1)
END
