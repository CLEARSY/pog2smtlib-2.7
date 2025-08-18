MACHINE
    set_union_2
CONSTANTS
    elt, vset1, vset2
PROPERTIES
    vset1 : POW(INTEGER) &
    vset2 : POW(INTEGER) &
    elt : vset1
ASSERTIONS
    elt : (vset1 \/ vset2)
END
