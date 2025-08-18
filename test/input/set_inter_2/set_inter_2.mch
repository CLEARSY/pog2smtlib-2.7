MACHINE
    set_inter_2
CONSTANTS
    vset1, vset2, elt
PROPERTIES
    vset1 : POW(INTEGER) &
    vset2 : POW(INTEGER) &
    elt : vset1 &
    elt : vset2
ASSERTIONS
    elt : (vset1 /\ vset2)
END
