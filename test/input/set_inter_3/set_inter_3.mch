MACHINE
    set_inter_3
CONSTANTS
    vset1, vset2
PROPERTIES
    vset1 : POW(INTEGER) &
    vset2 : POW(INTEGER)
ASSERTIONS
    (vset1 /\ vset2) = (vset2 /\ vset1)
END
