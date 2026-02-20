MACHINE
    set_inter_4
CONSTANTS
    vset1, vset2, vset3
PROPERTIES
    vset1 : POW(INTEGER) &
    vset2 : POW(INTEGER) &
    vset3 : POW(INTEGER)
ASSERTIONS
    (vset1 /\ vset2) /\ vset3 = vset1 /\ (vset2 /\ vset3)
END
