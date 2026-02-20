MACHINE
    set_union_4
CONSTANTS
    co1, co2, co3
PROPERTIES
    co1 : POW(INTEGER) &
    co2 : POW(INTEGER) &
    co3 : POW(INTEGER)
ASSERTIONS
    (co1 \/ co2) \/ co3 = co1 \/ (co2 \/ co3)
END
