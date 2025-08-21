MACHINE
    quantified_union_3
ASSERTIONS
    UNION (xx, yy) . (xx : {2, 4} & yy : {{0, 1, 10}} | {zz | zz : INTEGER & zz <= xx & zz : yy}) = {0, 10}
END
