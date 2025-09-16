MACHINE
    nestedstruct
CONSTANTS
    struct1, struct2,
    record11, record12, record21, record22
PROPERTIES
    struct1 = struct(x1: INTEGER, y1: INTEGER) &
    struct2 = struct(x2: struct1, y2: struct1) &
    record11 = rec(x1: 1, y1: 1) &
    record12 = rec(x1: 1, y1: 1) &
    record21 = rec(x2: record11, y2: record12) &
    record22 = rec(x2: record12, y2: record11)
ASSERTIONS
    record11'x1 = 1;
    record21'x2'x1 = 1;
    record21'x2 = record11;
    record21 /= record22
END
