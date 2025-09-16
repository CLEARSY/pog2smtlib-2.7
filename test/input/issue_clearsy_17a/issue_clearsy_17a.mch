MACHINE
    issue_clearsy_17a
CONSTANTS
    struct1, struct2,
    record11, record12, record21, record22
PROPERTIES
    struct1 = struct(x1: INTEGER, y1: INTEGER) &
    struct2 = struct(x2: INTEGER, y2: INTEGER) &
    record11 = rec(x1: 1, y1: 1) &
    record12 = rec(x1: 1, y1: 1) &
    record21 = rec(x2: 1, y2: 1) &
    record22 = rec(x2: 1, y2: 1)
ASSERTIONS
    record11 = record12;
    record21 = record22
END
