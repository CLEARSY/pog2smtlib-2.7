
MACHINE
    equal_4
CONSTANTS
    zero
PROPERTIES
    zero = 1-1
ASSERTIONS
    { 1 |-> 2, 2 |-> 3 } = { zero + 1 |-> 2 + zero, 2 |-> 2+1} =>
    { { 0 }, { 1 } } = { { zero + 1 }, { zero, 0 }}
END
