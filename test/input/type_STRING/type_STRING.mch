MACHINE
  type_STRING
VARIABLES
    va
INVARIANT
    va : INTEGER &
    0 < va
INITIALISATION
    va :( va: INTEGER & 0 < va)
OPERATIONS
  read(str) =
  PRE str : STRING
  THEN
    va := va + 1
  END
END
