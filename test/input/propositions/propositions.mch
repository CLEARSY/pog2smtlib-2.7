MACHINE
  propositions
CONSTANTS
  c0, c1, c2, c3, c4, c5
PROPERTIES
  c0 : INTEGER &
  c1 : INTEGER &
  c2 : INTEGER &
  c3 : INTEGER &
  c4 : INTEGER &
  c5 : INTEGER
ASSERTIONS
  (c0 = c1 & not(c0 = c2)) or ((c0 = c3 => c0 = c4) <=> (c0 = c5))
END
