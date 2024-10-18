require utils.fs
require dimacs.fs

: test ( 0 li .. ln 0 lj .. lm cn vn b -- )
  \ test the list of clauses and assert the expected result
  { expected }
  prepare is-sat ( result )
  dup expected <> IF ." Expected " expected . ." but was " . ELSE drop THEN
;

s" ./dimacs/t1.cnf" parse-dimacs
true test

s" ./dimacs/t2.cnf" parse-dimacs
true test

s" ./dimacs/t3.cnf" parse-dimacs
true test

s" ./dimacs/t3.cnf" parse-dimacs
false test


