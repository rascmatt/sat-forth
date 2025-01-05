require utils.fs
require dimacs.fs

: test ( 0 li .. ln 0 lj .. lm cn vn b -- )
  \ test the list of clauses and assert the expected result
  { expected }
  prepare       ( a_addr l_addr )
  2dup is-sat   ( a_addr l_addr result )
  dup expected <> IF ." Expected " expected . ." but was " . ELSE drop THEN

  free-list     ( a_addr )
  free throw    ( )
;

s" ./dimacs/t1.cnf" dimacs
true test

s" ./dimacs/t2.cnf" dimacs
true test

s" ./dimacs/t3.cnf" dimacs
true test

s" ./dimacs/t4.cnf" dimacs
false test

s" ./dimacs/uf20-01.cnf" dimacs
true test

s" ./dimacs/uf20-0101.cnf" dimacs
true test

s" ./dimacs/uf20-0999.cnf" dimacs
true test