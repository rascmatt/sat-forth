require utils.fs

: test ( 0 li .. ln 0 lj .. lm cn vn b -- )
  \ test the list of clauses and assert the expected result
  { expected }
  prepare is-sat ( result )
  dup expected <> IF ." Expected " expected . ." but was " . ELSE drop THEN
;

\ Example 1

0 1 2
0 1 3
0 -2 -3 
3 3 true test

\ Example 2

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3

4 3 true test

\ Example 3

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3
0 -1 2 -3

5 3 true test

\ Example 4

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3
0 -1 2 -3
0 -1 -2 3

6 3 false test

\ Example 5

0 1 -2
0 -1 2

2 2 true test
