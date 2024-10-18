: test ( 0 li .. ln 0 lj .. lm n b -- )
  \ test the list of clauses and assert the expected result
  { expected }
  dup { n }
  create-clause-list { list }
  here align n 2 * 2 + cells allot { assignment }
  assignment n 1+ cells + { dl_lookup }
  
  \ initialize the assignent & dl lookup table
  n assignment !
  n dl_lookup  !
  n 0 u+do
    -1 assignment i 1+ cells + !
    -1 dl_lookup  i 1+ cells + !
  loop

  assignment list is-sat ( result )
  dup expected <> IF ." Expected " expected . " but was " . ELSE drop THEN
;

\ Example 1

0 1 2
0 1 3
0 -2 -3 
3 true test

\ Example 2

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3

4 true test

\ Example 3

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3
0 -1 2 -3

5 true test

\ Example 4

0 1 2 
0 1 3 
0 -2 -3 
0 -1 2 3
0 -1 2 -3
0 -1 -2 3

6 false test

