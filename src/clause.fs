\ Library including words for creating, traversing and manipulating
\ the clause database (i.e. a linked list) of the SAT solver.
\
\ Also includes words for checking checking equality or the status
\ of a clause.

: sort { addr u -- }
  \ Bubble sort the array in ascending order

  \ Base case: if u <= 1, the array is already sorted
  u 1 <= IF EXIT THEN

  \ Outer loop: repeat u-1 times
  u 1 u+do
    \ Inner loop: compare and swap adjacent elements
    u i - 0 DO
      
      \ Get the addresses of two adjacent elements
      addr i cells + @            \ Get the I-th element
      addr i 1+ cells + @         \ Get the (I+1)-th element

      \ Compare them
      2dup > IF                   \ If element I > element I+1
        \ Swap the elements
        addr i cells + !          \ Store the (I+1)-th element in the I-th position
        addr i 1+ cells + !       \ Store the I-th element in the (I+1)-th position
      ELSE
        2DROP                       \ Drop the compared values
      THEN
    loop
  loop
;

: create-clause ( l1 .. ln n -- addr )
  \ Write a clause of n literals in the format (n, l1, .., ln, n_addr) to memory (in reverse order) and return the addresss
  
  dup   ( l1 .. ln n n)
  \ Already reserve enough memory for the start element (length) and the trailing link to the next clause in a list
  2 + cells allocate throw swap ( l1 .. ln addr n )
  2dup swap !       ( l1 .. ln addr n )  \ The first value is the length of the clause
  swap cell + swap  ( l1 .. ln addr+1 n )
  0 u+do
    swap over       ( l1 .. ln-1 addr ln addr )
    i cells + !
  loop
  cell - \ Return the original address, including the length of the clause
  ( c_addr )
  
  \ Initialize the trailing link with -1
  dup @ 1+ cells over + ( c_addr n_addr )
  -1 swap !             ( c_addr )
;

: free-clause ( addr -- )
  \ Free the memory reserved by this clause
  free throw
;

: free-list ( l_addr -- )
  \ Free the memory reserved by the clause list
  begin              ( l_addr )
      dup -1 > WHILE ( l_addr )
          dup                 ( l_addr l_addr )
          dup @ 1+ cells + @  ( l_addr l+1_addr )
          swap free-clause    ( l+1_addr )
  repeat ( -1 )
  drop
;

: create-clause-list ( 0 li1 .. lin 0 lj1 .. ljm c_n -- addr )
  \ Commit a list of clauses to memory as a linked list and return the starting address
  
  dup 0<= IF ." Expected at least one clause" -1 throw THEN
  
  -1 \ Initialize address of the next element (-1 for the last one)
  swap

  0 u+do        ( 0 li1 .. lin 0 lj1 .. ljm )
    >r          \ Move the address of the next link to the return stack
    0           \ Initialize inner loop counter
    begin swap dup while
        >r 1+
    repeat
    drop dup    ( 0 li1 .. lin m m | R: ljm .. lj1 )
    begin dup 0> while
        r>      ( 0 li1 .. lin m i lj1 | R: ljm .. lj2 )
        -rot    ( 0 li1 .. lin lj1 m i | R: ljm .. lj2 )
        1-
    repeat
    drop        \ Drop the loop counter
                ( 0 li1 .. lin lj1 .. ljm m )
    create-clause  ( 0 li1 .. lin j_addr )

    dup @ 1+ cells over + ( 0 li1 .. lin j_addr n_addr )
    r> swap !             ( 0 li1 .. lin j_addr )
  loop
;

: next-clause ( addr -- addr )
  dup @ 1+ cells + @
;

: is-equal-clause { c1_addr c2_addr -- b }
  \ Two clauses are equal if they contain the same number of literals
  \ and the literals are the same.

  c1_addr -1 = c2_addr -1 = xor IF false THEN
  c1_addr -1 = c2_addr -1 = and IF true THEN

  c1_addr @ ( n )
  c2_addr @ ( n m )
  <> IF false exit THEN

  \ Sort the literals in ascending order
  c1_addr cell+ c1_addr @ sort
  c2_addr cell+ c2_addr @ sort

  true    ( s )
  c1_addr @ 0 u+do   ( s )
    i 1+ cells       ( s o )
    c1_addr over + @ ( s o li_a )
    swap             ( s li_a o )
    c2_addr swap + @ ( s li_a li_b )
    <> IF drop false leave THEN ( s )
  loop ( s )
;

: get-clause-list-length ( l_addr -- n )
    0 swap \ Initialize counter
    begin               ( i l_addr )
        dup -1 > WHILE ( i l_addr )
            dup @ 1+ cells + @
            swap 1+ swap
    repeat ( i -1 )
    drop
;

: get-clause ( addr -- li1 .. lin n )
  dup @ >r
  r@ 0 u+do
    dup i 1+ cells + @ swap
  loop
  drop r>
;

: append-clause-set ( l_addr c_addr -- c_addr )
  \ Append a new clause c to the end of the list l if l does not
  \ yet contain an identical clause. Returns either the address of the added
  \ clause of the identical clause that is already in the set.
  swap          ( c_addr l_addr )
  dup next-clause   ( c_addr l_addr l+1_addr )
  begin         ( c_addr l_addr l+1_addr )
    third third ( c_addr l_addr l+1_addr c_addr l_addr )
    is-equal-clause  IF ( c_addr l_addr l+1_addr ) \ The clause is already part of the set: Stop and return
      drop swap drop    ( l_addr )
      exit
    THEN
    dup -1 <> while ( c_addr l_addr l+1_addr )
    swap drop dup   ( c_addr l+1_addr l+1_addr )
    next-clause     ( c_addr l+1_addr l+2_addr )
  repeat        ( c_addr l_addr l+1_addr )
  drop          ( c_addr l_addr )
  over -rot     ( c_addr c_addr l_addr )
  dup @ 1+ cells swap +  ( c_addr c_addr ln_addr )
  !             ( c_addr )
;

: print-clause ( c_addr -- )
  get-clause  ( l1 .. ln n )
  0 u+do
    .
  loop
;

: lit-sign ( l -- n )
  \ return the sign of a literal as truth value
  \ i.e. 0 if the literal is negated and 1 if the literal is positive
  0< IF 0 ELSE 1 THEN
;

: get-clause-status { a_addr c_addr -- status }
  \ Return the status of the clause ( 0 .. unresolved, 1 .. unit, 2 .. unsatisfied, 3 .. satisfied )

  c_addr get-clause    ( li1 .. lin n )
  { n }
  0 \ Count of unsatisfied literals
  0 \ Count of satisfied literals
  n 0 u+do          ( li1 .. lin u s )
    rot             ( li1 .. lin-1 u s lin )
    dup abs a_addr swap cells + @ ( u s lin a )
    dup 0>= IF \ If a < 0, it's unresolved
      swap lit-sign = IF 1+ ELSE swap 1+ swap THEN
    ELSE drop drop THEN
  loop
  0 > IF drop 3 EXIT THEN
  dup n = IF drop 2 EXIT THEN
  dup n 1- = IF drop 1 EXIT THEN
  drop 0
;

: get-unit-literal { a_addr c_addr -- li }
  \ Find the literal in the current clause c_addr which is unit under the
  \ assignment a_addr
  c_addr get-clause ( li1 .. lin n )
  0 swap            ( li1 .. lin r n ) \ Initialize result. We can't exit early because we need to clean up the stack
  0 u+do            ( li1 .. lin r )
    swap            ( li1 .. lin-1 r lin )
    dup abs a_addr swap cells + @ ( li1 .. lin-1 r lin a )
    0< IF swap drop ELSE drop THEN
  loop
;

: is-asserting { dl a_addr c_addr -- b }
  \ Check if there the clause c is asserting, i.e. it has only one literal
  \ from the current decision level
  a_addr dup @ 1+ cells + { dl_addr }
  c_addr get-clause  ( l1 .. ln n )
  0 swap      ( l1 .. ln i n )
  0 u+do      ( l1 .. ln i )
    swap      ( l1 .. ln-1 i ln )
    abs cells dl_addr + @  ( l1 .. ln-1 i dl-n )
    dl = IF 1+ THEN
  loop ( i )
  1 =
;