: create-clause ( l1 .. ln n -- addr )
  \ Write a clause of n literals in the format (n, l1, .., ln) to memory (in reverse order) and return the addresss
  
  align here over   ( l1 .. ln n addr n)
  1+ cells allot swap ( l1 .. ln addr n )
  2dup swap !       ( l1 .. ln addr n )  \ The first value is the length of the clause
  swap cell + swap  ( l1 .. ln addr+1 n )
  0 u+do
    swap over       ( l1 .. ln-1 addr ln addr )
    i cells + !
  loop
  cell - \ Return the original address, including the length of the clause
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
    r>          ( 0 li1 .. lin j_addr n_addr )
    align here cell allot ( j_addr n_addr addr )
    !                     ( j_addr )
  loop
;

: append-clause-list ( li1 .. lin n l_addr -- l_addr )
  \ Append a new clause to the clause list at l_addr. Return the new head of the list.
  >r
  create-clause            ( i_addr )
  align here cell allot ( i_addr addr )
  r> swap               ( i_addr l_addr addr )
  !                     ( i_addr )
;

: next-clause ( addr -- addr )
  dup @ 1+ cells + @
;

: get-clause ( addr -- li1 .. lin n )
  dup @ >r
  r@ 0 u+do
    dup i 1+ cells + @ swap
  loop
  drop r>
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

: bcp-next ( a_addr l_addr -- c_addr status )
    \ Find a clause c_addr under the current assignment a_addr given the clause list l_addr
    \ where the clause is either unssatisfied, indicating a conflict, or unit, indicating an
    \ implication
    BEGIN
      dup -1 <> WHILE ( a_addr c_addr )
      2dup get-clause-status ( a_addr c_addr s )
      dup dup 1 = swap 2 = or IF ( a_addr c_adr s )
        rot drop exit ( c_addr s )
      THEN
      drop next-clause
    REPEAT
    swap drop -1 \ Status -1 -> no next
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

: bcp ( i0 .. in dl a_addr l_addr -- i0 .. in .. im dl b )
  \ Boolean constraint propagation: 
  \ Search for unit clauses under the current assignment, change the assignments
  \ and grow the implication graph accordingly. Return false if a conflict is reached
  \ or true if propagation terminates normally.

  begin
    2dup bcp-next ( i0 .. in dl a_addr l_addr c_addr s )
    dup -1 <> WHILE
    dup 2  = IF drop drop drop drop false exit THEN \ We've found an unsatisfied clause. There's a conflict.
    dup 1 <> IF drop drop drop drop ." Expected the next clause to be unit " -1 throw THEN
    drop third swap   ( .. a_addr l_addr a_addr c_addr )
    dup -rot          ( .. a_addr l_addr c_addr a_addr c_addr)
    get-unit-literal  ( .. a_addr l_addr c_addr u-li )

    \ Extend implication graph
    dup >r rot >r rot >r        ( dl c_addr u-li | u-li l_addr a_addr )
    -rot over                   ( u-li dl c_addr dl | u-li l_addr a_addr )
    r> r> r>            ( .. a_addr l_addr u-li )

    dup lit-sign        ( a_addr l_addr u-li a ) \ The new assignment a is 0 if the literal appears negatively, else 1
    swap abs cells      ( a_addr l_addr a offset )
    fourth + !          ( a_addr l_addr )
  repeat
  drop drop drop drop true
;

: decide { dl a_addr -- i1 .. in in+1 dl b }
  \ Make a new decision, adapt the current assignment accordingly and append the implication graph
  \ with a new decision level. 
  \ Returns true if a new assignment was made, otherwise false, i.e. there is already a complete assignment.
  \ This implementation naively assigns the next free variable to 1
  false                  ( r )
  a_addr @ 0 u+do
    a_addr i 1+ cells +  ( r addr )
    dup @ 0< IF          ( r addr )
      1 swap ! drop true ( r )
      i 1+ dl 1+ rot -1 swap ( li dl -1 r ) \ Grow the implication graph
      leave ( r )
    THEN
    drop ( r )
  loop
  dl     ( r dl )
  over IF 1+ THEN \ Make sure we increase the decision level if we've made a decision
  swap   ( dl r )
;

: drop-imp-graph ( i1 .. in dl -- )
  \ Drop all elemnts of the implication graph
  drop
  begin  ( li dl c )
    2dup >r >r third r> r> ( li dl c li dl c )
    -1 = -rot -1 = -rot -1 = and and 0= WHILE
      drop drop drop
  repeat
  drop drop drop
;

: is-sat { a_addr l_addr -- b }
  \ Checks whether clause set given by l_addr is satisfiable. If so, a_addr contains the model
  -1 -1 -1  \ Initialize the root of the implication graph
  0 ( dl ) \ Initialize the decision level with 0
  begin
    a_addr l_addr bcp  ( dl b )
    0= IF
      \ TODO: learn a clause and backtrack. For now we just return false, i.e. unsat
      drop-imp-graph
      false
    THEN ( dl )
    a_addr decide ( dl b )
    0= IF \ No conflict, and no free variables left -> Found a satisfying assignment
      drop-imp-graph
      true exit
    THEN
  again
;