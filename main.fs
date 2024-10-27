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

: print-clause ( c_addr -- )
  get-clause  ( l1 .. ln n )
  0 u+do
    .
  loop
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

: bcp-next { a_addr l_addr -- c_addr status }
    \ Find a clause c_addr under the current assignment a_addr given the clause list l_addr
    \ where the clause is either unssatisfied, indicating a conflict, or unit, indicating an
    \ implication

    \ First, try to find an unsatisfied clause. BCP needs to stop immediately if a conflict is reached.
    a_addr l_addr
    BEGIN
      dup -1 <> WHILE ( a_addr c_addr )
      2dup get-clause-status ( a_addr c_addr s )
      dup 2 = IF ( a_addr c_adr s )
        rot drop exit ( c_addr s )
      THEN
      drop next-clause
    REPEAT ( a_addr c_addr )
    
    drop l_addr ( a_addr l_addr )

    \ Second, try to find a unit clause.
    BEGIN
      dup -1 <> WHILE ( a_addr c_addr )
      2dup get-clause-status ( a_addr c_addr s )
      dup 1 = IF ( a_addr c_adr s )
        rot drop exit ( c_addr s )
      THEN
      drop next-clause
    REPEAT ( a_addr c_addr )

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
    fourth +            ( a_addr l_addr a o_addr )

    \ Write current decision level to lookup table for assigned variable
    dup 4 pick @ 1+ cells + ( a_addr l_addr a o_addr dl_addr )
    5 pick swap !           ( a_addr l_addr a o_addr )

    !                       ( a_addr l_addr ) \ Assign the variable
  repeat
  drop drop drop drop true
;

: decide { dl a_addr -- i1 .. in in+1 dl b }
  \ Make a new decision, adapt the current assignment accordingly and append the implication graph
  \ with a new decision level. 
  \ Returns true if a new assignment was made, otherwise false, i.e. there is already a complete assignment.
  \ This implementation finds the next free variable with the highest decision score, which is calculated
  \ according to the VSIDS scheme.

  \ Choose the free variable with the highest decision score. Break ties by randomly choosing one:
  \ (0) Run through variables and push all free variables on stack and determine the
  \     highest decision score
  \ (1) Remove the variables by popping them from the stack if the decision score is
  \     not the highest one
  \ (2) Pick one of the remaining literals randomly and choose it

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h1_offs )
  +                          { h1_addr }  \ Calculate the offset of the decision score table for positive literals
  h1_addr n 1+ cells +       { h2_addr }  \ Offset of the decision scores for negative literals
  
  cell allocate throw { high_score } -1 high_score !
  cell allocate throw { count } 0 count ! \ Count the number of literals with the high score

  0                ( f_n ) 
  a_addr @ 0 u+do  ( f_n )
    i 1+           ( f_n a )
    dup cells a_addr + @ 0< IF ( f_n a )
      \ Fetch the best score (pos/neg) of the current variable
      dup  h1_addr swap cells + @ ( f_n a h_p )
      over h2_addr swap cells + @ ( f_n a h_p h_n )

      \ Convert variable to a literal depending on the higher score
      2dup < IF
       rot negate -rot swap
      THEN drop    ( f_n li_a h_a )

      \ Remember the current score, if it's the best so far
      dup high_score @      ( f_n li_a h_a h_a h_b )
      2dup > IF             ( f_n li_a h_a h_a h_b )
        drop drop           ( f_n li_a h_a )
        high_score ! ( f_n li_a )
        1 count !    ( f_n li_a ) \ Reset the counter
      ELSE           ( f_n li_a h_a h_a h_b )
        = IF         ( f_n li_a h_a )
          count @ 1+ count !      \ Increase the counter
        THEN ( f_n li_a h_a )
        drop ( f_n li_a )       
      THEN ( f_n li_a )

      \ Keep the literal and increase the counter
      swap 1+                  ( li_a f_n )
    ELSE drop THEN             ( f_n )
  loop ( li_1 .. li_n n )

  dup 0<= IF \ No more free variables
    high_score free throw
    drop dl false exit
  THEN

  ( li_1 .. li_n n )

  \ Pick an index in [0; count)
  utime drop count @ mod { idx }

  \ Prepare a variable to store the chosen literal (and initialize with 0)
  cell allocate throw { a } 0 a !

  ( li_1 .. li_n n )
  0 swap \ Initialize idx
  ( li_1 .. li_n i n )
  0 u+do ( li_1 .. li_n i )
    swap     ( li_1 .. i li_n )
    dup 0< IF h2_addr ELSE h1_addr THEN ( .. i li_n h_addr )
    over abs cells + @                  ( .. i li_n h_n )
    high_score @ = IF                   ( .. i li_n )
      over idx = IF ( .. i li_n )
        dup a !
      THEN ( .. i li_n )
      drop 1+ ( .. i+1 )
    ELSE drop THEN
    ( .. i )
  loop  ( i )
  drop

  a @                     ( li )
  dup abs cells a_addr +  ( a addr )
  over lit-sign swap !    ( li ) \ Assign the new value
  a_addr dup @ 1+ cells + ( li dl_addr )
  over abs cells +        ( li ld_a_addr)
  dl 1+ swap !            ( li ) \ Store the decision level to the lookup table
  dl 1+ -1                ( li dl -1 ) \ Grow the implication graph

  high_score free throw   \ Free the variables
  a free throw         

  dl 1+ true              ( .. dl b )
;

: drop-decision ( [ li dl c_addr ] a_addr -- )
  \ Drop a decision node on the implication graph. This also marks the decision
  \ for removal in the table

  \ Decision level -1 indicates the implication graph root. Nothing
  \ to mark for deletion.
  third -1 = IF drop drop drop drop THEN

  \ Mark for removal
  dup @               ( li dl c_addr a_addr n )
  2 * 2 + cells +     ( li dl c_addr m_offs )
  fourth abs cells +  ( li dl c_addr ma_offs )
  true swap !         ( li dl c_addr )

  \ Drop the implication graph element
  drop drop drop
;

: backtrack ( i1 .. in dl a_addr t_dl -- i1 .. ij t_dl )
  \ Backtrack to the specified target decision level
  
  rot drop  ( i1 .. in a_addr t_dl )
  swap >r   ( li dl c t_dl )
  begin     ( li dl c t_dl )
    dup fourth swap > WHILE ( li dl c t_dl )
      r@        ( li dl c t_d a_addr )
      swap >r   ( li dl c a_addr )
      drop-decision
      r>        ( t_d )
  repeat
  r>            ( t_d a_addr )

  \ Remove the assignments & dl previously marked for deletion during conflict resolving
  \ or backtracking
  dup @                { a_addr n } ( t_d )
  a_addr  n 1+ cells + { dl_addr  } ( t_d )
  dl_addr n 1+ cells + { rm_addr  } ( t_d )

  n 0 u+do       ( t_d )
    i 1+ cells   ( t_d offs )
    rm_addr over + @ IF
      a_addr  over + -1 swap ! ( t_d offs ) \ Unassign the variable
      dl_addr over + -1 swap ! ( t_d offs ) \ Remove the decision level
      rm_addr + false swap !   ( t_d )      \ Unmark for removal
    ELSE drop THEN
  loop ( t_d )
;

: drop-implication-graph ( i1 .. in dl a_addr -- )
  \ Drop all elemnts of the implication graph
  -1              ( i1 .. in dl a_addr -1 )
  backtrack       ( [-1, -1, -1] -1 )
  drop            \ Drop the decision level dl
  drop drop drop  \ Drop the root node
;

: factor { c_addr -- f_addr }
  \ Apply the factoring rule i.e. deduplicate occurences of the same literals

  \ Sort the literals in the clause in ascending order
  c_addr @ ( n )
  c_addr cell + swap sort
  c_addr get-clause  ( li .. ln n )
  { n }
  0 >r        \ Push a marker on the return stack
  0 0         ( li .. ln p i )
  begin
    dup n < while ( li .. ln p i )
    -rot          ( li .. i ln p )
    2dup = IF drop swap ELSE
      drop dup >r swap
    THEN ( li .. ln p i )
    1+
  repeat ( li .. ln p i )
  drop drop ( )
  
  r> 0      ( ln i )
  begin
    over 0<> while ( li .. lj i )
      r> swap 1+
  repeat    ( li .. lm 0 m )
  swap drop \ Drop the marker
  ( li .. lm m )
  create-clause
;

: resolve { c1_addr c2_addr li -- c3_addr }
  \ Apply the resolution rule with pivot element li

  \ First, assert that li appears in c1 with the same sign.
  c1_addr get-clause  ( li .. ln n )
  0                   
  swap 0 u+do         ( li .. ln i )
    swap dup li = IF    ( li .. i ln )
      drop drop -1      ( li .. i )
    ELSE
      negate li =       ( li .. i b )
      over -1 <> and    ( li .. i b )
      IF drop -2 THEN   ( li .. i ) \ Only set to -2 if we've not already set it to -1
    THEN ( li .. i )
  loop ( i )

  \ case 1: li does not appear in c1 at all -> just combine clauses and factor
  dup 0= IF 
    drop \ drop the indicator
    c1_addr get-clause
    >r
    c2_addr get-clause r> +
    create-clause       ( c3_addr ) \ Produce an intermediary clause, which we can free after factoring
    dup factor          ( c3_addr c4_addr )
    swap free-clause    ( c4_addr )
    exit
  THEN

  \ case 2: li appears in c1 only with the opposite sign -> negate li to guarantee it occurs in c1
  -2 = IF li negate ELSE li THEN { li_n } \ Give a new name so we don't get the 'redefinition' warning

  \ Then, assert that -li appears in c2 with the right sign
  c2_addr get-clause  ( li .. lm m )
  0                   
  swap 0 u+do         ( li .. ln i )
    swap negate li_n = IF drop -1 THEN
  loop ( i )

  \ case 3: -li does not appear in c2 at all -> just combine clauses and factor
  0= IF 
    c1_addr get-clause
    >r
    c2_addr get-clause r> +
    create-clause       ( c3_addr ) \ Produce an intermediary clause, which we can free after factoring
    dup factor          ( c3_addr c4_addr )
    swap free-clause    ( c4_addr )
    exit
  THEN

  \ Here we can be sure that li occurs in c1 and -li occurs in c2

  0 \ Put a marker on the stack
  c1_addr get-clause drop ( 0 l_c1 .. l_cn )
  0 \ Another marker
  c2_addr get-clause drop ( 0 l_c1 .. l_cn 0 lc2 .. l_cm )
  
  0 \ Put a counter on the stack
  begin                   ( 0 l_c2 .. l_cm i )
    swap dup 0<> while    ( 0 l_c2 .. i l_cm )
    dup li_n negate <> IF >r 1+ ELSE drop THEN
  repeat
  drop \ Drop the first marker
  begin                   ( 0 l_c2 .. l_cn i )
    swap dup 0<> while    ( 0 l_c2 .. i l_cn )
    dup li_n <> IF >r 1+ ELSE drop THEN
  repeat
  drop \ Drop the second marker

  { n } \ Length of new clause
  n
  begin
    1- dup 0 >= while
    r> swap
  repeat ( li .. ln 0 )
  drop n ( li .. ln n )
  create-clause       ( c3_addr ) \ Produce an intermediary clause, which we can free after factoring
  dup factor          ( c3_addr c4_addr )
  swap free-clause    ( c4_addr )
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

: get-backtrack-dl { a_addr c_addr dl -- n_dl }
  \ Determine the dl to backtrack to based on the current dl and the
  \ learned clause c. This implementation returns the second-highest
  \ dl in the clause (or the one previous to the only present dl ).

  c_addr get-clause  ( li .. ln n )
  
  dup 0<= IF ." Expected the learned clause to have at least one literal." -1 throw THEN

  a_addr dup @ 1+ cells + { dl_addr }
  
  \ Remember the biggest and second biggest encountered dl
  -1 -1 rot    ( li .. ln b sb n )
  0 u+do       ( li .. ln b sb )
    rot        ( li .. b sb ln )
    abs cells dl_addr + @ ( li .. b sb dl_n )
    dup fourth > IF \ The new dl is bigger than the previous biggest
      -rot drop   ( li .. dl_n b )
    ELSE
      dup fourth <> IF
        dup third > IF \ The new dl is bigger than the previous second-biggest but not equal to the biggest
          swap drop ( li .. b dl_n )
        ELSE 
          drop  ( li .. b sb )
        THEN
      ELSE 
        drop   ( li .. b sb )
      THEN
    THEN
  loop ( b sb )
  
  over -1 = IF ." Expected the biggest decision level in a clause to be >= 0. " -1 throw THEN
  dup  -1 = IF drop 1- exit THEN
  swap drop
;

: initialize-decision-score { a_addr l_addr -- }
  \ Initialize the decision score for variables.
  \ > The current implementation initializes all scores with 1.
  \ > l_addr is unused for now, however in the future we might want to calculate the initial score
  \ > based on the input clause set

  \ TODO: initialize according to the DLIS scheme

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h1_offs )
  +                          { h1_addr }  \ Calculate the offset of the decision score table for positive literals
  h1_addr n 1+ cells +       { h2_addr }  \ Offset of the decision scores for negative literals

  n 0 u+do  ( )
    0 h1_addr i 1+ cells + !
    0 h2_addr i 1+ cells + !
  loop
;

: bump-decision-score { a_addr c_addr -- }
  \ Bump the decision score for variables occuring in the clause c
  \ > The current implementation bumps all scores by 1

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h1_offs )
  +                          { h1_addr }  \ Calculate the offset of the decision score table for positive literals
  h1_addr n 1+ cells +       { h2_addr }  \ Offset of the decision scores for negative literals

  c_addr get-clause  ( li1 .. ln n )
  0 u+do             ( li1 .. ln )
    dup 0< IF h2_addr ELSE h1_addr THEN ( .. ln hx_addr )
    swap abs cells + ( .. lin-1 hn_addr )
    dup @            ( .. lin-1 hn_addr h )
    1 +              ( .. lin-1 hn_addr h+1 )
    swap !           ( li1 .. lin-1 )
  loop ( )
;

: decay-decision-score { a_addr -- }
  \ Decay the decision score of variables
  \ > The current implementation decays all scores by 50%

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h1_offs )
  +                          { h1_addr }  \ Calculate the offset of the decision score table for positive literals
  h1_addr n 1+ cells +       { h2_addr }  \ Offset of the decision scores for negative literals

  n 0 u+do  ( )
    \ Decay positive literal scores
    h1_addr i 1+ cells +  ( hn_addr )
    dup @ 2 /             ( hn_addr h/2 )
    swap !                ( )
    \ Decay negative literal scores
    h2_addr i 1+ cells +  ( hn_addr )
    dup @ 2 /             ( hn_addr h/2 )
    swap !                ( )
  loop
;

: print-decision-scores { a_addr -- }
  \ Print the decision scores

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h1_offs )
  +                          { h1_addr }  \ Calculate the offset of the decision score table for positive literals
  h1_addr n 1+ cells +       { h2_addr }  \ Offset of the decision scores for negative literals

  n 0 u+do  ( )
    i 1+ . ." ("
    h1_addr i 1+ cells + @ . ." /"
    h2_addr i 1+ cells + @ . ." ), "
  loop
;

: resolve-conflict { dl a_addr l_addr -- .. dl }
  \ Resolve the conflict by learning a clause and backtracking to the right level
  a_addr l_addr bcp-next ( .. c_addr s )
  2 <> IF ." Expected an unsatisfied clause" -1 throw THEN
  
  \ Initialize a boolean variable to indicate that we constructed a new clause, which can potentially be freed
  cell allocate throw { is_new } false is_new !
  
  10 emit ." Resolving:"

  begin                 ( c_addr )
    \ Continue resolveing until either the clause becomes asserting, or there is not
    \ further antecedent clause to walk back to
    dup dl a_addr rot     ( c_addr dl a_addr c_addr )
    is-asserting 0=       ( [ li dl cl ] c_addr b )
    third -1 <> and while ( [ li dl cl ] c_addr )
      >r                    ( [ li dl cl ] | c_addr )
      third >r dup >r       ( [ li dl cl ] | c_addr li cl )
      a_addr drop-decision  ( | c_addr li cl )
      r> r> r>              ( cl li c_addr )
      -rot                  ( c_addr cl li )
      third -rot            ( c_addr c_addr cl li )

      10 emit third print-clause ." | " over print-clause ." | " dup .

      resolve               ( c_addr r_addr )

      ." >> " dup print-clause
      
      dup @ 0= IF   \ Resolved the empty clause: Unsat
        drop drop
        is_new free throw
        -1 exit
      THEN

      \ If the current c_addr is an intermediary result, we need to free it
      swap                  ( r_addr c_addr )
      is_new @ IF free-clause  ELSE drop THEN ( r_addr )
      true is_new !         ( r_addr )

  repeat ( c_addr )

  \ Bump the decision score for the conflict clause
  dup a_addr swap     ( c_addr a_addr c_addr)
  bump-decision-score ( c_addr )

  \ free the is_new variable
  is_new free throw

  l_addr swap         ( l_addr c_addr )  \ This may return an existing element in the list
  append-clause-set   ( c_addr )

  dl a_addr -rot      ( a_addr c_addr dl )
  get-backtrack-dl    ( new_dl )  

  10 emit
  ." Backtracking to DL " dup .

  dl a_addr rot       ( .. old_dl a_addr new_dl )
  backtrack           ( .. new_dl )
;

: print-assignment { a_addr -- }
  \ Print the (partial) variable assignment
  a_addr @  ( n )
  0 u+do    ( )
    i 1+    { li }
    a_addr li cells + @ ( a )
    dup -1 <> IF        ( a )
      li swap 0= IF negate THEN
      ." " . \ print the literal
    ELSE drop THEN
  loop
;

: is-sat { a_addr l_addr -- b }
  \ Checks whether clause set given by l_addr is satisfiable. If so, a_addr contains the model

  align here cell allot { iteration } 0 iteration !
  align here cell allot { conflict } 0 conflict !

  \ Initialize variable scores for the decision heuristics
  a_addr l_addr initialize-decision-score

  a_addr @ { n } 
  a_addr n 3 * 3 + cells     ( addr h_offs )
  +                          { h_addr } 

  -1 -1 -1  \ Initialize the root of the implication graph
  0 ( dl ) \ Initialize the decision level with 0
  begin

    10 emit ." >bcp< "
    10 emit a_addr print-assignment

    a_addr l_addr bcp  ( ..  dl b )

    10 emit ." <bcp> "
    10 emit a_addr print-assignment

    0= IF

      \ Increase the conflict count
      conflict @ 1+ conflict !

      \ Decay after every 100th conflict by 50%
      conflict @ 100 mod 0= IF
        a_addr decay-decision-score
      THEN

      a_addr l_addr resolve-conflict ( .. dl )

      10 emit ." Scores: "
      a_addr print-decision-scores

      dup -1 = IF \ Backtracked to dl -1: Formula is unsatisfiable
        \ Clean up stack and exit
        a_addr drop-implication-graph
        false exit
      THEN
    ELSE ( .. dl )  \ BCP terminated without conflict: Make a new decision.

      10 emit ." Scores: "
      a_addr print-decision-scores

      a_addr decide ( .. dl b )

      10 emit ." decide " 4 pick . '@' emit over .

      0= IF \ All variables are assigned: Satisfying assignment found.
        a_addr print-assignment
        \ Clean up stack and exit
        a_addr drop-implication-graph
        true exit
      THEN
    THEN

    iteration @ 1+ iteration !

    key drop
  again
;