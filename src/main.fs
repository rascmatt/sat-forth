require clause.fs
require resolution.fs
require random.fs

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
  \ This implementation naively assigns the next free variable to a random truth value

  \ Randomize the choice of the sign
  2 random { sign }

  \ Randomize the choice of the free variable to assign:
  \ (0) Run through variables and push all free variables on stack
  \ (1) Pick a random one to assign
  \ (2) Pop the list of variables from the stack and only assign the chosen one
  
  0                ( f_n ) 
  a_addr @ 0 u+do  ( f_n )
    i 1+           ( f_n a )
    dup cells a_addr + @ 0< IF ( f_n a )
      swap 1+                  ( a f_n )
    ELSE drop THEN             ( f_n )
  loop ( a1 .. an n )

  dup 0<= IF \ No more free variables
    drop dl false exit
  THEN

  ( a1 .. an n )

  \ Pick a random index in [0; n)
  dup random { idx }
  
  \ Prepare a variable to store the chosen literal
  cell allocate throw { a }

  ( a1 .. an n )
  0 u+do ( a1 .. an )
    idx i = IF  ( a_i )
      a !       ( )
    ELSE drop THEN
  loop  ( )

  a @                     ( a )
  dup cells a_addr +      ( a addr )
  sign swap !             ( a ) \ Assign the new value
  a_addr dup @ 1+ cells + ( a dl_addr )
  over cells +            ( a ld_a_addr)
  dl 1+ swap !            ( a ) \ Put the decision level to the lookup table
  sign 0= IF negate THEN  ( li )
  dl 1+ -1                ( li dl -1 ) \ Grow the implication graph

  a free throw            \ Free the variable

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
  
  \ Remove any elements on the implication graph where the dl is greater
  \ than the target dl (i.e. in case the elements have not been removed due to
  \ the resolution algorithm)
  
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

: resolve-conflict { dl a_addr l_addr -- .. dl }
  \ Resolve the conflict by learning a clause and backtracking to the right level
  a_addr l_addr bcp-next ( .. c_addr s )
  2 <> IF ." Expected an unsatisfied clause" -1 throw THEN
  
  \ Initialize a boolean variable to indicate that we constructed a new clause, which can potentially be freed
  cell allocate throw { is_new } false is_new !
  
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

      resolve               ( c_addr r_addr )

      \ If the current c_addr is an intermediary result, we need to free it
      swap                  ( r_addr c_addr )
      is_new @ IF free-clause  ELSE drop THEN ( r_addr )
      true is_new !         ( r_addr )

  repeat ( c_addr )

  \ free the is_new variable
  is_new free throw

  l_addr swap         ( l_addr c_addr )  \ This may return an existing element in the list
  append-clause-set   ( c_addr )

  dl a_addr -rot      ( a_addr c_addr dl )
  get-backtrack-dl    ( new_dl )  

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

  453428 seed! \ Set a seed for determinism of probabilistic decisions

  align here cell allot { iteration } 0 iteration !

  -1 -1 -1  \ Initialize the root of the implication graph
  0 ( dl ) \ Initialize the decision level with 0
  begin

    a_addr l_addr bcp  ( ..  dl b )

    0= IF
      a_addr l_addr resolve-conflict ( .. dl )

      dup -1 = IF \ Backtracked to dl -1: Formula is unsatisfiable
        \ Clean up stack and exit
        a_addr drop-implication-graph
        false exit
      THEN
    ELSE ( .. dl )  \ BCP terminated without conflict: Make a new decision.

      a_addr decide ( .. dl b )

      0= IF \ All variables are assigned: Satisfying assignment found.
        a_addr print-assignment
        \ Clean up stack and exit
        a_addr drop-implication-graph
        true exit
      THEN
    THEN

    iteration @ 1+ iteration !
  again
;