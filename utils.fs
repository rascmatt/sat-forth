require main.fs

: prepare ( 0 li .. ln 0 lj .. lm cn vn -- a_addr l_addr )
  \ For a list of clauses, initialize the tables and clause list for the SAT solver
  \ cn .. Number of clauses
  \ vn .. Number of variables

  { cn vn }
  cn create-clause-list { list }
  
  
  vn 1+ cells    \ Space required for the assignment table
  vn 1+ cells +  \ Space required for the decision-level lookup table
  vn 1+ cells +  \ Space required for the removal marker table
  vn 1+ floats + \ Space required for the decision heuristic score table (VSIDS)

  allocate throw { assignment }             \ Table to store (partial) assignments
  assignment vn 1+ cells + { dl_lookup }    \ Table to store the dl at which a variable was assigned
  dl_lookup vn 1+ cells +  { dl_marker }    \ Table to mark entries in dl_lookup on next backtrack
  dl_marker vn 1+ cells +  { vsids_score }  \ Table to store the decision score for the VSIDS scheme
  
  \ Initialize the tables
  
  vn assignment !
  vn dl_lookup  !
  vn dl_marker  !
  vn s>f vsids_score f!

  vn 0 u+do
    -1 assignment i 1+ cells + !
    -1 dl_lookup  i 1+ cells + !
    false dl_marker i 1+ cells + !
    0e  vsids_score i 1+ floats + f!
  loop

  assignment list
;
