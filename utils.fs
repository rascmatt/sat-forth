require main.fs

: prepare ( 0 li .. ln 0 lj .. lm cn vn -- a_addr l_addr )
  \ For a list of clauses, initialize the tables and clause list for the SAT solver
  \ cn .. Number of clauses
  \ vn .. Number of variables

  { cn vn }
  cn create-clause-list { list }
  
  vn 1+ cells    \ Space required for the assignment table
  vn 1+ cells +  \ Space required for the decision-level lookup table
  vn 1+ floats + \ Space required for the decision heuristic score table (VSIDS)
  allocate throw { assignment }
  assignment vn 1+ cells + { dl_lookup }
  dl_lookup  vn 1+ cells + { vsids_score }
  
  \ initialize the tables
  vn assignment !
  vn dl_lookup  !
  vn s>f vsids_score f!
  vn 0 u+do
    -1 assignment i 1+ cells + !
    -1 dl_lookup  i 1+ cells + !
    0e  vsids_score i 1+ floats + f!
  loop

  assignment list
;
