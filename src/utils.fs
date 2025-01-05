require main.fs

: prepare ( 0 li .. ln 0 lj .. lm cn vn -- a_addr l_addr )
  \ For a list of clauses, initialize the tables and clause list for the SAT solver
  \ cn .. Number of clauses
  \ vn .. Number of variables

  { cn vn }
  cn create-clause-list { list }
  
  vn 3 * 3 + cells allocate throw { assignment } \ Table to store (partial) assignments
  assignment vn 1+ cells + { dl_lookup }         \ Table to store the dl at which a variable was assigned
  dl_lookup vn 1+ cells +  { dl_marker }         \ Table to mark entries in dl_lookup on next backtrack
  
  \ initialize the assignent & dl lookup table
  vn assignment !
  vn dl_lookup  !
  vn dl_marker  !
  vn 0 u+do
    -1 assignment i 1+ cells + !
    -1 dl_lookup  i 1+ cells + !
    false dl_marker i 1+ cells + !
  loop

  assignment list
;
