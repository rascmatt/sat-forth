require main.fs

: prepare ( 0 li .. ln 0 lj .. lm cn vn -- a_addr l_addr )
  \ For a list of clauses, initialize the tables and clause list for the SAT solver
  \ cn .. Number of clauses
  \ vn .. Number of variables

  { cn vn }
  cn create-clause-list { list }
  
  here align vn 2 * 2 + cells allot { assignment }
  assignment vn 1+ cells + { dl_lookup }
  
  \ initialize the assignent & dl lookup table
  vn assignment !
  vn dl_lookup  !
  vn 0 u+do
    -1 assignment i 1+ cells + !
    -1 dl_lookup  i 1+ cells + !
  loop

  assignment list
;
