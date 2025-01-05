: c ( -- )
  10 parse 2drop ; \ parse until the end of line, then drop it

: cnf ( -- ) ; \ Noop

: p ( -- r: nv nc )
  interpret   \ The dimacs problem definition should be a valid word ('cnf')
  interpret   \ The number of variables
  interpret   \ The number of clauses
  0 0 ;       \ Put a marker down

: re-order ( vn cn 0 0 li .. ln 0 lj .. lm 0 -- 0 li .. ln 0 lj .. lm cn vn )

  0 >r \ Put a marker on the return stack
  begin
    2dup + while
    >r begin dup while >r repeat \ Move one clause to the return stack
  repeat
  2drop  \ ( vn cn )

  { vn cn }
  
  begin
    r@ r@ + while
    0 begin r> dup while repeat drop
  repeat
  r> drop \ Drop the marker from the return stack

  cn vn
;

: dimacs ( c-addr u -- 0 li .. ln 0 lj .. lm cn vn )
  included      \ Parse the specified file
  re-order      \ Re-order the stack so we have the metadata on top
 ;