\ Utilities to parse CNFs from DIMACS file definitions

: consume-whitespace ( addr u -- addr u )
  
  dup 0= IF exit THEN
  
  over -rot     ( addr addr u )
  chars + swap  ( limit addr )
  begin
    2dup swap <        ( limit addr b )
    over c@ 32 = and   ( limit addr b )
    WHILE char+
  repeat
  dup -rot      ( addr limit addr )
  -             ( addr u )
;

: consume-sign  ( addr u -- addr u b )
  
  dup 0= IF true EXIT THEN
  
  over c@ dup '+' = IF
    \ Consume the '+' character
    drop
    swap char+ swap 1-
    true
  ELSE
    '-' = IF
        \ Consume the '-' character
        swap char+ swap 1-
        false
    ELSE true THEN
  THEN
;

: consume-literal ( addr u -- addr u li )

  dup 0= IF ." Attepted to parse 0 length string as literal." -1 throw THEN

  consume-whitespace
  consume-sign >r    ( addr u )
  0 0 2swap          ( 0 0 addr u )
  >number            ( d d addr u )
  2swap d>s            ( addr u n )
  r> 0= IF negate THEN ( addr u li )
;

: parse-clause ( addr u -- li .. ln )
  begin             ( addr u)
    dup 0<> while   ( addr u)
        consume-literal ( addr u li )
        dup 0= IF
            drop drop drop exit
        THEN
        -rot
  repeat
  drop drop
;

: parse-dimacs ( addr u -- 0 li .. ln 0 lj .. lm cn vn )
    \ Read a propositional formula from a DIMACS definition in the file
    \ with the specified file name

    \ Open the file
    r/o open-file throw >r

    \ Reserve memory to store number of variables (vn) and clauses (cn)
    align here cell allot { vn } -1 vn !
    align here cell allot { cn } -1 cn !

    align here 256 chars allot { line-buffer }

    BEGIN ( )
        \ Read each line from the file
        line-buffer 256 r@ read-line throw ( n f ) WHILE ( n )

        dup 0<> IF ( n ) \ Only process non-empty lines
            line-buffer swap     ( addr n )
            consume-whitespace   ( addr n )
            over c@              ( addr n c )

            dup 'c' <> IF        ( addr n c )
                'p' = IF         ( addr n )
                    over 5 s" p cnf" compare 0<> IF ." Expected problem type 'CNF'." -1 throw THEN
                    \ Advance to the cn & vn definition
                    5 + swap 5 chars + swap ( addr n )
                    consume-literal vn !    ( addr n )
                    consume-literal cn !    ( addr n )
                ELSE              ( addr n )
                    0 -rot        ( 0 addr n )
                    parse-clause  ( 0 l1 .. ln )
                    0 0           \ add two dummy values for the drops later
                THEN
            ELSE drop THEN
            ( addr n )
            swap drop ( n )
        THEN ( n )
        drop
    REPEAT ( n )
    drop   ( )

    \ Close the file
    r> close-file throw

    \ Push the number of clauses (cn) and number of variables (vn)
    cn @ vn @
;

: lf ( -- )
  10 emit
;

: dump-dimacs { a_addr l_addr -- }
  \ Output the current clause set in DIMACS format to stdout
  
  a_addr @ { vn }
  l_addr get-clause-list-length { cn }

  \ Print the problem line
  lf ." p cnf " vn . cn . 
  lf

  l_addr
  begin              ( l_addr )
      dup -1 > WHILE ( l_addr )
          dup get-clause  ( l_addr li1 .. li2 n )
          0 u+do
            .
          loop ( l_addr )
          ." 0" lf
          dup @ 1+ cells + @ ( l+1_addr )
  repeat ( -1 )
  drop
;
