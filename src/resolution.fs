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
