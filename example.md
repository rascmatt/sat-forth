gforth main.fs dimacs.fs utils.fs

-- Example 1 (sat):

"../dimacs/t1.cnf" dimacs prepare
is-sat

-- Example 2 (unsat):

"../dimacs/t4.cnf" dimacs prepare
is-sat

-- Example 3 (sat):

"../dimacs/uf20-01.cnf" dimacs prepare
is-sat

-- Example 4 (sat):

"../dimacs/uf20-0101.cnf" dimacs prepare
value l0 value a0 a0 l0
is-sat
