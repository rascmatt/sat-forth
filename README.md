# Forth SAT Solver

A SAT solver implemented in Forth, using **clause learning** and **conflict-driven backtracking**. This project is designed to solve Boolean satisfiability (SAT) problems and represents an ongoing effort to integrate modern techniques with a minimalist and stack-based language like Forth.

## Features

- **Clause Learning**: Implements conflict-driven clause learning (CDCL), allowing the solver to learn from conflicts and avoid repeating the same mistakes.
- **Conflict-Driven Backtracking**: Efficiently backtracks to the point of conflict rather than simple chronological backtracking.
- **First UIP Scheme**: Utilizes the **first Unique Implication Point (UIP)** scheme to learn an asserting clause during conflict analysis, which helps in faster backtracking.
- **Implication Graph**: Uses an implication graph represented directly on the Forth data stack to track decisions and implications.
- **Resolution Calculus**: Calculates learned clauses using the resolution calculus after conflicts are detected.

## Overview of How It Works

1. **Input Format**: The solver accepts problems in **DIMACS CNF format**. Each problem is represented as a series of clauses with literals, and the problem is processed into an intermediate format on the Forth data stack.
   
2. **Implication Graph**: 
   - The Forth **data stack** represents the implication graph, where literals and their dependencies are tracked as the solver explores possible variable assignments.
   - The implication graph is used to determine implications of decisions (unit propagation) and can be directly referenced during conflict analysis and backtracking.

3. **First UIP Clause Learning**:
   - During conflict analysis, the solver identifies the **first Unique Implication Point (UIP)** in the implication graph, which is a crucial decision point. 
   - The solver then learns an **asserting clause** that helps avoid similar conflicts in the future, improving the efficiency of subsequent searches.

4. **Conflict Detection and Clause Learning**:
   - When a conflict is detected (i.e., a set of clauses cannot all be satisfied), the solver performs **conflict analysis**.
   - **Learned clauses** are generated using the **resolution calculus** to help avoid repeating the same conflicting assignments in the future.
   
5. **Conflict-Driven Backtracking**:
   - Instead of backtracking chronologically through decisions, the solver **backtracks to the second highest decision level** involved in the conflict clause, reducing unnecessary recomputation.

## Limitations

- **Naive Data Structures**: The clause working set is currently implemented as a simple linked list, on the dictionary. This does not only introduce access delays due to its non-optimised structure, it also introduces memory restrictions, as the dictionary space in forth is limited quite strictly.
- **Basic Decision Heuristics**: The solver does not yet include any advanced decision heuristics. Essentially it chooses the next free variable to assign, without any heuristics to aid the decision.
