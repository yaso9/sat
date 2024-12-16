# A Very Simple SAT Solver

This is a simple implementation of a CDCL (Conflict-Driven Clause Learning) SAT
solver I wrote the learn the CDCL algorithm.

## Features

- CDCL-based solving algorithm
- DIMACS CNF file format support
- Conflict clause learning
- Non-chronological backtracking
- Variable selection heuristic based on literal occurrence counting

## Building

Requires a C++17 (or later) compiler. To compile:

```bash
g++ -O2 -std=c++17 sat.cc -o sat
```

## Usage

```bash
./sat <dimacs_cnf_file>
```

The program will output:
- Whether the formula is satisfiable (SAT/UNSAT)
- If SAT, a satisfying assignment for each variable
