# StringAlgebra-MZV

Lean 4 formalization of multiple zeta values and related algebraic structures.

## Scope

1. `StringAlgebra/MZV/Basic.lean`
2. `StringAlgebra/MZV/ShuffleAlgebra.lean`
3. `StringAlgebra/MZV/StuffleAlgebra.lean`
4. `StringAlgebra/MZV/DoubleShuffle.lean`
5. `StringAlgebra/MZV/Relations.lean`
6. `StringAlgebra/MZV/IteratedIntegral.lean`
7. `StringAlgebra/MZV/Polylogarithm.lean`
8. `StringAlgebra/MZV/Motivic.lean`
9. `StringAlgebra/MZV/Associator.lean`

## Build

```bash
lake build StringAlgebra.MZV
```

## Audit

```bash
rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/MZV --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/MZV --glob '*.lean'
```

## Status (2026-02-26)

1. Theorem-level `sorry` count: `0`
2. No assumption-bundle wrapper classes.
3. No hidden-choice smuggling patterns.

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. VOA: https://github.com/xiyin137/StringAlgebra-VOA
3. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity
4. MTC: https://github.com/xiyin137/StringAlgebra-MTC
