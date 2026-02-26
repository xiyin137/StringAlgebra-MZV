# StringAlgebra MZV

Standalone extraction of `StringAlgebra.MZV` from the StringAlgebra monorepo.

## Status (2026-02-26)

1. Theorem-level `sorry` count in `StringAlgebra/MZV`: 0
2. Anti-smuggling policy: no `axiom` smuggling, no assumption-bundle wrapper classes.
3. Build target: `lake build StringAlgebra.MZV`

## Quick Audit Commands

```bash
lake build StringAlgebra.MZV
rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/MZV --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/MZV --glob '*.lean'
```
