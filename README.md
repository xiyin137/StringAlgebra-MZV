# StringAlgebra-MZV

Lean 4 formalization of multiple zeta values (MZVs), with an active focus on motivic/coaction infrastructure in the direction of Francis Brown's program.

## Repository Scope

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

Targeted motivic build:

```bash
lake build StringAlgebra.MZV.Motivic
```

## Verification/Audit Commands

```bash
rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean' | wc -l
rg -n '^\s*axiom\b|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/MZV --glob '*.lean' | wc -l
rg -n '^\s*def\s+.*:\s*Prop\b' StringAlgebra/MZV --glob '*.lean' | wc -l
rg -n '\btheorem\b' StringAlgebra/MZV --glob '*.lean' | wc -l
rg -n 'native_decide' StringAlgebra/MZV/Motivic.lean | wc -l
```

## Status (2026-02-27, locally verified)

1. `sorry` count in `StringAlgebra/MZV`: `0`
2. `axiom`/`admit`/`unsafe` count in `StringAlgebra/MZV`: `0`
3. Proposition-shell count (`def ... : Prop`): `93` (explicit spec/conjectural interfaces)
4. `theorem` token count in `StringAlgebra/MZV`: `533`
5. `native_decide` uses in `Motivic.lean`: `11`
6. Build status: `lake build StringAlgebra.MZV` passes

## Working Documents

1. `MOTIVIC_MZV_DEVELOPMENT_PLAN.md` - motivic roadmap and milestones.
2. `MOTIVIC_MZV_PROOF_NOTES.md` - proof notes and mathematical rationale.
3. `CLAUDE_ISSUES_REMEDIATION.md` - tracked remediation of critique items.
4. `claude_to_codex.md` - critique source document.

## References/Reading

1. `references/` stores downloaded reference papers.
2. `read_references.py` provides local PDF text extraction helpers.

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. VOA: https://github.com/xiyin137/StringAlgebra-VOA
3. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity
4. MTC: https://github.com/xiyin137/StringAlgebra-MTC
