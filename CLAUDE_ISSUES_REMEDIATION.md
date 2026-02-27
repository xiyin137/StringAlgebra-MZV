# Claude-to-Codex Remediation Tracker

Date: 2026-02-27
Source: `claude_to_codex.md`

## Section 3 (Vacuous Shells)

1. `Polylogarithm.lean` status: addressed
   - Replaced vacuous shells with explicit conjecture interfaces (`*_conjecture`) whose bodies encode actual functional-equation/distribution style statements.

2. `Relations.lean` status: addressed
   - Replaced vacuous relation shells with nontrivial conjectural statements.
   - Promoted `hoffman_basis_theorem` to a real theorem via `brown_hoffman_basis`.

3. `Associator.lean` status: addressed
   - Removed `DrinfeldAssociator.groupLike` assumption field.
   - Replaced vacuous CFT/LMO/parallel-transport shells with explicit conjecture interfaces.
   - Strengthened pentagon/hexagon equations so they are no longer definitional tautologies.

4. `DoubleShuffle.lean` status: addressed
   - Replaced vacuous `extendedDoubleShuffle` append-commutativity shell with regularized evaluation equality.
   - Added semantic relation `FormalSum.Equivalent`.

5. `Motivic.lean` conjecture shells status: addressed
   - `motivic_lie_algebra_conjecture` and `cosmic_galois_conjecture` were rewritten as nontrivial interfaces.
   - `PeriodAlgebra` is no longer `Set.univ`; now modeled as `Set.range motivicPeriodMap`.

## Section 11 (Deep Architectural Findings)

1. Wrong derivation model (`iharaDerivComp`) status: partially addressed
   - Added explicit naming split (`weightRaiseDerivComp`, `weightRaiseDerivation`) to prevent conflation with Brown's weight-lowering coaction derivations.
   - Full Brown-style derivation rebuild remains open.

2. `native_decide` reliance status: partially addressed
   - Current count in `Motivic.lean`: `11` (down from `62` at initial audit, and from `19` before this pass).
   - Replaced a subset of low-complexity proof obligations with structural `simp`/`decide`
     (notably finite-index witnesses, finite-development count evaluation, and column-equality checks).
   - Remaining `native_decide` sites are concentrated in explicit low-weight coefficient extraction
     and two kernel-witness scalar equalities where reduction gets stuck under `decide`.

3. Repetitive low-weight boilerplate status: partially addressed
   - Partial automation landed:
     - unified key-indexed generators for low-weight step reports, matrix-injectivity reports,
       and consistency reports;
     - canonical key lists now drive core/extended/augmented report families;
     - added simp-normalization lemmas so downstream proofs use generated lists transparently.
   - Full tactic/metaprogram abstraction is still open.

4. Unverified weight/depth metadata status: partially addressed
   - Added `MotivicMZV.WellFormed` with boundedness checks and preservation lemmas for `zero/one/add/smul/neg/sub`.

5. Missing algebraic instances status: partially addressed
   - Added notation-level instances (`Zero`, `One`, `Add`, `Mul`, `Neg`, `Sub`, `SMul`).
   - Full algebraic law instances (`AddCommMonoid`, `Ring`, `Algebra`) remain open.

6. Level block completeness proofs status: open
   - Manual block lists remain; completeness/independence theorems are pending.

7. `FormalSum.normalize` / boolean equivalence correctness status: partially addressed
   - Added semantic `FormalSum.Equivalent`.
   - Soundness/completeness theorem for `heuristicEquiv` and normalization correctness remains open.

8. Brown step `3 -> 2` zero-matrix confusion status: partially addressed
   - Current infrastructure now names weight-raising behavior explicitly.
   - Mathematical fix still depends on full coaction-derived derivation implementation.

## Current Metrics

1. Build: `lake build StringAlgebra.MZV` passes.
2. `sorry` count: `0`.
3. `def ... : Prop` count: `90`.
4. `theorem` count: `512`.
5. `native_decide` count in `StringAlgebra/MZV/Motivic.lean`: `11`.
