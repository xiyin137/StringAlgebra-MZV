# MZV Soundness TODO (Dependency-Driven)

Date: 2026-02-26

This file tracks semantic and proof debt for `StringAlgebra/MZV` under `agent.md` rigor rules.

## Current Verified State

1. `lake build StringAlgebra.MZV` passes.
2. `StringAlgebra/MZV/*.lean` is `sorry`-free (proof-level `sorry` count: 0).
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in MZV Lean files.
4. Placeholder `True := trivial` stubs have been removed from the main MZV interfaces.
5. `DoubleShuffle.lean` end-stage contracts were tightened: coaction/motivic compatibility are explicit map-parameterized properties, finite-generation is phrased via finite bases, and the implemented Ihara derivation now has explicit additive and basic structural lemmas.
6. Redundant tautological endpoint shells were removed from `DoubleShuffle.lean` (direct `Iff.rfl` theorem wrappers of definitions).
7. Additional unused tautological example equalities were removed from `Basic.lean`, `Relations.lean`, `Motivic.lean`, and `Polylogarithm.lean` to reduce non-semantic surface area.
8. Additional unused tautological arithmetic/weight wrappers were removed from `Basic.lean`, `Relations.lean`, and `Motivic.lean` (`zeta21_weight`, `bk_values`, `zeta3_eq_f3`, `zeta5_eq_f5`, `weight8_relation`).
9. Misleading relation-labeled theorem shells that only proved weight equalities were removed from `DoubleShuffle.lean`/`Motivic.lean` (`zeta21_eq_zeta3`, `weight4_relations`, `motivic_zeta21_eq_zeta3`), alongside the unused definitional wrapper `hoffmanCount_recurrence`.

## MZV Dependency Graph

```text
Basic
  ├─> ShuffleAlgebra
  ├─> StuffleAlgebra
  └─> Polylogarithm

ShuffleAlgebra + StuffleAlgebra -> DoubleShuffle
ShuffleAlgebra -> IteratedIntegral
DoubleShuffle -> Relations
DoubleShuffle -> Motivic
Motivic -> Associator
```

## Theorem Flow Toward Motivic/Associator Pipeline

```text
Basic composition/word infrastructure
-> shuffle + stuffle products
-> double shuffle compatibility/regularization interface
-> motivic MZV/coaction interface
-> Drinfeld associator interface
```

## Audit Matrix

1. `Basic.lean`: low risk. Core composition/word invariants are explicit and proved.
2. `ShuffleAlgebra.lean`: medium risk. Core shuffle combinatorics are present; full associativity closure remains as explicit proposition-level target.
3. `StuffleAlgebra.lean`: medium risk. Quasi-shuffle combinatorics are present; full associativity closure remains tracked as proposition-level target.
4. `DoubleShuffle.lean`: medium-high risk. Relation and regularization interfaces are explicit; full derivation pipeline remains pending.
5. `Relations.lean`: medium-high risk. Classical relation families are encoded; major conjectural/high-weight closures remain proposition-level contracts.
6. `IteratedIntegral.lean`: medium risk. Differential-form and shuffle interfaces are explicit; full analytic convergence bridge remains pending.
7. `Polylogarithm.lean`: medium-high risk. Polylog/HPL interfaces are explicit; analytic continuation and deep functional equations remain pending.
8. `Motivic.lean`: medium-high risk. Motivic/coaction structure is explicit; full Hopf-algebra and period-isomorphism closure remains pending.
9. `Associator.lean`: high risk. Associator and GT interfaces are explicit; full pentagon/hexagon derivations from constructed coefficients remain pending.
10. `DoubleShuffle.lean` keeps explicit finite-generation/motivic interfaces while avoiding tautological endpoint wrappers.

## Open Work Packages

### WP1 - Product Algebra Closure

Targets: `ShuffleAlgebra.lean`, `StuffleAlgebra.lean`, `DoubleShuffle.lean`

1. Prove full associativity/distributivity closure for shuffle and stuffle structures.
2. Connect regularization maps to these algebraic laws by explicit compatibility lemmas.
3. Promote proposition-level relation shells to theorem-level consequences.

### WP2 - Relations Internalization

Target: `Relations.lean`

1. Derive low-weight sum/duality/Ohno consequences from implemented product infrastructure.
2. Replace declaration-style proposition wrappers with theorem statements where infrastructure is sufficient.
3. Maintain explicit separation between proved theorems and conjectural statements.

### WP3 - Motivic Hopf Closure

Targets: `Motivic.lean`, `Associator.lean`

1. Strengthen coaction identities into explicit Hopf-compatibility lemmas.
2. Connect motivic generators to associator coefficient interfaces by explicit maps.
3. Tighten GT/associator bridge statements from interface-level contracts toward derived theorems.

### WP4 - Polylog/Iterated Integral Bridge

Targets: `IteratedIntegral.lean`, `Polylogarithm.lean`

1. Expand bridge lemmas from iterated-integral words to polylog/HPL encodings.
2. Formalize more functional-equation steps (inversion, duplication, distribution) from explicit identities.
3. Track analytic assumptions explicitly and minimize external contracts.

## Anti-Smuggling Gates

1. No `axiom`.
2. No `sorry`.
3. No fabricated outputs disguised as canonical constructions.
4. Conjectural content must remain clearly marked as conjectural/interface-level, not as proved theorem.
