# Motivic MZV Proof Notes (Reference-Driven)

Date: 2026-02-26
Scope: motivic multiple zeta values (`StringAlgebra/MZV/Motivic.lean`) and its dependencies.

## 1. Sources Studied

Primary sources:

1. `references/Brown_2012_Mixed_Tate_motives_over_Z_1102.1312.pdf`
2. `references/Brown_2012_Decomposition_of_motivic_MZV_1102.1310.pdf`
3. `references/Brown_2013_Depth_graded_motivic_MZV_1301.3053.pdf`
4. `references/Brown_2014_Motivic_periods_and_P1_minus_3pts_1407.5165.pdf`
5. `references/Brown_2013_Single_valued_periods_and_MZV_1309.5309.pdf`

Supporting sources:

1. `references/Brown_2006_MZV_and_periods_of_M0n_math0606419.pdf`
2. `references/Goncharov_2001_Multiple_polylog_and_mixed_Tate_motives_math0103059.pdf`
3. `references/Racinet_2002_Doubles_melanges_polylog_math0202142.pdf`
4. `references/Kaneko_Noro_Tsurumaki_2007_Double_shuffle_Euler_sums_0705.2267.pdf`

## 2. Core Mathematical Architecture (What the References Actually Prove)

## 2.1 Brown 2012 (Mixed Tate motives over Z)

Anchor results:

1. Theorem 1.1: motivic Hoffman basis `{ζ^m(w): w in {2,3}*}`.
2. Corollary: periods of mixed Tate motives over `Z` are `Q[(2πi)^(-1)]`-linear combinations of corresponding zeta values.

Proof architecture (high level):

1. Construct motivic MZVs inside a graded comodule `H` over the motivic Hopf algebra `A`.
2. Use explicit coaction formula on motivic iterated integrals (Goncharov formula).
3. Introduce `level` filtration by number of `3`s in words over `{2,3}`.
4. Pass from global coaction to infinitesimal derivations `∂_{2n+1}` lowering level by one.
5. Compute the induced maps on level-graded pieces via explicit matrices `M_{N,ℓ}`.
6. Prove matrix invertibility with a `2`-adic valuation argument.
7. Deduce injectivity of level-lowering maps and conclude linear independence by induction on level.
8. Compare counts with known motivic dimension series to upgrade to basis statement.

Formalization takeaway:

1. The mathematically hard step is not a generic Hopf theorem; it is the concrete control of derivations on level-graded words and matrix invertibility.
2. Any Lean plan that skips the matrix/valuation core cannot recover Brown’s theorem as proved in the reference.

## 2.2 Brown 2012 (Decomposition algorithm)

Anchor idea:

1. Given a chosen basis up to weight `N`, define maps into a free noncommutative algebra in symbols `f_{odd}` and `f_2`.
2. Use derivations extracted from coaction to compute coordinates recursively.

Algorithmic structure:

1. Fix weight cutoff `M` and candidate basis `B`.
2. Build an inductive realization map `ρ` on basis generators and products.
3. Define coefficient maps via projection to indecomposables and graded coaction pieces.
4. Compute `∂^φ_{2n+1}` values for new elements.
5. Reconstruct the missing top-weight coordinate as the residual after enforcing derivation constraints.
6. Validate that `ρ` remains an isomorphism; otherwise reject `B`.

Formalization takeaway:

1. This gives a computable normalization/decomposition engine once derivation infrastructure exists.
2. For Lean, this naturally splits into:
   - structural correctness of derivations,
   - finite-dimensional linear algebra at each weight,
   - algorithm correctness theorems.

## 2.3 Brown 2013 (Depth-graded motivic MZVs)

Anchor results:

1. Depth filtration on motivic side and corresponding depth-graded Lie algebra.
2. Linearized double-shuffle Lie algebra framework.
3. Explicit injection from even period polynomials to depth-4 linearized double-shuffle solutions (Theorem 8.3).
4. Conjectural statements connecting exceptional depth-4 elements to motivic Lie algebra.

Proof architecture:

1. Encode motivic data in depth-graded Lie and coalgebra objects.
2. Compare with linearized double-shuffle equations where computations are explicit.
3. Construct modular (period polynomial) elements and show they satisfy linearized equations.
4. Use exact-sequence style control in low depths.
5. Isolate conjectural gap: motivicity of all exceptional elements.

Formalization takeaway:

1. A robust Lean development should separate:
   - proved depth-graded algebra/linearized-shuffle statements,
   - conjectural motivicity statements.
2. Conflating these as plain `def ... : Prop := ...` hides real boundary lines.

## 2.4 Brown 2014 (Motivic periods and `P^1 \ {0,1,∞}`)

Anchor results:

1. Tannakian period formalism specialized to motivic fundamental groupoid.
2. Faithful Galois action statements in this setting.
3. Coaction formulas for motivic iterated integrals and motivic MZVs.
4. Algebraic independence / polynomial generation formulations for motivic MZVs (Hoffman-Lyndon flavor).

Formalization takeaway:

1. `Motivic.lean` should be built on explicit period/coaction API, not ad hoc list lengths.
2. The period map and coaction are central interfaces, not optional wrappers.

## 2.5 Brown 2013 (Single-valued periods and MZV)

Anchor results:

1. Construction of single-valued motivic period map `sv`.
2. Definition of single-valued motivic MZVs and proof they satisfy motivic relations.
3. Structural statements on `H_sv` (generation and Poincare behavior).

Formalization takeaway:

1. Single-valued sector is a natural extension phase once motivic/coaction base is stable.
2. It should be modeled as a derived map from period formalism, not introduced axiomatically.

## 3. Supporting Context from Other References

1. Brown 2006 (`M_{0,n}` periods): geometric period-computation pipeline, primitives in polylog algebras, and geometric origin of shuffle/stuffle compatibility.
2. Goncharov 2001: Hopf algebra viewpoint on polylogarithms/mixed Tate motives; foundational for coaction language.
3. Racinet 2002 + Kaneko-Noro-Tsurumaki 2007: double-shuffle and regularization combinatorics; useful for non-motivic algebraic infrastructure layers.

## 4. Gap Analysis Against Current `Motivic.lean`

Current file status (`StringAlgebra/MZV/Motivic.lean`):

1. Coaction theorems are currently length checks (`...value.length = 2`) and do not encode coassociativity/multiplicativity in algebraic form.
2. Major motivic statements are proposition shells (`def ... : Prop := ...`) rather than theorem obligations.
3. Period algebra is represented by `Set.univ` model, suitable as placeholder but not as semantic endpoint.

Consequence:

1. The file currently captures naming/interface intent, but not the core reference proofs.
2. To align with reference mathematics, theorem obligations must explicitly track the derivation/coaction/filtration machinery.

## 5. Formalization-Ready Proof Skeletons

## 5.1 Hoffman basis route (Brown 2012)

Lean-target skeleton:

1. Define word-level `{2,3}` indexing and level filtration.
2. Define graded pieces and induced maps `∂_{N,ℓ}`.
3. Build symbolic coefficient system for level-1 cuts.
4. Prove compatibility of coaction-derived map with combinatorial matrix representation.
5. Prove `2`-adic valuation criterion for matrix invertibility.
6. Induct on level to get linear independence.
7. Combine with dimension formula to deduce basis.

## 5.2 Decomposition algorithm route

Lean-target skeleton:

1. Define finite-weight truncations and basis records.
2. Define coefficient extraction maps from coaction.
3. Define recursion step for extending decomposition map by one weight.
4. Prove soundness (correct decomposition) and basis-check criterion (injectivity/surjectivity test).

## 5.3 Depth-graded route

Lean-target skeleton:

1. Define depth filtration on motivic algebra modulo `ζ(2)` where needed.
2. Define depth-graded Lie/coalgebra interfaces.
3. Implement linearized double-shuffle equations as explicit polynomial constraints.
4. Construct depth-4 exceptional elements from period polynomials.
5. Prove they satisfy linearized equations.
6. Mark motivicity of all exceptional elements as conjectural boundary unless proved.

## 6. Proof Debt Classification for This Repo

## 6.1 Proved and reusable now

1. Basic combinatorics in shuffle/stuffle files.
2. Simple formal-sum manipulations.

## 6.2 Must be promoted to explicit theorem obligations

1. Brown-structure and depth-graded claims in `Motivic.lean`.
2. Major relation claims in `Relations.lean` and `DoubleShuffle.lean`.
3. Associator-level global claims that currently live as proposition shells.

## 6.3 Conjectural content (must stay flagged)

1. Period conjecture/injectivity type statements.
2. Full motivicity of exceptional depth-4 classes where references state conjectural boundaries.
3. Goncharov-style completeness statements beyond proven low-depth control.

## 7. Immediate Actionable Notes for Next Edits

1. Convert theorem-like proposition shells in `Motivic.lean` into theorem declarations with explicit proof obligations.
2. Replace `coaction_*` length theorems with algebraic equalities over explicit tensor operations.
3. Introduce a dedicated file for graded/filtered structures (`Motivic/Filtered.lean` or similar) before attempting Brown-level theorems.
4. Add an explicit “proved vs conjectural” section in code comments to mirror reference boundaries.

