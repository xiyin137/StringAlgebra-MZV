# MZV Formalization Status — Honest Assessment

Date: 2026-03-05 (updated)

## Build Status

1. `lake build StringAlgebra.MZV` passes.
2. No `axiom`/`admit` usage.
3. No theorem-level `sorry` remains.
4. `native_decide` count in `Motivic.lean`: 11 (used for small matrix kernel checks).

## Honesty Notes

### What is actually proved

The proved content is limited to **basic combinatorics on lists**:

- **Basic.lean**: Weight/depth additivity, reversal, composition-to-word conversions.
  `hoffman_composition_exists` proves that Hoffman compositions of each weight ≥ 2 exist
  (a purely combinatorial fact, NOT Brown's theorem about MZV bases).
- **ShuffleAlgebra.lean**: Correct recursive shuffle product, length preservation,
  commutativity (as multisets), binomial coefficient count of shuffles, and
  associativity as a theorem.
- **StuffleAlgebra.lean**: Correct recursive stuffle product, weight preservation,
  commutativity, and **associativity** (fully proved). Helper infrastructure includes
  `perm_transpose_3x3`, `perm_deinterleave`, and stuffle key lemmas for the 9-term expansion.
- **IteratedIntegral.lean**: Duality involution correctly defined and proved involutive.
  Weight/depth preservation for form words.
- **DoubleShuffle.lean**: Formal sum algebra operations. Weight-raising derivation
  distributes over formal sum addition (trivial). Zagier dimension recurrence
  is immediate from the definition.
- **Motivic.lean**: Low-weight matrix infrastructure (lines ~700-5300) correctly
  computes specific small matrices and verifies trivial kernels via `native_decide`.
  The depth-1 primitive coaction (Δ(m) = m⊗1 + 1⊗m) is trivially coassociative
  and multiplicative by case analysis.

### What is NOT proved (but may appear "proved")

- **Coaction model**: The coaction in `Motivic.lean` is a **depth-1 primitive model**
  (every element is primitive). This is NOT Brown's admissible-cut coaction.
  The "coassociativity" and "multiplicativity" theorems are trivially true for
  any primitive coaction in any Hopf algebra.

- **Prop-as-Definition pattern**: Many mathematical statements are encoded as
  `def ... : Prop` parameterized by abstract evaluation maps. These are
  *specifications* (what it means for an evaluation map to satisfy the relation),
  not proved theorems. Examples: `sum_formula_general`, `duality_relation`,
  `mzv_shuffle_product`, `extendedDoubleShuffle`, all `*_conjecture` defs.

- **MotivicMZV structure**: The `weight` and `depth` fields are free metadata
  not structurally tied to the formal sum. `WellFormed` checks consistency
  but is not enforced by the type system.

### What was removed/fixed in this audit

1. **Associator.lean** — Complete rewrite:
   - Pentagon/hexagon equations were mathematically incorrect (were trivial
     properties of word concatenation, not the actual coherence conditions).
     Now stated correctly as specifications requiring multi-variable substitution.
   - `GTElement` duality condition now correctly swaps A↔B (was trivially true before).
   - `GRTElement` now requires antisymmetry under A↔B swap.
   - `PureBraidWord` now correctly computes the induced permutation.
   - `KontsevichIntegral` replaced `String` knot field with `ChordDiagram` formalism.
   - Removed vacuous theorems (`kontsevich_unknot`, `kz_braid_representation`,
     `associator_parallel_transport_conjecture`, `chern_simons_connection_conjecture`,
     `kz_cft_origin_conjecture`, `lmo_universal_conjecture`).

2. **Basic.lean**: `brown_hoffman_basis` renamed to `hoffman_composition_exists`
   with honest docstring (it's combinatorics, not Brown's theorem).

3. **IteratedIntegral.lean**: Removed vacuous `deRhamRealization`/`bettiRealization`
   type aliases and the trivial `deRham_Betti_comparison` "theorem" (which just
   wrapped a word in a singleton list). `formWordPeriodMap` renamed to `formWordDepth`.

4. **Polylogarithm.lean**: `BlochGroup` (was `Set.univ` with trivial closure)
   replaced with `PreBlochGenerator`/`PreBlochGroup`/`BlochFiveTermRelation`.

5. **Motivic.lean**: Honest documentation added to `MotivicMZV`, coaction model,
   `MotivicGaloisGroup`. `feynman_integral_connection` renamed to
   `motivicPeriodMap_mem_toyPeriodAlgebra` with honest docstring (tautological).
   `motivicGaloisGroup` renamed to `trivialGaloisAction`.

6. **Relations.lean**: `odd_zeta_independence_conjecture` was stating injectivity
   (ζ(n) ≠ ζ(m)), not algebraic independence. Replaced with honest interface
   noting that proper formalization requires `MvPolynomial`.

7. **DoubleShuffle.lean**: `ihara_lie_algebra` (claiming Lie structure but only
   proving linearity) replaced with honest `weightRaiseDerivation_additive`.
   `zagier_generating_function` (Prop def) converted to `zagier_dimension_recurrence`
   (trivially proved theorem).

### Second audit fixes

8. **IteratedIntegral.lean**: `duality_theorem` renamed to `duality_involutive_convergent`
   with honest docstring — it only proves combinatorial involutivity, not integral equality.

9. **Motivic.lean**:
   - `period_conjecture` was FALSE in the toy model (`motivicPeriodMap` sums coefficients,
     so distinct elements map to the same value). Now parameterized by an abstract
     period map `per : MotivicMZV → R`.
   - `cosmic_galois_conjecture` was trivially provable (satisfied by `trivialGaloisAction`).
     Now requires both per-equivariance and non-triviality of the action,
     parameterized by an abstract period map.

10. **Associator.lean**:
    - `low_degree_expansion` was tautological (existentially quantified `zeta2`/`zeta3`
      could be chosen as whatever the coefficients are). Now takes `zeta2`/`zeta3` as
      parameters and additionally requires degree-1 coefficients to vanish.
    - `coefficients_are_MZVs` was too weak (allowed different witness per word, didn't
      express ℚ-linear combinations). Now requires finite ℚ-linear combinations with
      a universal evaluation map and weight compatibility.
    - `kontsevich_multiplicative_conjecture` was vacuous (∃ K₃ always satisfiable).
      Now parameterized by abstract knot type with connected sum operation.

### Third audit fixes

11. **StuffleAlgebra.lean**: `double_shuffle_relation` was vacuous (existentially
    quantified both evaluation maps — satisfied by zero maps). Now takes `ζw`
    and `ζc` as parameters.

12. **Polylogarithm.lean**: `BlochFiveTermRelation` was vacuous (only asserted
    existence of generators with correct values, missing the actual "= 0"
    relation). Now includes `ev x - ev y + ev g₃ - ev g₄ + ev g₅ = 0`.

13. **Relations.lean**:
    - `ohno_relation_conjecture` was vacuous (universally quantified over ALL
      lists satisfying weight/depth constraints). Now correctly enumerates
      specific compositions via `distributions`/`addHeights`/`ohnoTerms`.
    - `odd_zeta_independence_conjecture` concluded with `→ True` (tautological).
      Now properly expresses algebraic independence as: no non-trivial polynomial
      with distinct monomials evaluates to zero.
    - `sumFormulaTerms` had off-by-one: `List.range (n - 1)` gave k ∈ [2, n]
      instead of k ∈ [2, n-1]. Fixed to `List.range (n - 2)`.

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

## Critical Open Work

### WP0 — Foundational Gaps (Highest Priority)

1. ~~**Prove shuffle/stuffle associativity**~~ — **DONE** (2026-03-05).
   Both `shuffle_assoc` and `stuffle_assoc` fully proved by well-founded induction
   with 3×3 block transpose and column-combining strategy.
2. **Replace depth-1 primitive coaction** with Brown's admissible-cut coaction.
   This is the single most impactful change for mathematical content.
3. **Enforce MotivicMZV invariants** — either make weight/depth computed fields
   or use a subtype with WellFormed.

### WP1 — Product Algebra Closure

Targets: `ShuffleAlgebra.lean`, `StuffleAlgebra.lean`, `DoubleShuffle.lean`

1. ~~Prove associativity for shuffle and stuffle.~~ — **DONE** (2026-03-05).
2. Connect regularization maps by explicit compatibility lemmas.
3. Prove concrete double shuffle relations (e.g., ζ(2,1) = ζ(3)).

### WP2 — Relations Internalization

Target: `Relations.lean`

1. Derive low-weight sum/duality/Ohno consequences from product infrastructure.
2. Formalize `odd_zeta_independence_conjecture` properly using `MvPolynomial`.

### WP3 — Motivic Hopf Closure

Targets: `Motivic.lean`, `Associator.lean`

1. Implement Brown's admissible-cut coaction.
2. Prove non-trivial coaction identities.
3. Formalize pentagon/hexagon with multi-variable NC series infrastructure.

### WP4 — Analytic Bridge

Targets: `IteratedIntegral.lean`, `Polylogarithm.lean`

1. Formalize period map (requires Mathlib integration theory).
2. Connect iterated integral representation to MZV evaluation.

## Anti-Smuggling Gates

1. No `axiom`.
2. No fabricated outputs disguised as canonical constructions.
3. Conjectural content must be clearly marked as `*_conjecture` or as `def ... : Prop`.
4. Documentation must honestly describe what is and is not proved.
5. Definitions must be mathematically correct, not "simplified" placeholders.
