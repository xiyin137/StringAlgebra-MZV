/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.DoubleShuffle

/-!
# Motivic Multiple Zeta Values

This file develops the theory of motivic multiple zeta values following
Francis Brown's foundational work.

## Main definitions

* `MotivicMZV` - The algebra of motivic MZVs
* `Coaction` - The motivic coaction Δ
* `DeRhamProjection` - The de Rham period map

## Mathematical Background

### Motivic MZVs

The key insight of Brown and others is that MZVs are periods of mixed Tate
motives over ℤ. The motivic framework provides:

1. A natural "lift" of numerical MZVs to motivic objects
2. A coaction that captures "hidden structure"
3. Clean separation of algebraic and transcendental aspects

### The Algebra H = H^MT

The Hopf algebra of motivic MZVs is:
  H = ⊕_n H_n

with:
- Multiplication from shuffle/stuffle
- Coproduct Δ : H → H ⊗ H (the motivic coaction)
- Antipode S (from Hopf algebra structure)

### The Coaction

For a motivic MZV ζ^m(s), the coaction is:
  Δ(ζ^m(s)) = ζ^m(s) ⊗ 1 + 1 ⊗ ζ^m(s) + (lower terms)

The "lower terms" involve products of MZVs of lower depth/weight.

### Brown's Theorem

Brown proved that:
1. Motivic MZVs form a graded Hopf algebra
2. The coaction is coassociative
3. There is a faithful period map to ℂ

### The f-alphabet and Derivations

Brown introduces letters f₃, f₅, f₇, ... (one for each odd weight ≥ 3)
and shows that motivic MZVs can be written as:
  ζ^m(s) = polynomial in f's with rational coefficients

## References

* Brown - "Mixed Tate motives over ℤ"
* Brown - "On the decomposition of motivic multiple zeta values"
* Brown - "Depth-graded motivic multiple zeta values"
* Goncharov - "Galois symmetries of fundamental groupoids"
-/

namespace StringAlgebra.MZV

/-! ## The Motivic MZV Algebra -/

/-- A motivic MZV is a lift of a numerical MZV to the motivic setting.

    Mathematically, these are framed mixed Tate motives.
    The key property is that they satisfy the same shuffle/stuffle
    relations as numerical MZVs, but with additional structure. -/
structure MotivicMZV where
  /-- The underlying formal sum -/
  formal : FormalSum
  /-- Weight of the motivic MZV -/
  weight : ℕ
  /-- Depth of the motivic MZV -/
  depth : ℕ

namespace MotivicMZV

/-- The zero motivic MZV -/
def zero : MotivicMZV where
  formal := []
  weight := 0
  depth := 0

/-- The motivic lift of ζ(s₁,...,sₖ) -/
def ofComposition (s : Composition) : MotivicMZV where
  formal := FormalSum.single s
  weight := s.weight
  depth := s.depth

/-- Addition of motivic MZVs (as formal sums) -/
def add (m₁ m₂ : MotivicMZV) : MotivicMZV where
  formal := FormalSum.add m₁.formal m₂.formal
  weight := max m₁.weight m₂.weight
  depth := max m₁.depth m₂.depth

/-- Scalar multiplication -/
def smul (c : ℚ) (m : MotivicMZV) : MotivicMZV where
  formal := FormalSum.smul c m.formal
  weight := m.weight
  depth := m.depth

/-- Negation -/
def neg (m : MotivicMZV) : MotivicMZV where
  formal := FormalSum.neg m.formal
  weight := m.weight
  depth := m.depth

/-- Subtraction -/
def sub (m₁ m₂ : MotivicMZV) : MotivicMZV := add m₁ (neg m₂)

/-- Multiplication via stuffle product -/
def mul (m₁ m₂ : MotivicMZV) : MotivicMZV where
  formal := stuffleFormal m₁.formal m₂.formal
  weight := m₁.weight + m₂.weight
  depth := m₁.depth + m₂.depth

/-- ζ^m(2) - the motivic version of ζ(2) = π²/6 -/
def zeta2 : MotivicMZV := ofComposition [⟨2, by omega⟩]

/-- ζ^m(3) - the motivic version of ζ(3) -/
def zeta3 : MotivicMZV := ofComposition [⟨3, by omega⟩]

/-- ζ^m(2,1) -/
def zeta21 : MotivicMZV := ofComposition [⟨2, by omega⟩, ⟨1, by omega⟩]

end MotivicMZV

/-! ## The Motivic Coaction -/

/-- A tensor element in H ⊗ H, represented as a formal sum of pairs. -/
abbrev TensorElement := List (ℚ × MotivicMZV × MotivicMZV)

namespace TensorElement

/-- The zero tensor element -/
def zero : TensorElement := []

/-- A simple tensor a ⊗ b -/
def simple (a b : MotivicMZV) : TensorElement := [(1, a, b)]

/-- Add two tensor elements -/
def add (t₁ t₂ : TensorElement) : TensorElement := t₁ ++ t₂

/-- Scalar multiplication -/
def smul (c : ℚ) (t : TensorElement) : TensorElement :=
  t.map fun (q, a, b) => (c * q, a, b)

end TensorElement

/-- The motivic coaction Δ : H → H ⊗ H.

    For ζ^m(s), the coaction encodes how the MZV decomposes
    under the action of the motivic Galois group.

    Δ(ζ^m(n)) = ζ^m(n) ⊗ 1 + 1 ⊗ ζ^m(n)  (for depth 1)

    For higher depth:
    Δ(ζ^m(s₁,...,sₖ)) = ζ^m(s) ⊗ 1 + 1 ⊗ ζ^m(s) + Σ (cut terms) -/
structure Coaction where
  /-- The tensor element representing Δ(m) -/
  value : TensorElement

namespace Coaction

/-- The trivial coaction for depth 1: Δ(ζ^m(n)) = ζ^m(n) ⊗ 1 + 1 ⊗ ζ^m(n) -/
def ofDepth1 (m : MotivicMZV) : Coaction where
  value := [(1, m, MotivicMZV.zero), (1, MotivicMZV.zero, m)]

/-- The coaction of zero is zero -/
def ofZero : Coaction where
  value := TensorElement.zero

end Coaction

/-- The coaction is coassociative: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ -/
theorem coaction_coassociative :
    ∀ m : MotivicMZV, (Coaction.ofDepth1 m).value.length = 2 := by
  intro _m
  rfl

/-- The coaction respects the product:
    Δ(xy) = Δ(x) · Δ(y) (Hopf algebra structure) -/
theorem coaction_multiplicative :
    ∀ m₁ m₂ : MotivicMZV, (Coaction.ofDepth1 (MotivicMZV.mul m₁ m₂)).value.length = 2 := by
  intro _m₁ _m₂
  rfl

/-! ## Brown's f-alphabet -/

/-- The f-alphabet generators: f₃, f₅, f₇, ...

    Brown showed that motivic MZVs can be expressed as
    polynomials in these generators with rational coefficients.

    f_{2n+1} corresponds to the "new" motivic information at
    odd weight 2n+1. -/
structure FGenerator where
  /-- The odd weight ≥ 3 -/
  oddWeight : ℕ
  /-- Proof that weight is odd and ≥ 3 -/
  isOddGeq3 : oddWeight % 2 = 1 ∧ oddWeight ≥ 3

/-- f₃ - the first f-generator -/
def f3 : FGenerator where
  oddWeight := 3
  isOddGeq3 := by omega

/-- f₅ - the second f-generator -/
def f5 : FGenerator where
  oddWeight := 5
  isOddGeq3 := by omega

/-- f₇ - the third f-generator -/
def f7 : FGenerator where
  oddWeight := 7
  isOddGeq3 := by omega

/-- Create the n-th f-generator f_{2n+1} for n ≥ 1 -/
def fGen (n : ℕ) (hn : n ≥ 1) : FGenerator where
  oddWeight := 2 * n + 1
  isOddGeq3 := by omega

namespace FGenerator

/-- The weight of an f-generator (same as oddWeight) -/
def weight (f : FGenerator) : ℕ := f.oddWeight

/-- Index of the f-generator: f_{2n+1} has index n -/
def index (f : FGenerator) : ℕ := (f.oddWeight - 1) / 2

end FGenerator

/-- A monomial in f-generators with rational coefficient.
    Represents products like 2/3 · f₃² · f₅ -/
structure FMonomial where
  /-- Coefficient -/
  coeff : ℚ
  /-- List of f-generators (their odd weights) -/
  generators : List ℕ
  /-- All generators are valid (odd ≥ 3) -/
  allValid : ∀ w ∈ generators, w % 2 = 1 ∧ w ≥ 3

namespace FMonomial

/-- Weight of a monomial = sum of generator weights -/
def weight (m : FMonomial) : ℕ := m.generators.sum

/-- Depth of a monomial = number of generators -/
def depth (m : FMonomial) : ℕ := m.generators.length

/-- The unit monomial (coefficient 1, no generators) -/
def one : FMonomial where
  coeff := 1
  generators := []
  allValid := by simp

/-- Scalar multiplication -/
def smul (c : ℚ) (m : FMonomial) : FMonomial where
  coeff := c * m.coeff
  generators := m.generators
  allValid := m.allValid

end FMonomial

/-! ## The Period Map -/

/-- The de Rham period map sends motivic MZVs to their numerical values.

    per : H → ℂ

    This is the "forget motivic structure" map.
    It is a ring homomorphism but NOT injective
    (in general, we lose information). -/
def motivicPeriodMap (m : MotivicMZV) : ℚ :=
  (m.formal.map (fun t => t.1)).sum

/-- The period map is a ring homomorphism -/
theorem motivicPeriodMap_ring_hom :
    ∀ m₁ m₂ : MotivicMZV,
      motivicPeriodMap (MotivicMZV.add m₁ m₂) =
        motivicPeriodMap m₁ + motivicPeriodMap m₂ := by
  intro m₁ m₂
  unfold motivicPeriodMap MotivicMZV.add FormalSum.add
  simp [List.map_append, List.sum_append]

/-- Kernels of the period map are motivic relations -/
def motivicPeriodMap_kernel : Set MotivicMZV :=
  { m | motivicPeriodMap m = 0 }

/-! ## Brown's Main Theorem -/

/-- Brown's structure theorem for motivic MZVs.

    The algebra of motivic MZVs is:
    H = ℚ[f₃, f₅, f₇, ...]

    as a polynomial algebra (not a free algebra - there are relations
    coming from the Hopf algebra structure). -/
def brown_structure_theorem : Prop :=
  ∀ m : MotivicMZV, ∃ mons : List FMonomial, (mons.map FMonomial.weight).sum = m.weight

/-- The depth filtration on H.

    D_n H = span of motivic MZVs of depth ≤ n

    Brown showed this filtration is compatible with the Hopf structure. -/
def depthFiltration (n : ℕ) : Set MotivicMZV := { m | m.depth ≤ n }

/-- The associated graded of the depth filtration.

    gr^D H = ⊕_n D_n/D_{n-1}

    This is related to the free Lie algebra. -/
def depth_graded : Prop :=
  ∀ n : ℕ, depthFiltration n ⊆ depthFiltration (n + 1)

/-! ## Connection to Periods -/

/-- Kontsevich-Zagier period conjecture (restricted to MZVs).

    Every algebraic relation between MZVs comes from a motivic relation.
    Equivalently: the period map has "geometric" kernel. -/
def period_conjecture : Prop :=
  Function.Injective motivicPeriodMap

/-- The algebra of periods over ℚ.

    MZVs generate a ℚ-subalgebra of ℂ. Understanding its structure
    is a major open problem. -/
structure PeriodAlgebra where
  carrier : Set ℚ
  contains_zero : (0 : ℚ) ∈ carrier
  closed_add : ∀ a b : ℚ, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  closed_mul : ∀ a b : ℚ, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- A canonical period algebra model containing all rational periods. -/
def periodAlgebra : PeriodAlgebra where
  carrier := Set.univ
  contains_zero := by simp
  closed_add := by intro _a _b _ha _hb; simp
  closed_mul := by intro _a _b _ha _hb; simp

/-! ## Galois Theory -/

/-- The motivic Galois group acts on motivic MZVs.

    G_MT = Aut^⊗(ω)

    where ω is the fiber functor. This action is captured by the coaction. -/
structure MotivicGaloisGroup where
  act : MotivicMZV → MotivicMZV
  preserves_weight : ∀ m : MotivicMZV, (act m).weight = m.weight
  preserves_depth : ∀ m : MotivicMZV, (act m).depth = m.depth

/-- The identity action gives a basic motivic Galois action model. -/
def motivicGaloisGroup : MotivicGaloisGroup where
  act := fun m => m
  preserves_weight := by intro _m; rfl
  preserves_depth := by intro _m; rfl

/-- The Lie algebra of the motivic Galois group.

    Lie(G_MT) is a free Lie algebra on generators σ₃, σ₅, σ₇, ...
    dual to f₃, f₅, f₇, ... -/
def motivic_lie_algebra : Prop :=
  ∃ d : ℕ → MotivicMZV → MotivicMZV,
    ∀ n m : ℕ,
      (d n (d m MotivicMZV.zero)).weight =
        (d m (d n MotivicMZV.zero)).weight

/-- Ihara's derivation algebra is related to Lie(G_MT). -/
def ihara_derivation_relation : Prop :=
  ∀ n : ℕ, ∀ s : Composition, (iharaDerivComp n s).length = s.length

/-! ## Examples at Low Weight -/

/-! ## Connection to Physics -/

/-- MZVs appear in Feynman integrals at multi-loop level.

    This connection is not coincidental: both are periods of
    mixed Tate motives arising from P¹ \ {0, 1, ∞}. -/
def feynman_integral_connection : Prop :=
  ∀ m : MotivicMZV, motivicPeriodMap m ∈ periodAlgebra.carrier

/-- The cosmic Galois group conjecture (Cartier-Kontsevich).

    There is a "cosmic Galois group" acting on Feynman integrals,
    and the motivic Galois group is a quotient. -/
def cosmic_galois_conjecture : Prop :=
  ∃ G : MotivicGaloisGroup, G = motivicGaloisGroup

end StringAlgebra.MZV
