/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.DoubleShuffle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

## Formalization Status (Phase 0)

This file now separates:
1. proved infrastructure lemmas;
2. explicit specification interfaces for still-open mathematical obligations;
3. conjectural interfaces, named with `_conjecture`.
-/

namespace StringAlgebra.MZV

/-! ## The Motivic MZV Algebra -/

/-- Toy model of a motivic MZV as a formal sum with weight/depth metadata.

    LIMITATIONS: This is a simplified combinatorial model, NOT a faithful
    formalization of motivic MZVs (framed mixed Tate motives). Key gaps:

    1. The `weight` and `depth` fields are free metadata not structurally
       tied to `formal`. Use `WellFormed` to check consistency.
    2. The algebra operations (add, mul) are defined on formal sums
       but do NOT quotient by shuffle/stuffle relations.
    3. The coaction is a depth-1 primitive model (Δ(m) = m⊗1 + 1⊗m),
       not Brown's admissible-cut coaction.

    A proper formalization would require:
    - The quotient of the formal MZV algebra by double shuffle relations
    - Brown's coaction via admissible cuts on composition words
    - The period map to ℂ (or ℝ) via actual MZV evaluation -/
structure MotivicMZV where
  /-- The underlying formal sum -/
  formal : FormalSum
  /-- Weight of the motivic MZV (metadata — check with WellFormed) -/
  weight : ℕ
  /-- Depth of the motivic MZV (metadata — check with WellFormed) -/
  depth : ℕ
  deriving DecidableEq, Repr

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

/-- The multiplicative unit motivic MZV. -/
def one : MotivicMZV := ofComposition []

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

instance : Zero MotivicMZV := ⟨zero⟩
instance : One MotivicMZV := ⟨one⟩
instance : Add MotivicMZV := ⟨add⟩
instance : Neg MotivicMZV := ⟨neg⟩
instance : Sub MotivicMZV := ⟨sub⟩
instance : Mul MotivicMZV := ⟨mul⟩
instance : SMul ℚ MotivicMZV := ⟨smul⟩

/-- Metadata check: every term weight is bounded by the declared weight. -/
def WeightBounded (m : MotivicMZV) : Prop :=
  ∀ q s, (q, s) ∈ m.formal → s.weight ≤ m.weight

/-- Metadata check: every term depth is bounded by the declared depth. -/
def DepthBounded (m : MotivicMZV) : Prop :=
  ∀ q s, (q, s) ∈ m.formal → s.depth ≤ m.depth

/-- Combined metadata well-formedness predicate for the toy model. -/
def WellFormed (m : MotivicMZV) : Prop := WeightBounded m ∧ DepthBounded m

theorem wellFormed_zero : WellFormed zero := by
  constructor
  · intro q s hs
    simp [zero] at hs
  · intro q s hs
    simp [zero] at hs

theorem wellFormed_ofComposition (s : Composition) : WellFormed (ofComposition s) := by
  constructor
  · intro q t ht
    simp [ofComposition, FormalSum.single] at ht
    rcases ht with ⟨hq, ht⟩
    subst hq
    subst ht
    exact Nat.le_refl _
  · intro q t ht
    simp [ofComposition, FormalSum.single] at ht
    rcases ht with ⟨hq, ht⟩
    subst hq
    subst ht
    exact Nat.le_refl _

theorem wellFormed_one : WellFormed one := by
  simpa [one] using wellFormed_ofComposition ([] : Composition)

theorem wellFormed_add {m₁ m₂ : MotivicMZV}
    (h₁ : WellFormed m₁) (h₂ : WellFormed m₂) :
    WellFormed (add m₁ m₂) := by
  rcases h₁ with ⟨h₁w, h₁d⟩
  rcases h₂ with ⟨h₂w, h₂d⟩
  constructor
  · intro q s hs
    simp [add, FormalSum.add] at hs
    rcases hs with hs | hs
    · exact Nat.le_trans (h₁w q s hs) (Nat.le_max_left _ _)
    · exact Nat.le_trans (h₂w q s hs) (Nat.le_max_right _ _)
  · intro q s hs
    simp [add, FormalSum.add] at hs
    rcases hs with hs | hs
    · exact Nat.le_trans (h₁d q s hs) (Nat.le_max_left _ _)
    · exact Nat.le_trans (h₂d q s hs) (Nat.le_max_right _ _)

theorem wellFormed_smul (c : ℚ) {m : MotivicMZV} (hm : WellFormed m) :
    WellFormed (smul c m) := by
  rcases hm with ⟨hw, hd⟩
  constructor
  · intro q s hs
    simp [smul, FormalSum.smul] at hs
    rcases hs with ⟨q', hs, _⟩
    exact hw q' s hs
  · intro q s hs
    simp [smul, FormalSum.smul] at hs
    rcases hs with ⟨q', hs, _⟩
    exact hd q' s hs

theorem wellFormed_neg {m : MotivicMZV} (hm : WellFormed m) :
    WellFormed (neg m) := by
  rcases hm with ⟨hw, hd⟩
  constructor
  · intro q s hs
    simp [neg, FormalSum.neg] at hs
    rcases hs with ⟨q', hs, _⟩
    exact hw q' s hs
  · intro q s hs
    simp [neg, FormalSum.neg] at hs
    rcases hs with ⟨q', hs, _⟩
    exact hd q' s hs

theorem wellFormed_sub {m₁ m₂ : MotivicMZV}
    (h₁ : WellFormed m₁) (h₂ : WellFormed m₂) :
    WellFormed (sub m₁ m₂) := by
  exact wellFormed_add h₁ (wellFormed_neg h₂)

/-- Right unit law for motivic multiplication. -/
@[simp] theorem mul_one (m : MotivicMZV) : mul m one = m := by
  cases m with
  | mk formal weight depth =>
    simp [mul, one, ofComposition, stuffleFormal, FormalSum.single, stuffle_nil_right,
      Composition.weight, Composition.depth]

/-- Left unit law for motivic multiplication. -/
@[simp] theorem one_mul (m : MotivicMZV) : mul one m = m := by
  cases m with
  | mk formal weight depth =>
    simp [mul, one, ofComposition, stuffleFormal, FormalSum.single, stuffle_nil_left,
      Composition.weight, Composition.depth]

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

/-- Tensor product multiplication induced by multiplication in each factor. -/
def mul (t₁ t₂ : TensorElement) : TensorElement :=
  t₁.flatMap fun (q₁, a₁, b₁) =>
    t₂.map fun (q₂, a₂, b₂) => (q₁ * q₂, MotivicMZV.mul a₁ a₂, MotivicMZV.mul b₁ b₂)

/-- The strict part keeps only terms with non-unit entries in both tensor factors. -/
def strictPart (t : TensorElement) : TensorElement :=
  t.filter fun (_, a, b) => a ≠ MotivicMZV.one ∧ b ≠ MotivicMZV.one

/-- The right-weight part keeps only terms whose right tensor factor has weight `w`. -/
def rightWeightPart (w : ℕ) (t : TensorElement) : TensorElement :=
  t.filter fun (_, _, b) => b.weight = w

/-- Every right tensor factor has depth strictly less than `d`. -/
def RightDepthLt (d : ℕ) (t : TensorElement) : Prop :=
  ∀ q : ℚ, ∀ a b : MotivicMZV, (q, a, b) ∈ t → b.depth < d

/-- Right-depth bounds are monotone in the target bound. -/
theorem rightDepthLt_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) {t : TensorElement}
    (ht : RightDepthLt d₁ t) : RightDepthLt d₂ t := by
  intro q a b hb
  exact Nat.lt_of_lt_of_le (ht q a b hb) h

/-- Coefficient extraction for a fixed tensor basis pair. -/
def coeff (t : TensorElement) (a b : MotivicMZV) : ℚ :=
  ((t.filter fun (_, x, y) => x = a ∧ y = b).map fun (q, _, _) => q).sum

/-- Canonical coefficient-function normalization. -/
def normalize (t : TensorElement) : MotivicMZV → MotivicMZV → ℚ :=
  coeff t

/-- Extensional equivalence of tensor elements via normalized coefficients. -/
def Equiv (t₁ t₂ : TensorElement) : Prop :=
  normalize t₁ = normalize t₂

theorem equiv_refl (t : TensorElement) : Equiv t t := rfl

theorem equiv_symm {t₁ t₂ : TensorElement} (h : Equiv t₁ t₂) : Equiv t₂ t₁ := h.symm

theorem equiv_trans {t₁ t₂ t₃ : TensorElement}
    (h₁₂ : Equiv t₁ t₂) (h₂₃ : Equiv t₂ t₃) : Equiv t₁ t₃ := h₁₂.trans h₂₃

theorem equiv_of_eq {t₁ t₂ : TensorElement} (h : t₁ = t₂) : Equiv t₁ t₂ := by
  subst h
  exact equiv_refl _

end TensorElement

/-- A tensor element in H ⊗ H ⊗ H, represented as a formal sum of triples. -/
abbrev TripleTensorElement := List (ℚ × MotivicMZV × MotivicMZV × MotivicMZV)

namespace TripleTensorElement

/-- Coefficient extraction for a fixed tensor basis triple. -/
def coeff (t : TripleTensorElement) (a b c : MotivicMZV) : ℚ :=
  ((t.filter fun (_, x, y, z) => x = a ∧ y = b ∧ z = c).map fun (q, _, _, _) => q).sum

/-- Canonical coefficient-function normalization. -/
def normalize (t : TripleTensorElement) : MotivicMZV → MotivicMZV → MotivicMZV → ℚ :=
  coeff t

/-- Extensional equivalence of triple tensor elements via normalized coefficients. -/
def Equiv (t₁ t₂ : TripleTensorElement) : Prop :=
  normalize t₁ = normalize t₂

theorem equiv_refl (t : TripleTensorElement) : Equiv t t := rfl

theorem equiv_symm {t₁ t₂ : TripleTensorElement} (h : Equiv t₁ t₂) : Equiv t₂ t₁ := h.symm

theorem equiv_trans {t₁ t₂ t₃ : TripleTensorElement}
    (h₁₂ : Equiv t₁ t₂) (h₂₃ : Equiv t₂ t₃) : Equiv t₁ t₃ := h₁₂.trans h₂₃

theorem equiv_of_eq {t₁ t₂ : TripleTensorElement} (h : t₁ = t₂) : Equiv t₁ t₂ := by
  subst h
  exact equiv_refl _

end TripleTensorElement

/-- Toy model of the motivic coaction Δ : H → H ⊗ H.

    LIMITATION: This implements only the depth-1 primitive coaction
    Δ(m) = m ⊗ 1 + 1 ⊗ m, which is the coaction of a primitive
    element in any Hopf algebra.

    Brown's actual coaction involves admissible cuts on the word
    representation and produces non-trivial "middle terms" at
    higher depth. The depth-1 primitive model does NOT capture this
    structure — it makes every element primitive.

    The theorems proved below (coassociativity, multiplicativity)
    are trivially true for the primitive coaction and do NOT
    constitute proofs of the corresponding statements for the
    full motivic coaction. -/
structure Coaction where
  /-- The tensor element representing Δ(m) -/
  value : TensorElement

namespace Coaction

/-- Depth-1 primitive coaction model:
    `Δ(m) = m ⊗ 1 + 1 ⊗ m`, with a unit normalization at `1`. -/
def primitiveTensor (m : MotivicMZV) : TensorElement :=
  if m = MotivicMZV.one then
    TensorElement.simple MotivicMZV.one MotivicMZV.one
  else
    TensorElement.add
      (TensorElement.simple m MotivicMZV.one)
      (TensorElement.simple MotivicMZV.one m)

/-- The trivial coaction for depth 1: Δ(ζ^m(n)) = ζ^m(n) ⊗ 1 + 1 ⊗ ζ^m(n) -/
def ofDepth1 (m : MotivicMZV) : Coaction where
  value := primitiveTensor m

/-- The coaction of zero is zero -/
def ofZero : Coaction where
  value := TensorElement.zero

/-- `(Δ ⊗ id)` expansion for the depth-1 coaction model. -/
def leftAssociate (c : Coaction) : TripleTensorElement :=
  c.value.flatMap fun (q, a, b) =>
    (ofDepth1 a).value.map fun (q', a₁, a₂) => (q * q', a₁, a₂, b)

/-- `(id ⊗ Δ)` expansion for the depth-1 coaction model. -/
def rightAssociate (c : Coaction) : TripleTensorElement :=
  c.value.flatMap fun (q, a, b) =>
    (ofDepth1 b).value.map fun (q', b₁, b₂) => (q * q', a, b₁, b₂)

/-- Product expansion of two depth-1 primitive coactions in `H ⊗ H`. -/
def productExpansion (m₁ m₂ : MotivicMZV) : TensorElement :=
  TensorElement.add
    (TensorElement.add
      (TensorElement.simple (MotivicMZV.mul m₁ m₂) MotivicMZV.one)
      (TensorElement.simple m₁ m₂))
    (TensorElement.add
      (TensorElement.simple m₂ m₁)
      (TensorElement.simple MotivicMZV.one (MotivicMZV.mul m₁ m₂)))

/-- Bilinear core terms corresponding to the Leibniz-type middle cuts. -/
def leibnizCore (m₁ m₂ : MotivicMZV) : TensorElement :=
  TensorElement.add
    (TensorElement.simple m₁ m₂)
    (TensorElement.simple m₂ m₁)

/-- For non-unit inputs, the strict part of `Δ(m₁)⋅Δ(m₂)` is exactly the Leibniz core. -/
theorem strictPart_product_depth1
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one) :
    TensorElement.strictPart
      (TensorElement.mul (Coaction.ofDepth1 m₁).value (Coaction.ofDepth1 m₂).value) =
        leibnizCore m₁ m₂ := by
  simp [Coaction.ofDepth1, Coaction.primitiveTensor, TensorElement.mul, TensorElement.strictPart,
    leibnizCore, TensorElement.add, TensorElement.simple, h₁, h₂]

/-- In the Leibniz core, right factors are strictly lower-depth than the product depth
    whenever both inputs have positive depth. -/
theorem leibnizCore_rightDepth_lt_mulDepth
    (m₁ m₂ : MotivicMZV)
    (hdepth₁ : 0 < m₁.depth) (hdepth₂ : 0 < m₂.depth) :
    TensorElement.RightDepthLt (MotivicMZV.mul m₁ m₂).depth (leibnizCore m₁ m₂) := by
  intro q a b hmem
  simp [leibnizCore, TensorElement.add, TensorElement.simple] at hmem
  rcases hmem with h | h
  · rcases h with ⟨hq, ha, hb⟩
    subst hq; subst ha; subst hb
    simp [MotivicMZV.mul]
    omega
  · rcases h with ⟨hq, ha, hb⟩
    subst hq; subst ha; subst hb
    simp [MotivicMZV.mul]
    omega

/-- Strict right-depth lowering for non-unit depth-1 product coactions. -/
theorem strictPart_product_depth1_rightDepth_lt_mulDepth
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one)
    (hdepth₁ : 0 < m₁.depth) (hdepth₂ : 0 < m₂.depth) :
    TensorElement.RightDepthLt
      (MotivicMZV.mul m₁ m₂).depth
      (TensorElement.strictPart
        (TensorElement.mul (Coaction.ofDepth1 m₁).value (Coaction.ofDepth1 m₂).value)) := by
  simpa [strictPart_product_depth1, h₁, h₂] using
    leibnizCore_rightDepth_lt_mulDepth m₁ m₂ hdepth₁ hdepth₂

end Coaction

/-- The coaction is coassociative: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ -/
theorem coaction_coassociative :
    ∀ m : MotivicMZV,
      Coaction.leftAssociate (Coaction.ofDepth1 m) =
        Coaction.rightAssociate (Coaction.ofDepth1 m) := by
  intro m
  by_cases h : m = MotivicMZV.one
  · subst h
    simp [Coaction.leftAssociate, Coaction.rightAssociate, Coaction.ofDepth1,
      Coaction.primitiveTensor, TensorElement.simple, TensorElement.add]
  · simp [Coaction.leftAssociate, Coaction.rightAssociate, Coaction.ofDepth1,
      Coaction.primitiveTensor, TensorElement.simple, TensorElement.add, h]

/-- Multiplicativity formula for the depth-1 primitive coaction model. -/
theorem coaction_multiplicative :
    ∀ m₁ m₂ : MotivicMZV,
      TensorElement.mul (Coaction.ofDepth1 m₁).value (Coaction.ofDepth1 m₂).value =
        if m₁ = MotivicMZV.one then
          (Coaction.ofDepth1 m₂).value
        else if m₂ = MotivicMZV.one then
          (Coaction.ofDepth1 m₁).value
        else
          Coaction.productExpansion m₁ m₂ := by
  intro m₁ m₂
  by_cases h₁ : m₁ = MotivicMZV.one
  · subst h₁
    simp [Coaction.ofDepth1, Coaction.primitiveTensor, TensorElement.mul,
      TensorElement.simple, TensorElement.add]
  · by_cases h₂ : m₂ = MotivicMZV.one
    · subst h₂
      simp [Coaction.ofDepth1, Coaction.primitiveTensor, TensorElement.mul,
        TensorElement.simple, TensorElement.add, h₁]
    · simp [Coaction.ofDepth1, Coaction.primitiveTensor, TensorElement.mul,
        TensorElement.simple, TensorElement.add, Coaction.productExpansion, h₁, h₂]

/-- Coassociativity restated up to coefficient-function equivalence. -/
theorem coaction_coassociative_equiv :
    ∀ m : MotivicMZV,
      TripleTensorElement.Equiv
        (Coaction.leftAssociate (Coaction.ofDepth1 m))
        (Coaction.rightAssociate (Coaction.ofDepth1 m)) := by
  intro m
  exact TripleTensorElement.equiv_of_eq (coaction_coassociative m)

/-- Multiplicativity restated up to coefficient-function equivalence. -/
theorem coaction_multiplicative_equiv :
    ∀ m₁ m₂ : MotivicMZV,
      TensorElement.Equiv
        (TensorElement.mul (Coaction.ofDepth1 m₁).value (Coaction.ofDepth1 m₂).value)
        (if m₁ = MotivicMZV.one then
          (Coaction.ofDepth1 m₂).value
        else if m₂ = MotivicMZV.one then
          (Coaction.ofDepth1 m₁).value
        else
          Coaction.productExpansion m₁ m₂) := by
  intro m₁ m₂
  exact TensorElement.equiv_of_eq (coaction_multiplicative m₁ m₂)

/-! ## Coaction Interfaces -/

/-- A generic coaction operator `Δ : H → H ⊗ H` at the current level of abstraction. -/
structure CoactionMap where
  delta : MotivicMZV → TensorElement

namespace CoactionMap

/-- View `Δ(m)` as a `Coaction` package. -/
def toCoaction (Δ : CoactionMap) (m : MotivicMZV) : Coaction :=
  { value := Δ.delta m }

/-- `Δ` agrees with the primitive depth-1 model on all inputs. -/
def IsPrimitiveFragment (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV, Δ.delta m = Coaction.primitiveTensor m

/-- Coassociativity for a generic coaction map. -/
def IsCoassociative (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV,
    Coaction.leftAssociate (toCoaction Δ m) = Coaction.rightAssociate (toCoaction Δ m)

/-- Multiplicativity in the current primitive depth-1 expansion model. -/
def IsMultiplicativePrimitive (Δ : CoactionMap) : Prop :=
  ∀ m₁ m₂ : MotivicMZV,
    TensorElement.mul (Δ.delta m₁) (Δ.delta m₂) =
      if m₁ = MotivicMZV.one then
        Δ.delta m₂
      else if m₂ = MotivicMZV.one then
        Δ.delta m₁
      else
        Coaction.productExpansion m₁ m₂

/-- Coassociativity up to coefficient-function equivalence. -/
def IsCoassociativeUpToEquiv (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV,
    TripleTensorElement.Equiv
      (Coaction.leftAssociate (toCoaction Δ m))
      (Coaction.rightAssociate (toCoaction Δ m))

/-- Multiplicativity up to coefficient-function equivalence. -/
def IsMultiplicativePrimitiveUpToEquiv (Δ : CoactionMap) : Prop :=
  ∀ m₁ m₂ : MotivicMZV,
    TensorElement.Equiv
      (TensorElement.mul (Δ.delta m₁) (Δ.delta m₂))
      (if m₁ = MotivicMZV.one then
        Δ.delta m₂
      else if m₂ = MotivicMZV.one then
        Δ.delta m₁
      else
        Coaction.productExpansion m₁ m₂)

/-- Binary infinitesimal part induced by `Δ`: keep only strict middle tensor terms. -/
def binaryInfinitesimal (Δ : CoactionMap) (m₁ m₂ : MotivicMZV) : TensorElement :=
  TensorElement.strictPart (TensorElement.mul (Δ.delta m₁) (Δ.delta m₂))

/-- Weight-`w` slice of the binary infinitesimal part (on the right tensor factor). -/
def binaryInfinitesimalRightWeight
    (Δ : CoactionMap) (w : ℕ) (m₁ m₂ : MotivicMZV) : TensorElement :=
  TensorElement.rightWeightPart w (binaryInfinitesimal Δ m₁ m₂)

/-- Weight-`w` slice of the coaction of a single motivic element (right factor). -/
def coactionRightWeightSlice
    (Δ : CoactionMap) (w : ℕ) (m : MotivicMZV) : TensorElement :=
  TensorElement.rightWeightPart w (Δ.delta m)

/-- Left-factor formal projection of a tensor element, weighted by tensor coefficients. -/
def leftFormalProjection (t : TensorElement) : FormalSum :=
  t.flatMap (fun (q, a, _) => FormalSum.smul q a.formal)

@[simp] theorem leftFormalProjection_zero :
    leftFormalProjection TensorElement.zero = FormalSum.zero := rfl

@[simp] theorem leftFormalProjection_add (t₁ t₂ : TensorElement) :
    leftFormalProjection (TensorElement.add t₁ t₂) =
      FormalSum.add (leftFormalProjection t₁) (leftFormalProjection t₂) := by
  simp [leftFormalProjection, TensorElement.add, FormalSum.add]

/-- If left factors in a tensor expression are uniformly well-formed and weight bounded,
    the projected formal sum inherits the same weight bound. -/
theorem weightBounded_leftFormalProjection_of_leftFactor
    (t : TensorElement) (W : ℕ)
    (hweight : ∀ q : ℚ, ∀ a b : MotivicMZV, (q, a, b) ∈ t → a.weight ≤ W)
    (hwell : ∀ q : ℚ, ∀ a b : MotivicMZV, (q, a, b) ∈ t → MotivicMZV.WellFormed a) :
    ∀ q : ℚ, ∀ s : Composition, (q, s) ∈ leftFormalProjection t → s.weight ≤ W := by
  intro q s hs
  rcases List.mem_flatMap.mp hs with ⟨x, hxmem, hxproj⟩
  rcases x with ⟨q₀, a, b⟩
  simp [FormalSum.smul] at hxproj
  rcases hxproj with ⟨q₁, hq₁, hcoeff⟩
  have hWa : a.weight ≤ W := hweight q₀ a b hxmem
  have hWFa : MotivicMZV.WellFormed a := hwell q₀ a b hxmem
  rcases hWFa with ⟨haWeight, _haDepth⟩
  have hsWeight : s.weight ≤ a.weight := haWeight q₁ s hq₁
  exact Nat.le_trans hsWeight hWa

/-- If left factors in a tensor expression are uniformly well-formed and depth bounded,
    the projected formal sum inherits the same depth bound. -/
theorem depthBounded_leftFormalProjection_of_leftFactor
    (t : TensorElement) (D : ℕ)
    (hdepth : ∀ q : ℚ, ∀ a b : MotivicMZV, (q, a, b) ∈ t → a.depth ≤ D)
    (hwell : ∀ q : ℚ, ∀ a b : MotivicMZV, (q, a, b) ∈ t → MotivicMZV.WellFormed a) :
    ∀ q : ℚ, ∀ s : Composition, (q, s) ∈ leftFormalProjection t → s.depth ≤ D := by
  intro q s hs
  rcases List.mem_flatMap.mp hs with ⟨x, hxmem, hxproj⟩
  rcases x with ⟨q₀, a, b⟩
  simp [FormalSum.smul] at hxproj
  rcases hxproj with ⟨q₁, hq₁, hcoeff⟩
  have hDa : a.depth ≤ D := hdepth q₀ a b hxmem
  have hWFa : MotivicMZV.WellFormed a := hwell q₀ a b hxmem
  rcases hWFa with ⟨_haWeight, haDepth⟩
  have hsDepth : s.depth ≤ a.depth := haDepth q₁ s hq₁
  exact Nat.le_trans hsDepth hDa

/-- Coaction-derived odd cut operator at odd weight `2r+1`. -/
def oddCoactionCut (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) : TensorElement :=
  coactionRightWeightSlice Δ (2 * r + 1) m

/-- Coaction hypothesis: every left tensor factor is well-formed. -/
def LeftFactorsWellFormed (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV, ∀ q : ℚ, ∀ a b : MotivicMZV,
    (q, a, b) ∈ Δ.delta m → MotivicMZV.WellFormed a

/-- Coaction hypothesis: every left tensor factor has depth bounded by the source depth. -/
def LeftDepthBounded (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV, ∀ q : ℚ, ∀ a b : MotivicMZV,
    (q, a, b) ∈ Δ.delta m → a.depth ≤ m.depth

/-- Coaction hypothesis: each tensor term splits weight within source weight budget. -/
def LeftRightWeightBounded (Δ : CoactionMap) : Prop :=
  ∀ m : MotivicMZV, ∀ q : ℚ, ∀ a b : MotivicMZV,
    (q, a, b) ∈ Δ.delta m → a.weight + b.weight ≤ m.weight

@[simp] theorem mem_oddCoactionCut_iff
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV)
    (q : ℚ) (a b : MotivicMZV) :
    (q, a, b) ∈ oddCoactionCut Δ r m ↔
      (q, a, b) ∈ Δ.delta m ∧ b.weight = 2 * r + 1 := by
  simp [oddCoactionCut, coactionRightWeightSlice, TensorElement.rightWeightPart]

/-- Candidate Brown-style weight-lowering derivation induced by odd coaction cuts.
    This is intentionally separated from the legacy weight-raising Ihara model. -/
def weightLoweringOddDerivationCandidate
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) : MotivicMZV where
  formal := leftFormalProjection (oddCoactionCut Δ r m)
  weight := m.weight - (2 * r + 1)
  depth := m.depth

/-- Family form of the coaction-derived weight-lowering odd cut operator. -/
def weightLoweringOddDerivationFamily (Δ : CoactionMap) :
    ℕ → MotivicMZV → MotivicMZV :=
  fun r m => weightLoweringOddDerivationCandidate Δ r m

@[simp] theorem weightLoweringOddDerivationCandidate_depth
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) :
    (weightLoweringOddDerivationCandidate Δ r m).depth = m.depth := rfl

@[simp] theorem weightLoweringOddDerivationCandidate_weight
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) :
    (weightLoweringOddDerivationCandidate Δ r m).weight = m.weight - (2 * r + 1) := rfl

theorem weightLoweringOddDerivationCandidate_weight_le
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) :
    (weightLoweringOddDerivationCandidate Δ r m).weight ≤ m.weight := by
  simp [weightLoweringOddDerivationCandidate]

theorem weightLoweringOddDerivationCandidate_weight_eq_zero_of_lt
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV)
    (h : m.weight < 2 * r + 1) :
    (weightLoweringOddDerivationCandidate Δ r m).weight = 0 := by
  simp [weightLoweringOddDerivationCandidate, Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]

theorem weightLoweringOddDerivationFamily_weight
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV) :
    (weightLoweringOddDerivationFamily Δ r m).weight = m.weight - (2 * r + 1) := by
  rfl

/-- Well-formedness transfer for the coaction-derived odd weight-lowering candidate,
    under explicit left-factor boundedness assumptions on the odd coaction cut. -/
theorem weightLoweringOddDerivationCandidate_wellFormed_of_leftFactorBounds
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV)
    (hleftWeight :
      ∀ q : ℚ, ∀ a b : MotivicMZV,
        (q, a, b) ∈ oddCoactionCut Δ r m → a.weight ≤ m.weight - (2 * r + 1))
    (hleftDepth :
      ∀ q : ℚ, ∀ a b : MotivicMZV,
        (q, a, b) ∈ oddCoactionCut Δ r m → a.depth ≤ m.depth)
    (hleftWell :
      ∀ q : ℚ, ∀ a b : MotivicMZV,
        (q, a, b) ∈ oddCoactionCut Δ r m → MotivicMZV.WellFormed a) :
    MotivicMZV.WellFormed (weightLoweringOddDerivationCandidate Δ r m) := by
  constructor
  · intro q s hs
    exact weightBounded_leftFormalProjection_of_leftFactor
      (oddCoactionCut Δ r m) (m.weight - (2 * r + 1))
      hleftWeight hleftWell q s (by simpa [weightLoweringOddDerivationCandidate] using hs)
  · intro q s hs
    exact depthBounded_leftFormalProjection_of_leftFactor
      (oddCoactionCut Δ r m) m.depth
      hleftDepth hleftWell q s (by simpa [weightLoweringOddDerivationCandidate] using hs)

/-- Global coaction-side boundedness hypotheses imply well-formedness of the
    coaction-derived odd weight-lowering derivation candidate. -/
theorem weightLoweringOddDerivationCandidate_wellFormed_of_deltaBounds
    (Δ : CoactionMap) (r : ℕ) (m : MotivicMZV)
    (hWell : LeftFactorsWellFormed Δ)
    (hDepth : LeftDepthBounded Δ)
    (hWeight : LeftRightWeightBounded Δ) :
    MotivicMZV.WellFormed (weightLoweringOddDerivationCandidate Δ r m) := by
  refine weightLoweringOddDerivationCandidate_wellFormed_of_leftFactorBounds Δ r m ?_ ?_ ?_
  · intro q a b hcut
    have hmem :
        (q, a, b) ∈ Δ.delta m ∧ b.weight = 2 * r + 1 :=
      (mem_oddCoactionCut_iff Δ r m q a b).1 hcut
    have hsum : a.weight + b.weight ≤ m.weight := hWeight m q a b hmem.1
    have hsumOdd : a.weight + (2 * r + 1) ≤ m.weight := by
      simpa [hmem.2] using hsum
    omega
  · intro q a b hcut
    have hmem :
        (q, a, b) ∈ Δ.delta m ∧ b.weight = 2 * r + 1 :=
      (mem_oddCoactionCut_iff Δ r m q a b).1 hcut
    exact hDepth m q a b hmem.1
  · intro q a b hcut
    have hmem :
        (q, a, b) ∈ Δ.delta m ∧ b.weight = 2 * r + 1 :=
      (mem_oddCoactionCut_iff Δ r m q a b).1 hcut
    exact hWell m q a b hmem.1

/-- Primitive-fragment agreement implies coassociativity in the current model. -/
theorem isCoassociative_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ) :
    IsCoassociative Δ := by
  intro m
  simpa [toCoaction, Coaction.ofDepth1, hΔ m] using coaction_coassociative m

/-- Primitive-fragment agreement implies primitive multiplicativity in the current model. -/
theorem isMultiplicativePrimitive_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ) :
    IsMultiplicativePrimitive Δ := by
  intro m₁ m₂
  simpa [hΔ m₁, hΔ m₂, Coaction.ofDepth1] using coaction_multiplicative m₁ m₂

/-- Primitive-fragment agreement implies coassociativity up to equivalence. -/
theorem isCoassociativeUpToEquiv_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ) :
    IsCoassociativeUpToEquiv Δ := by
  intro m
  exact TripleTensorElement.equiv_of_eq (isCoassociative_of_primitive_fragment hΔ m)

/-- Primitive-fragment agreement implies primitive multiplicativity up to equivalence. -/
theorem isMultiplicativePrimitiveUpToEquiv_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ) :
    IsMultiplicativePrimitiveUpToEquiv Δ := by
  intro m₁ m₂
  exact TensorElement.equiv_of_eq (isMultiplicativePrimitive_of_primitive_fragment hΔ m₁ m₂)

/-- Primitive-fragment agreement identifies binary infinitesimal terms with the
    depth-1 Leibniz core. -/
theorem binaryInfinitesimal_eq_leibnizCore_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ)
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one) :
    binaryInfinitesimal Δ m₁ m₂ = Coaction.leibnizCore m₁ m₂ := by
  simpa [binaryInfinitesimal, hΔ m₁, hΔ m₂, Coaction.ofDepth1] using
    Coaction.strictPart_product_depth1 m₁ m₂ h₁ h₂

/-- Primitive-fragment agreement propagates strict right-depth lowering
    for binary infinitesimal terms. -/
theorem binaryInfinitesimal_rightDepth_lt_mulDepth_of_primitive_fragment
    {Δ : CoactionMap} (hΔ : IsPrimitiveFragment Δ)
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one)
    (hdepth₁ : 0 < m₁.depth) (hdepth₂ : 0 < m₂.depth) :
    TensorElement.RightDepthLt
      (MotivicMZV.mul m₁ m₂).depth
      (binaryInfinitesimal Δ m₁ m₂) := by
  simpa [binaryInfinitesimal_eq_leibnizCore_of_primitive_fragment, hΔ, h₁, h₂] using
    Coaction.leibnizCore_rightDepth_lt_mulDepth m₁ m₂ hdepth₁ hdepth₂

end CoactionMap

/-- The concrete depth-1 coaction operator. -/
def depth1CoactionMap : CoactionMap where
  delta := fun m => (Coaction.ofDepth1 m).value

/-- `ofDepth1` realizes the primitive fragment of the generic coaction interface. -/
theorem depth1_coaction_is_primitive_fragment :
    CoactionMap.IsPrimitiveFragment depth1CoactionMap := by
  intro m
  rfl

/-- The depth-1 coaction operator is coassociative in the current model. -/
theorem depth1_coaction_is_coassociative :
    CoactionMap.IsCoassociative depth1CoactionMap := by
  exact CoactionMap.isCoassociative_of_primitive_fragment
    depth1_coaction_is_primitive_fragment

/-- The depth-1 coaction operator satisfies the primitive multiplicativity law. -/
theorem depth1_coaction_is_multiplicative :
    CoactionMap.IsMultiplicativePrimitive depth1CoactionMap := by
  exact CoactionMap.isMultiplicativePrimitive_of_primitive_fragment
    depth1_coaction_is_primitive_fragment

/-- Depth-1 coassociativity up to coefficient-function equivalence. -/
theorem depth1_coaction_is_coassociative_up_to_equiv :
    CoactionMap.IsCoassociativeUpToEquiv depth1CoactionMap := by
  exact CoactionMap.isCoassociativeUpToEquiv_of_primitive_fragment
    depth1_coaction_is_primitive_fragment

/-- Depth-1 primitive multiplicativity up to coefficient-function equivalence. -/
theorem depth1_coaction_is_multiplicative_up_to_equiv :
    CoactionMap.IsMultiplicativePrimitiveUpToEquiv depth1CoactionMap := by
  exact CoactionMap.isMultiplicativePrimitiveUpToEquiv_of_primitive_fragment
    depth1_coaction_is_primitive_fragment

/-- Depth-1 binary infinitesimal terms recover the explicit Leibniz core. -/
theorem depth1_binaryInfinitesimal_eq_leibnizCore
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one) :
    CoactionMap.binaryInfinitesimal depth1CoactionMap m₁ m₂ = Coaction.leibnizCore m₁ m₂ := by
  exact CoactionMap.binaryInfinitesimal_eq_leibnizCore_of_primitive_fragment
    depth1_coaction_is_primitive_fragment m₁ m₂ h₁ h₂

/-- Depth-1 binary infinitesimal terms satisfy strict right-depth lowering
    relative to the product depth. -/
theorem depth1_binaryInfinitesimal_rightDepth_lt_mulDepth
    (m₁ m₂ : MotivicMZV)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one)
    (hdepth₁ : 0 < m₁.depth) (hdepth₂ : 0 < m₂.depth) :
    TensorElement.RightDepthLt
      (MotivicMZV.mul m₁ m₂).depth
      (CoactionMap.binaryInfinitesimal depth1CoactionMap m₁ m₂) := by
  exact CoactionMap.binaryInfinitesimal_rightDepth_lt_mulDepth_of_primitive_fragment
    depth1_coaction_is_primitive_fragment m₁ m₂ h₁ h₂ hdepth₁ hdepth₂

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

/-- A monomial in f-letters with rational coefficient.
    The weight `2` models the Tate letter `f₂`; odd weights model `f_{2n+1}`. -/
structure FMonomial where
  /-- Coefficient -/
  coeff : ℚ
  /-- List of f-letter weights -/
  generators : List ℕ
  /-- Valid letters are `2` or odd weights `≥ 3`. -/
  allValid : ∀ w ∈ generators, w = 2 ∨ (w % 2 = 1 ∧ w ≥ 3)

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
    In this toy model it only records the total coefficient sum, so it is
    additive but not multiplicative. -/
def motivicPeriodMap (m : MotivicMZV) : ℚ :=
  (m.formal.map (fun t => t.1)).sum

/-- The toy period map is additive with respect to formal-sum addition. -/
theorem motivicPeriodMap_add :
    ∀ m₁ m₂ : MotivicMZV,
      motivicPeriodMap (MotivicMZV.add m₁ m₂) =
        motivicPeriodMap m₁ + motivicPeriodMap m₂ := by
  intro m₁ m₂
  unfold motivicPeriodMap MotivicMZV.add FormalSum.add
  simp [List.map_append, List.sum_append]

/-- Explicit lift of a rational number into the toy motivic model. -/
def rationalLift (q : ℚ) : MotivicMZV where
  formal := [(q, [])]
  weight := 0
  depth := 0

@[simp] theorem motivicPeriodMap_rationalLift (q : ℚ) :
    motivicPeriodMap (rationalLift q) = q := by
  simp [motivicPeriodMap, rationalLift]

theorem motivicPeriodMap_surjective : Function.Surjective motivicPeriodMap := by
  intro q
  exact ⟨rationalLift q, motivicPeriodMap_rationalLift q⟩

/-- Kernels of the period map are motivic relations -/
def motivicPeriodMap_kernel : Set MotivicMZV :=
  { m | motivicPeriodMap m = 0 }

/-! ## Brown-Inspired Weight Skeleton -/

/-- Weight-only combinatorial skeleton inspired by Brown's theorem.

    This result does not reconstruct the motivic element `m` and does not prove
    polynomial-algebra structure. It only produces Hoffman-style `f`-monomials
    whose total generator weight matches the metadata field `m.weight`.

    In this model we exclude formal weight `1`, which has no MZV generator. -/
theorem brown_structure_weight_skeleton :
    ∀ m : MotivicMZV, m.weight ≠ 1 →
      ∃ mons : List FMonomial, (mons.map FMonomial.weight).sum = m.weight := by
  intro m hwt
  by_cases hzero : m.weight = 0
  · refine ⟨[], ?_⟩
    simp [hzero]
  · have hge2 : m.weight ≥ 2 := by omega
    rcases hoffman_composition_exists m.weight hge2 with ⟨s, hsH, hsW⟩
    let mon : FMonomial :=
      { coeff := 1
        generators := s.map (·.val)
        allValid := by
          intro w hw
          rcases List.mem_map.mp hw with ⟨n, hn, rfl⟩
          have hn23 := hsH n hn
          cases hn23 with
          | inl h2 =>
            left
            exact h2
          | inr h3 =>
            right
            constructor <;> omega }
    have hmonWeight : FMonomial.weight mon = m.weight := by
      simpa [mon, FMonomial.weight, Composition.weight] using hsW
    refine ⟨[mon], ?_⟩
    simp [hmonWeight]

/-! ## Filtrations and Associated Graded Interfaces -/

/-- The depth filtration on H.

    D_n H = span of motivic MZVs of depth ≤ n. -/
def depthFiltration (n : ℕ) : Set MotivicMZV := { m | m.depth ≤ n }

/-- Monotonicity of the depth filtration. -/
theorem depthFiltration_mono (n : ℕ) :
    depthFiltration n ⊆ depthFiltration (n + 1) := by
  intro m hm
  exact Nat.le_trans hm (Nat.le_succ n)

/-- Exact depth piece `gr^D_n` represented as an equality slice. -/
def depthExactPiece (n : ℕ) : Set MotivicMZV := { m | m.depth = n }

/-- Exact depth pieces sit in the corresponding depth filtration step. -/
theorem depthExactPiece_subset_depthFiltration (n : ℕ) :
    depthExactPiece n ⊆ depthFiltration n := by
  intro m hm
  exact hm.le

/-- Membership in `D_n` is equivalent to membership in some exact depth piece `≤ n`. -/
theorem mem_depthFiltration_iff_exists_depthExactPiece (n : ℕ) (m : MotivicMZV) :
    m ∈ depthFiltration n ↔ ∃ d ≤ n, m ∈ depthExactPiece d := by
  constructor
  · intro hm
    exact ⟨m.depth, hm, rfl⟩
  · intro h
    rcases h with ⟨d, hd, hmd⟩
    have hdepth : m.depth = d := by
      simpa [depthExactPiece] using hmd
    simpa [depthFiltration, hdepth] using hd

/-- Projection to the exact depth-`n` slice. -/
def depthProjection (n : ℕ) (m : MotivicMZV) : Option MotivicMZV :=
  if m.depth = n then some m else none

/-- Exact criterion for a successful depth projection. -/
theorem depthProjection_eq_some_iff (n : ℕ) (m : MotivicMZV) :
    depthProjection n m = some m ↔ m ∈ depthExactPiece n := by
  by_cases h : m.depth = n
  · simp [depthProjection, depthExactPiece, h]
  · simp [depthProjection, depthExactPiece, h]

/-- Exact criterion for a vanishing depth projection. -/
theorem depthProjection_eq_none_iff (n : ℕ) (m : MotivicMZV) :
    depthProjection n m = none ↔ m ∉ depthExactPiece n := by
  by_cases h : m.depth = n
  · simp [depthProjection, depthExactPiece, h]
  · simp [depthProjection, depthExactPiece, h]

/-- The associated graded of the depth filtration is monotone at the filtration level. -/
theorem depth_graded :
    ∀ n : ℕ, depthFiltration n ⊆ depthFiltration (n + 1) := depthFiltration_mono

/-- Hoffman level for a motivic element: max number of `3` letters
    among compositions in its formal support. -/
def motivicLevel (m : MotivicMZV) : ℕ :=
  (m.formal.map fun (_, s) => level s).foldl max 0

/-- Level of the zero motivic element. -/
@[simp] theorem motivicLevel_zero : motivicLevel MotivicMZV.zero = 0 := by
  simp [motivicLevel, MotivicMZV.zero]

/-- Level of a pure composition lift. -/
theorem motivicLevel_ofComposition (s : Composition) :
    motivicLevel (MotivicMZV.ofComposition s) = level s := by
  simp [motivicLevel, MotivicMZV.ofComposition, FormalSum.single]

/-- The level filtration on motivic elements. -/
def levelFiltration (ℓ : ℕ) : Set MotivicMZV := { m | motivicLevel m ≤ ℓ }

/-- Monotonicity of the level filtration. -/
theorem levelFiltration_mono (ℓ : ℕ) :
    levelFiltration ℓ ⊆ levelFiltration (ℓ + 1) := by
  intro m hm
  exact Nat.le_trans hm (Nat.le_succ ℓ)

/-- Exact Hoffman-level piece represented as an equality slice. -/
def levelExactPiece (ℓ : ℕ) : Set MotivicMZV := { m | motivicLevel m = ℓ }

/-- Exact level pieces sit in the corresponding level filtration step. -/
theorem levelExactPiece_subset_levelFiltration (ℓ : ℕ) :
    levelExactPiece ℓ ⊆ levelFiltration ℓ := by
  intro m hm
  exact hm.le

/-- Membership in the level filtration is equivalent to some exact level piece `≤ ℓ`. -/
theorem mem_levelFiltration_iff_exists_levelExactPiece (ℓ : ℕ) (m : MotivicMZV) :
    m ∈ levelFiltration ℓ ↔ ∃ k ≤ ℓ, m ∈ levelExactPiece k := by
  constructor
  · intro hm
    exact ⟨motivicLevel m, hm, rfl⟩
  · intro h
    rcases h with ⟨k, hk, hmk⟩
    have hlevel : motivicLevel m = k := by
      simpa [levelExactPiece] using hmk
    simpa [levelFiltration, hlevel] using hk

/-- Projection to the exact level-`ℓ` slice. -/
def levelProjection (ℓ : ℕ) (m : MotivicMZV) : Option MotivicMZV :=
  if motivicLevel m = ℓ then some m else none

/-- Exact criterion for a successful level projection. -/
theorem levelProjection_eq_some_iff (ℓ : ℕ) (m : MotivicMZV) :
    levelProjection ℓ m = some m ↔ m ∈ levelExactPiece ℓ := by
  by_cases h : motivicLevel m = ℓ
  · simp [levelProjection, levelExactPiece, h]
  · simp [levelProjection, levelExactPiece, h]

/-- Exact criterion for a vanishing level projection. -/
theorem levelProjection_eq_none_iff (ℓ : ℕ) (m : MotivicMZV) :
    levelProjection ℓ m = none ↔ m ∉ levelExactPiece ℓ := by
  by_cases h : motivicLevel m = ℓ
  · simp [levelProjection, levelExactPiece, h]
  · simp [levelProjection, levelExactPiece, h]

/-- A pure composition lift lies in its own exact level piece. -/
theorem ofComposition_mem_levelExactPiece (s : Composition) :
    MotivicMZV.ofComposition s ∈ levelExactPiece (level s) := by
  simp [levelExactPiece, motivicLevel_ofComposition]

/-- Depth-1 infinitesimal depth-lowering is stable under depth-filtration bounds. -/
theorem depth1_binaryInfinitesimal_rightDepth_lt_of_depthFiltration
    (m₁ m₂ : MotivicMZV) (n₁ n₂ : ℕ)
    (hm₁ : m₁ ∈ depthFiltration n₁) (hm₂ : m₂ ∈ depthFiltration n₂)
    (h₁ : m₁ ≠ MotivicMZV.one) (h₂ : m₂ ≠ MotivicMZV.one)
    (hdepth₁ : 0 < m₁.depth) (hdepth₂ : 0 < m₂.depth) :
    TensorElement.RightDepthLt (n₁ + n₂)
      (CoactionMap.binaryInfinitesimal depth1CoactionMap m₁ m₂) := by
  have hlt :=
    depth1_binaryInfinitesimal_rightDepth_lt_mulDepth m₁ m₂ h₁ h₂ hdepth₁ hdepth₂
  have hm₁' : m₁.depth ≤ n₁ := by simpa [depthFiltration] using hm₁
  have hm₂' : m₂.depth ≤ n₂ := by simpa [depthFiltration] using hm₂
  have hbound : (MotivicMZV.mul m₁ m₂).depth ≤ n₁ + n₂ := by
    simpa [MotivicMZV.mul] using Nat.add_le_add hm₁' hm₂'
  exact TensorElement.rightDepthLt_mono hbound hlt

/-! ## Level-Graded Derivation Blocks (Phase 5 Scaffold) -/

/-- Hoffman compositions of fixed weight and exact level. -/
def hoffmanLevelWeightSlice (N ℓ : ℕ) : Set Composition :=
  { s | isHoffmanComposition s ∧ s.weight = N ∧ level s = ℓ }

/-- Hoffman compositions of fixed weight and level at most `ℓ`. -/
def hoffmanWeightLevelFiltration (N ℓ : ℕ) : Set Composition :=
  { s | isHoffmanComposition s ∧ s.weight = N ∧ level s ≤ ℓ }

/-- Exact Hoffman level slice is contained in the corresponding level filtration. -/
theorem hoffmanLevelWeightSlice_subset_filtration (N ℓ : ℕ) :
    hoffmanLevelWeightSlice N ℓ ⊆ hoffmanWeightLevelFiltration N ℓ := by
  intro s hs
  rcases hs with ⟨hH, hW, hL⟩
  exact ⟨hH, hW, hL.le⟩

/-- Monotonicity in the Hoffman level filtration bound. -/
theorem hoffmanWeightLevelFiltration_mono (N ℓ : ℕ) :
    hoffmanWeightLevelFiltration N ℓ ⊆ hoffmanWeightLevelFiltration N (ℓ + 1) := by
  intro s hs
  rcases hs with ⟨hH, hW, hL⟩
  exact ⟨hH, hW, Nat.le_trans hL (Nat.le_succ ℓ)⟩

/-- A finite basis candidate for a fixed weight-level graded block. -/
structure LevelBlock where
  weight : ℕ
  levelDeg : ℕ
  basis : List Composition
  basis_hoffman : ∀ s ∈ basis, isHoffmanComposition s
  basis_weight : ∀ s ∈ basis, s.weight = weight
  basis_level : ∀ s ∈ basis, level s = levelDeg

namespace LevelBlock

/-- Rank of a level block (current finite basis length). -/
def rank (B : LevelBlock) : ℕ := B.basis.length

/-- Every basis element lies in the corresponding exact Hoffman slice. -/
theorem basis_mem_slice (B : LevelBlock) :
    ∀ s ∈ B.basis, s ∈ hoffmanLevelWeightSlice B.weight B.levelDeg := by
  intro s hs
  exact ⟨B.basis_hoffman s hs, B.basis_weight s hs, B.basis_level s hs⟩

/-- Every basis element lies in the corresponding level filtration. -/
theorem basis_mem_filtration (B : LevelBlock) :
    ∀ s ∈ B.basis, s ∈ hoffmanWeightLevelFiltration B.weight B.levelDeg := by
  intro s hs
  exact hoffmanLevelWeightSlice_subset_filtration B.weight B.levelDeg (B.basis_mem_slice s hs)

/-- Motivic lifts of basis elements lie in the corresponding motivic level filtration. -/
theorem basis_lift_mem_levelFiltration (B : LevelBlock) :
    ∀ s ∈ B.basis, MotivicMZV.ofComposition s ∈ levelFiltration B.levelDeg := by
  intro s hs
  have hsLevel : level s = B.levelDeg := B.basis_level s hs
  have hsExact : MotivicMZV.ofComposition s ∈ levelExactPiece (level s) := by
    exact ofComposition_mem_levelExactPiece s
  have hsExactB : MotivicMZV.ofComposition s ∈ levelExactPiece B.levelDeg := by
    simpa [hsLevel] using hsExact
  exact levelExactPiece_subset_levelFiltration B.levelDeg hsExactB

end LevelBlock

/-- Existence of a rank-1 level block at each weight `N ≥ 2`,
    obtained from the Hoffman existence theorem. -/
theorem exists_levelBlock_of_weight_ge2 (N : ℕ) (hN : N ≥ 2) :
    ∃ B : LevelBlock, B.weight = N ∧ B.rank = 1 := by
  rcases hoffman_composition_exists N hN with ⟨s, hsH, hsW⟩
  refine ⟨
    { weight := N
      levelDeg := level s
      basis := [s]
      basis_hoffman := by
        intro t ht
        have ht' : t = s := by simpa using ht
        simpa [ht'] using hsH
      basis_weight := by
        intro t ht
        have ht' : t = s := by simpa using ht
        simp [ht', hsW]
      basis_level := by
        intro t ht
        have ht' : t = s := by simpa using ht
        simp [ht'] }, rfl, ?_⟩
  simp [LevelBlock.rank]

namespace FormalSum

/-- Coefficient of a composition in a formal sum. -/
def coeffComp (f : FormalSum) (s : Composition) : ℚ :=
  ((f.filter fun (_, t) => t = s).map fun (q, _) => q).sum

theorem coeffComp_single (s t : Composition) :
    coeffComp (FormalSum.single s) t = (if t = s then 1 else 0) := by
  by_cases hst : s = t
  · subst hst
    simp [coeffComp, FormalSum.single]
  · have hts : t ≠ s := by intro h; exact hst h.symm
    simp [coeffComp, FormalSum.single, hst, hts]

theorem coeffComp_zero (s : Composition) : coeffComp FormalSum.zero s = 0 := by
  simp [coeffComp, FormalSum.zero]

end FormalSum

/-- Lift Ihara's derivation to motivic metadata.
    The formal part follows `iharaDerivation`, while the model stores weight shift `+ n`
    and preserves depth metadata. -/
def motivicIharaDerivation (n : ℕ) (m : MotivicMZV) : MotivicMZV where
  formal := iharaDerivation n m.formal
  weight := m.weight + n
  depth := m.depth

@[simp] theorem motivicIharaDerivation_depth (n : ℕ) (m : MotivicMZV) :
    (motivicIharaDerivation n m).depth = m.depth := rfl

@[simp] theorem motivicIharaDerivation_weight (n : ℕ) (m : MotivicMZV) :
    (motivicIharaDerivation n m).weight = m.weight + n := rfl

/-- Odd-indexed motivic derivations `∂_{2r+1}`. -/
def oddMotivicDerivation (r : ℕ) : MotivicMZV → MotivicMZV :=
  motivicIharaDerivation (2 * r + 1)

@[simp] theorem oddMotivicDerivation_depth (r : ℕ) (m : MotivicMZV) :
    (oddMotivicDerivation r m).depth = m.depth := by
  simp [oddMotivicDerivation]

@[simp] theorem oddMotivicDerivation_weight (r : ℕ) (m : MotivicMZV) :
    (oddMotivicDerivation r m).weight = m.weight + (2 * r + 1) := by
  simp [oddMotivicDerivation]

/-- Coefficient vectors on a finite basis. -/
abbrev CoeffVector (n : ℕ) := Fin n → ℚ

/-- Finite matrix block for level-graded derivation maps. -/
structure LevelMatrixBlock where
  rows : ℕ
  cols : ℕ
  entry : Fin rows → Fin cols → ℚ

namespace LevelMatrixBlock

/-- Apply a level matrix block to coefficient vectors. -/
def apply (M : LevelMatrixBlock) (v : CoeffVector M.cols) : CoeffVector M.rows :=
  fun i => (List.ofFn (fun j : Fin M.cols => M.entry i j * v j)).sum

/-- Linear-map view of matrix application on coefficient vectors. -/
def toLinearMap (M : LevelMatrixBlock) : CoeffVector M.cols →ₗ[ℚ] CoeffVector M.rows where
  toFun := M.apply
  map_add' := by
    intro v w
    funext i
    simp [apply, List.sum_ofFn, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    funext i
    have hsum : (∑ j, M.entry i j * (c * v j)) = c * (∑ j, M.entry i j * v j) := by
      calc
        (∑ j, M.entry i j * (c * v j))
            = ∑ j, c * (M.entry i j * v j) := by
                refine Finset.sum_congr rfl ?_
                intro j _hj
                ring
        _ = c * (∑ j, M.entry i j * v j) := by
              simp [Finset.mul_sum]
    simpa [apply, List.sum_ofFn, Pi.smul_apply] using hsum

@[simp] theorem toLinearMap_apply (M : LevelMatrixBlock) (v : CoeffVector M.cols) :
    M.toLinearMap v = M.apply v := rfl

@[simp] theorem apply_zero (M : LevelMatrixBlock) :
    M.apply (fun _ => 0) = (fun _ => 0) := by
  funext i
  simp [apply]

/-- Kernel predicate for matrix blocks. -/
def IsKernelVector (M : LevelMatrixBlock) (v : CoeffVector M.cols) : Prop :=
  M.apply v = (fun _ => 0)

/-- Trivial-kernel property for matrix blocks. -/
def HasTrivialKernel (M : LevelMatrixBlock) : Prop :=
  ∀ v : CoeffVector M.cols, IsKernelVector M v → v = (fun _ => 0)

/-- Injectivity of the matrix action on coefficient vectors. -/
def IsInjective (M : LevelMatrixBlock) : Prop := HasTrivialKernel M

/-- Square matrix block predicate. -/
def IsSquare (M : LevelMatrixBlock) : Prop := M.rows = M.cols

theorem hasTrivialKernel_iff_isInjective (M : LevelMatrixBlock) :
    M.HasTrivialKernel ↔ M.IsInjective := Iff.rfl

/-- A one-column matrix with at least one nonzero entry is injective. -/
theorem injective_of_cols_eq_one_of_exists_entry_ne_zero
    (M : LevelMatrixBlock) (hcols : M.cols = 1)
    (hex :
      ∃ i : Fin M.rows, M.entry i ⟨0, by simp [hcols]⟩ ≠ 0) :
    M.IsInjective := by
  intro v hv
  let col0 : Fin M.cols := ⟨0, by simp [hcols]⟩
  rcases hex with ⟨i0, hentry0⟩
  have hrow0 := congrArg (fun f => f i0) hv
  have hscalar : M.entry i0 col0 * v col0 = 0 := by
    simpa [apply, List.sum_ofFn, col0, hcols] using hrow0
  have hvcol0 : v col0 = 0 := by
    rcases mul_eq_zero.mp hscalar with hmul | hv0
    · exact (hentry0 hmul).elim
    · exact hv0
  funext j
  have hj : j = col0 := by
    apply Fin.ext
    have hjlt : j.1 < 1 := by
      simpa [hcols] using j.2
    omega
  simpa [hj] using hvcol0

/-- If a matrix has strictly fewer rows than columns, its action is not injective. -/
theorem notInjective_of_rows_lt_cols (M : LevelMatrixBlock) (h : M.rows < M.cols) :
    ¬ M.IsInjective := by
  intro hinj
  have hker_ne_bot : LinearMap.ker M.toLinearMap ≠ ⊥ := by
    have hdim :
        Module.finrank ℚ (CoeffVector M.rows) <
          Module.finrank ℚ (CoeffVector M.cols) := by
      simpa [CoeffVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h
    exact LinearMap.ker_ne_bot_of_finrank_lt (f := M.toLinearMap) hdim
  rcases (Submodule.ne_bot_iff _).1 hker_ne_bot with ⟨v, hvker, hvne⟩
  have hvKernelVector : M.IsKernelVector v := by
    exact LinearMap.mem_ker.mp hvker
  have hvzero : v = (fun _ => 0) := hinj v hvKernelVector
  exact hvne hvzero

/-- Transpose of a level matrix block. -/
def transpose (M : LevelMatrixBlock) : LevelMatrixBlock where
  rows := M.cols
  cols := M.rows
  entry := fun i j => M.entry j i

@[simp] theorem transpose_rows (M : LevelMatrixBlock) :
    M.transpose.rows = M.cols := rfl

@[simp] theorem transpose_cols (M : LevelMatrixBlock) :
    M.transpose.cols = M.rows := rfl

@[simp] theorem transpose_entry (M : LevelMatrixBlock)
    (i : Fin M.transpose.rows) (j : Fin M.transpose.cols) :
    M.transpose.entry i j = M.entry j i := rfl

@[simp] theorem transpose_transpose (M : LevelMatrixBlock) :
    M.transpose.transpose = M := by
  cases M
  rfl

@[simp] theorem transpose_isSquare_iff (M : LevelMatrixBlock) :
    M.transpose.IsSquare ↔ M.IsSquare := by
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

/-- A strict wide-shape matrix has a nontrivial kernel vector. -/
theorem exists_nonzero_kernelVector_of_rows_lt_cols
    (M : LevelMatrixBlock) (h : M.rows < M.cols) :
    ∃ v : CoeffVector M.cols, M.IsKernelVector v ∧ v ≠ (fun _ => 0) := by
  have hker_ne_bot : LinearMap.ker M.toLinearMap ≠ ⊥ := by
    have hdim :
        Module.finrank ℚ (CoeffVector M.rows) <
          Module.finrank ℚ (CoeffVector M.cols) := by
      simpa [CoeffVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h
    exact LinearMap.ker_ne_bot_of_finrank_lt (f := M.toLinearMap) hdim
  rcases (Submodule.ne_bot_iff _).1 hker_ne_bot with ⟨v, hvker, hvne⟩
  refine ⟨v, ?_, ?_⟩
  · exact LinearMap.mem_ker.mp hvker
  · simpa using hvne

/-- A nontrivial kernel vector certifies non-injectivity. -/
theorem notInjective_of_exists_nonzero_kernelVector
    (M : LevelMatrixBlock)
    (hex : ∃ v : CoeffVector M.cols, M.IsKernelVector v ∧ v ≠ (fun _ => 0)) :
    ¬ M.IsInjective := by
  intro hinj
  rcases hex with ⟨v, hvker, hvnz⟩
  have hvzero : v = (fun _ => 0) := hinj v hvker
  exact hvnz hvzero

/-- Non-injectivity is equivalent to existence of a nontrivial kernel vector. -/
theorem notInjective_iff_exists_nonzero_kernelVector
    (M : LevelMatrixBlock) :
    ¬ M.IsInjective ↔
      ∃ v : CoeffVector M.cols, M.IsKernelVector v ∧ v ≠ (fun _ => 0) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro v hv
    by_contra hvne
    have hex : ∃ w : CoeffVector M.cols, M.IsKernelVector w ∧ w ≠ (fun _ => 0) := by
      exact ⟨v, hv, hvne⟩
    exact hnone hex
  · intro hex
    exact notInjective_of_exists_nonzero_kernelVector M hex

end LevelMatrixBlock

namespace LevelBlock

/-- Coefficient vector of a formal sum in the ordered basis of a level block. -/
def coeffVectorOfFormal (B : LevelBlock) (f : FormalSum) : CoeffVector B.rank :=
  fun i => FormalSum.coeffComp f (B.basis.get i)

/-- Coefficient vector of a motivic element in the ordered basis of a level block. -/
def coeffVectorOfMotivic (B : LevelBlock) (m : MotivicMZV) : CoeffVector B.rank :=
  coeffVectorOfFormal B m.formal

/-- Odd derivation applied to the `j`-th basis element of `B`. -/
def oddDerivationOnBasis (B : LevelBlock) (r : ℕ) (j : Fin B.rank) : MotivicMZV :=
  oddMotivicDerivation r (MotivicMZV.ofComposition (B.basis.get j))

@[simp] theorem oddDerivationOnBasis_depth (B : LevelBlock) (r : ℕ) (j : Fin B.rank) :
    (oddDerivationOnBasis B r j).depth = (B.basis.get j).depth := by
  simp [oddDerivationOnBasis, MotivicMZV.ofComposition]

@[simp] theorem oddDerivationOnBasis_weight (B : LevelBlock) (r : ℕ) (j : Fin B.rank) :
    (oddDerivationOnBasis B r j).weight = (B.basis.get j).weight + (2 * r + 1) := by
  simp [oddDerivationOnBasis, MotivicMZV.ofComposition, oddMotivicDerivation_weight]

/-- `(i,j)`-entry from odd derivation of source basis and projection to target basis. -/
def oddDerivationEntry (target source : LevelBlock) (r : ℕ)
    (i : Fin target.rank) (j : Fin source.rank) : ℚ :=
  FormalSum.coeffComp (oddDerivationOnBasis source r j).formal (target.basis.get i)

/-- Concrete level-graded odd-derivation matrix block extracted from basis coefficients. -/
def oddDerivationMatrix (target source : LevelBlock) (r : ℕ) : LevelMatrixBlock where
  rows := target.rank
  cols := source.rank
  entry := oddDerivationEntry target source r

@[simp] theorem oddDerivationMatrix_rows (target source : LevelBlock) (r : ℕ) :
    (oddDerivationMatrix target source r).rows = target.rank := rfl

@[simp] theorem oddDerivationMatrix_cols (target source : LevelBlock) (r : ℕ) :
    (oddDerivationMatrix target source r).cols = source.rank := rfl

@[simp] theorem oddDerivationMatrix_entry (target source : LevelBlock) (r : ℕ)
    (i : Fin target.rank) (j : Fin source.rank) :
    (oddDerivationMatrix target source r).entry i j =
      FormalSum.coeffComp
        (oddMotivicDerivation r (MotivicMZV.ofComposition (source.basis.get j))).formal
        (target.basis.get i) := rfl

theorem oddDerivationEntry_eq_iharaDerivation_single
    (target source : LevelBlock) (r : ℕ)
    (i : Fin target.rank) (j : Fin source.rank) :
    oddDerivationEntry target source r i j =
      FormalSum.coeffComp
        (iharaDerivation (2 * r + 1) (FormalSum.single (source.basis.get j)))
        (target.basis.get i) := by
  rfl

end LevelBlock

/-- Data package for one Brown-style level-graded derivation step. -/
structure BrownLevelDerivationStep where
  source : LevelBlock
  target : LevelBlock
  matrix : LevelMatrixBlock
  rows_eq : matrix.rows = target.rank
  cols_eq : matrix.cols = source.rank
  level_drop : target.levelDeg + 1 = source.levelDeg
  weight_drop : target.weight + 1 ≤ source.weight

namespace BrownLevelDerivationStep

/-- Build a Brown-level derivation step from the concrete odd-derivation matrix
    extracted on source/target level blocks. -/
def ofOddDerivation
    (source target : LevelBlock) (r : ℕ)
    (hlevel : target.levelDeg + 1 = source.levelDeg)
    (hweight : target.weight + 1 ≤ source.weight) :
    BrownLevelDerivationStep where
  source := source
  target := target
  matrix := LevelBlock.oddDerivationMatrix target source r
  rows_eq := by simp [LevelBlock.oddDerivationMatrix, LevelBlock.rank]
  cols_eq := by simp [LevelBlock.oddDerivationMatrix, LevelBlock.rank]
  level_drop := hlevel
  weight_drop := hweight

@[simp] theorem ofOddDerivation_matrix_entry
    (source target : LevelBlock) (r : ℕ)
    (hlevel : target.levelDeg + 1 = source.levelDeg)
    (hweight : target.weight + 1 ≤ source.weight)
    (i : Fin target.rank) (j : Fin source.rank) :
    (ofOddDerivation source target r hlevel hweight).matrix.entry i j =
      LevelBlock.oddDerivationEntry target source r i j := by
  rfl

/-- Dimension compatibility condition for invertibility arguments. -/
def IsDimensionCompatible (S : BrownLevelDerivationStep) : Prop :=
  S.source.rank = S.target.rank

/-- Brown-style level drop forces positive source level. -/
theorem source_level_pos (S : BrownLevelDerivationStep) : 0 < S.source.levelDeg := by
  have : 0 < S.target.levelDeg + 1 := Nat.succ_pos _
  simpa [S.level_drop] using this

/-- Dimension compatibility yields a square matrix block. -/
theorem matrix_isSquare_of_dimensionCompatible (S : BrownLevelDerivationStep)
    (h : S.IsDimensionCompatible) : S.matrix.IsSquare := by
  unfold LevelMatrixBlock.IsSquare
  dsimp [IsDimensionCompatible] at h
  rw [S.rows_eq, S.cols_eq]
  exact h.symm

/-- Conversely, a square matrix block forces dimension compatibility. -/
theorem dimensionCompatible_of_matrix_isSquare (S : BrownLevelDerivationStep)
    (h : S.matrix.IsSquare) : S.IsDimensionCompatible := by
  unfold LevelMatrixBlock.IsSquare at h
  dsimp [IsDimensionCompatible]
  have h' : S.target.rank = S.source.rank := by
    calc
      S.target.rank = S.matrix.rows := by simpa using S.rows_eq.symm
      _ = S.matrix.cols := h
      _ = S.source.rank := by simpa using S.cols_eq
  exact h'.symm

/-- Source basis lifts are in the expected motivic level filtration. -/
theorem source_basis_lift_mem_levelFiltration (S : BrownLevelDerivationStep) :
    ∀ s ∈ S.source.basis, MotivicMZV.ofComposition s ∈ levelFiltration S.source.levelDeg := by
  exact S.source.basis_lift_mem_levelFiltration

/-- Abstract 2-adic invertibility package used in Brown's matrix step. -/
def IsTwoAdicallyInvertible (S : BrownLevelDerivationStep) : Prop :=
  S.matrix.IsSquare ∧ S.matrix.HasTrivialKernel

/-- A 2-adically invertible Brown step yields injectivity of the matrix map. -/
theorem matrix_injective_of_twoAdicallyInvertible (S : BrownLevelDerivationStep)
    (h : S.IsTwoAdicallyInvertible) : S.matrix.IsInjective := by
  exact h.2

/-- A wide Brown-step matrix is non-injective. -/
theorem matrix_notInjective_of_wide (S : BrownLevelDerivationStep)
    (hwide : S.matrix.rows < S.matrix.cols) :
    ¬ S.matrix.IsInjective := by
  exact LevelMatrixBlock.notInjective_of_rows_lt_cols S.matrix hwide

/-- A wide Brown-step matrix carries a nontrivial kernel relation. -/
theorem exists_nonzero_kernelVector_of_wide (S : BrownLevelDerivationStep)
    (hwide : S.matrix.rows < S.matrix.cols) :
    ∃ v : CoeffVector S.matrix.cols, S.matrix.IsKernelVector v ∧ v ≠ (fun _ => 0) := by
  exact LevelMatrixBlock.exists_nonzero_kernelVector_of_rows_lt_cols S.matrix hwide

/-- A wide Brown-step matrix cannot be two-adically invertible. -/
theorem notTwoAdicallyInvertible_of_wide (S : BrownLevelDerivationStep)
    (hwide : S.matrix.rows < S.matrix.cols) :
    ¬ S.IsTwoAdicallyInvertible := by
  intro h2
  rcases h2 with ⟨hsq, _hker⟩
  unfold LevelMatrixBlock.IsSquare at hsq
  have hwide' : S.matrix.rows < S.matrix.rows := by
    omega
  exact (Nat.lt_irrefl _) hwide'

/-- Three-valued status tracked by Brown-step injectivity evidence. -/
inductive InjectivityStatus where
  | proved
  | refuted
  | unknown
  deriving DecidableEq, Repr

/-- Evidence constructors used to certify injectivity status of a Brown step. -/
inductive InjectivityEvidence (S : BrownLevelDerivationStep) : Type
  | injective (h : S.matrix.IsInjective)
  | twoAdic (h : S.IsTwoAdicallyInvertible)
  | wide (h : S.matrix.rows < S.matrix.cols)
  | kernelWitness (v : CoeffVector S.matrix.cols)
      (hker : S.matrix.IsKernelVector v)
      (hnz : v ≠ (fun _ => 0))
  | unknown

namespace InjectivityEvidence

/-- Extract the tracked status from an evidence object. -/
def status {S : BrownLevelDerivationStep} (E : InjectivityEvidence S) : InjectivityStatus :=
  match E with
  | .injective _ => InjectivityStatus.proved
  | .twoAdic _ => InjectivityStatus.proved
  | .wide _ => InjectivityStatus.refuted
  | .kernelWitness .. => InjectivityStatus.refuted
  | .unknown => InjectivityStatus.unknown

/-- Proposition tracked by the evidence-derived status. -/
def statusProp {S : BrownLevelDerivationStep} (E : InjectivityEvidence S) : Prop :=
  match E.status with
  | InjectivityStatus.proved => S.matrix.IsInjective
  | InjectivityStatus.refuted => ¬ S.matrix.IsInjective
  | InjectivityStatus.unknown => True

/-- Every evidence object certifies its own tracked status proposition. -/
theorem status_sound {S : BrownLevelDerivationStep} (E : InjectivityEvidence S) :
    E.statusProp := by
  cases E with
  | injective h =>
      simpa [statusProp, status] using h
  | twoAdic h2 =>
      simpa [statusProp, status] using matrix_injective_of_twoAdicallyInvertible S h2
  | wide hwide =>
      simpa [statusProp, status] using matrix_notInjective_of_wide S hwide
  | kernelWitness v hker hnz =>
      have hnot : ¬ S.matrix.IsInjective := by
        exact LevelMatrixBlock.notInjective_of_exists_nonzero_kernelVector
          S.matrix ⟨v, hker, hnz⟩
      simpa [statusProp, status] using hnot
  | unknown =>
      simp [statusProp, status]

end InjectivityEvidence

/-- Certified Brown step carrying explicit injectivity evidence. -/
structure CertifiedStep where
  step : BrownLevelDerivationStep
  evidence : InjectivityEvidence step

namespace CertifiedStep

/-- Certified status of a Brown step. -/
def status (C : CertifiedStep) : InjectivityStatus :=
  C.evidence.status

/-- Proposition tracked by a certified step status. -/
def statusProp (C : CertifiedStep) : Prop :=
  match C.status with
  | InjectivityStatus.proved => C.step.matrix.IsInjective
  | InjectivityStatus.refuted => ¬ C.step.matrix.IsInjective
  | InjectivityStatus.unknown => True

/-- Every certified step satisfies its tracked status proposition. -/
theorem status_sound (C : CertifiedStep) : C.statusProp := by
  simpa [status, statusProp] using InjectivityEvidence.status_sound C.evidence

/-- A certified `proved` status yields matrix injectivity. -/
theorem matrixInjective_of_status_proved (C : CertifiedStep)
    (hstatus : C.status = InjectivityStatus.proved) :
    C.step.matrix.IsInjective := by
  have hsound := C.status_sound
  simpa [statusProp, hstatus] using hsound

/-- A certified `refuted` status yields matrix non-injectivity. -/
theorem matrixNotInjective_of_status_refuted (C : CertifiedStep)
    (hstatus : C.status = InjectivityStatus.refuted) :
    ¬ C.step.matrix.IsInjective := by
  have hsound := C.status_sound
  simpa [statusProp, hstatus] using hsound

/-- A certified `refuted` status yields an explicit nontrivial kernel relation. -/
theorem exists_nonzero_kernelVector_of_status_refuted (C : CertifiedStep)
    (hstatus : C.status = InjectivityStatus.refuted) :
    ∃ v : CoeffVector C.step.matrix.cols,
      C.step.matrix.IsKernelVector v ∧ v ≠ (fun _ => 0) := by
  have hnot : ¬ C.step.matrix.IsInjective :=
    matrixNotInjective_of_status_refuted C hstatus
  exact (LevelMatrixBlock.notInjective_iff_exists_nonzero_kernelVector C.step.matrix).1 hnot

end CertifiedStep

/-- Partition identity for `InjectivityStatus` counters on a status list. -/
theorem injectivityStatus_count_partition (xs : List InjectivityStatus) :
    (xs.filter (fun s => s = InjectivityStatus.proved)).length +
      (xs.filter (fun s => s = InjectivityStatus.refuted)).length +
      (xs.filter (fun s => s = InjectivityStatus.unknown)).length = xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      cases x <;> simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Generic finite Brown-development package indexed by arbitrary step labels. -/
structure FiniteDevelopment where
  Index : Type
  entries : List Index
  certify : Index → CertifiedStep

namespace FiniteDevelopment

/-- Status list extracted from a finite Brown-development package. -/
def statuses (D : FiniteDevelopment) : List InjectivityStatus :=
  D.entries.map (fun i => (D.certify i).status)

/-- Number of certified `proved` statuses in a finite package. -/
def provedCount (D : FiniteDevelopment) : ℕ :=
  (D.statuses.filter (fun s => s = InjectivityStatus.proved)).length

/-- Number of certified `refuted` statuses in a finite package. -/
def refutedCount (D : FiniteDevelopment) : ℕ :=
  (D.statuses.filter (fun s => s = InjectivityStatus.refuted)).length

/-- Number of certified `unknown` statuses in a finite package. -/
def unknownCount (D : FiniteDevelopment) : ℕ :=
  (D.statuses.filter (fun s => s = InjectivityStatus.unknown)).length

/-- Status counters form a partition of the finite package length. -/
theorem statusCount_partition (D : FiniteDevelopment) :
    D.provedCount + D.refutedCount + D.unknownCount = D.entries.length := by
  simpa [provedCount, refutedCount, unknownCount, statuses] using
    injectivityStatus_count_partition D.statuses

/-- Every listed index in a finite package has a sound certified status proposition. -/
theorem all_statuses_sound (D : FiniteDevelopment) :
    ∀ i ∈ D.entries, (D.certify i).statusProp := by
  intro i hi
  exact (D.certify i).status_sound

end FiniteDevelopment

/-- Weight/level metadata index for a Brown derivation step. -/
structure WeightLevelIndex where
  sourceWeight : ℕ
  sourceLevel : ℕ
  targetWeight : ℕ
  targetLevel : ℕ
  r : ℕ

namespace WeightLevelIndex

/-- Brown compatibility condition expected of a weight/level index. -/
def IsCompatible (I : WeightLevelIndex) : Prop :=
  I.targetLevel + 1 = I.sourceLevel ∧ I.targetWeight + 1 ≤ I.sourceWeight

end WeightLevelIndex

/-- Indexed family of Brown derivation steps with explicit weight/level metadata. -/
structure IndexedFamily where
  Index : Type
  data : Index → WeightLevelIndex
  step : Index → BrownLevelDerivationStep
  sourceWeight_eq : ∀ i, (step i).source.weight = (data i).sourceWeight
  sourceLevel_eq : ∀ i, (step i).source.levelDeg = (data i).sourceLevel
  targetWeight_eq : ∀ i, (step i).target.weight = (data i).targetWeight
  targetLevel_eq : ∀ i, (step i).target.levelDeg = (data i).targetLevel

namespace IndexedFamily

/-- Every indexed step automatically satisfies Brown compatibility at the metadata layer. -/
theorem data_isCompatible (F : IndexedFamily) (i : F.Index) :
    (F.data i).IsCompatible := by
  refine ⟨?_, ?_⟩
  · calc
      (F.data i).targetLevel + 1 = (F.step i).target.levelDeg + 1 := by
        simp [F.targetLevel_eq i]
      _ = (F.step i).source.levelDeg := (F.step i).level_drop
      _ = (F.data i).sourceLevel := by
        simp [F.sourceLevel_eq i]
  · calc
      (F.data i).targetWeight + 1 = (F.step i).target.weight + 1 := by
        simp [F.targetWeight_eq i]
      _ ≤ (F.step i).source.weight := (F.step i).weight_drop
      _ = (F.data i).sourceWeight := by
        simp [F.sourceWeight_eq i]

/-- Positive source-level consequence transported to indexed metadata. -/
theorem sourceLevel_pos (F : IndexedFamily) (i : F.Index) :
    0 < (F.data i).sourceLevel := by
  have hpos : 0 < (F.step i).source.levelDeg :=
    BrownLevelDerivationStep.source_level_pos (F.step i)
  simpa [F.sourceLevel_eq i] using hpos

/-- Source-basis motivic lifts lie in the indexed source-level filtration. -/
theorem source_basis_lift_mem_levelFiltration
    (F : IndexedFamily) (i : F.Index) :
    ∀ s ∈ (F.step i).source.basis,
      MotivicMZV.ofComposition s ∈ levelFiltration (F.data i).sourceLevel := by
  intro s hs
  have hmem :
      MotivicMZV.ofComposition s ∈ levelFiltration (F.step i).source.levelDeg :=
    (F.step i).source_basis_lift_mem_levelFiltration s hs
  simpa [F.sourceLevel_eq i] using hmem

end IndexedFamily

/-- Certified indexed family: every indexed step comes with injectivity evidence. -/
structure CertifiedIndexedFamily where
  family : IndexedFamily
  evidence : ∀ i : family.Index, InjectivityEvidence (family.step i)

namespace CertifiedIndexedFamily

/-- View one index of a certified indexed family as a certified step package. -/
def certifiedStep (C : CertifiedIndexedFamily) (i : C.family.Index) : CertifiedStep where
  step := C.family.step i
  evidence := C.evidence i

/-- Certified status at one index. -/
def status (C : CertifiedIndexedFamily) (i : C.family.Index) : InjectivityStatus :=
  (C.certifiedStep i).status

/-- Soundness of the certified status at one index. -/
theorem status_sound (C : CertifiedIndexedFamily) (i : C.family.Index) :
    (C.certifiedStep i).statusProp := by
  exact (C.certifiedStep i).status_sound

/-- Turn a certified indexed family into a finite development on a chosen finite index list. -/
def toFiniteDevelopment (C : CertifiedIndexedFamily) (entries : List C.family.Index) :
    FiniteDevelopment where
  Index := C.family.Index
  entries := entries
  certify := C.certifiedStep

/-- Counter partition for any finite stage cut out of an indexed certified family. -/
theorem finite_statusCount_partition (C : CertifiedIndexedFamily)
    (entries : List C.family.Index) :
    (C.toFiniteDevelopment entries).provedCount +
        (C.toFiniteDevelopment entries).refutedCount +
        (C.toFiniteDevelopment entries).unknownCount =
      entries.length := by
  simpa [toFiniteDevelopment] using
    (FiniteDevelopment.statusCount_partition (C.toFiniteDevelopment entries))

end CertifiedIndexedFamily

end BrownLevelDerivationStep


/-! Low-weight sample calculations have been moved out of the library core into local ignored scratch files. -/

end StringAlgebra.MZV
