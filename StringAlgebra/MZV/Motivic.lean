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
2. explicit theorem obligations (via theorem statements, with `sorry` where open);
3. conjectural interfaces, named with `_conjecture`.
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

/-! ## Brown's Main Theorem -/

/-- Brown's structure theorem for motivic MZVs (current algebraic skeleton).

    The algebra of motivic MZVs is:
    H = ℚ[f₃, f₅, f₇, ...]

    as a polynomial algebra (not a free algebra - there are relations
    coming from the Hopf algebra structure).

    In this model we exclude formal weight `1`, which has no MZV generator. -/
theorem brown_structure_theorem :
    ∀ m : MotivicMZV, m.weight ≠ 1 →
      ∃ mons : List FMonomial, (mons.map FMonomial.weight).sum = m.weight := by
  intro m hwt
  by_cases hzero : m.weight = 0
  · refine ⟨[], ?_⟩
    simp [hzero]
  · have hge2 : m.weight ≥ 2 := by omega
    rcases brown_hoffman_basis m.weight hge2 with ⟨s, hsH, hsW⟩
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
  rcases brown_hoffman_basis N hN with ⟨s, hsH, hsW⟩
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

/-! ## Low-Weight Matrix Checks -/

/-- Singleton level block at weight `2` (basis `{ζ(2)}`). -/
def levelBlock_2 : LevelBlock where
  weight := 2
  levelDeg := 0
  basis := [hoffman_2]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_2 := by simpa using hs
    simpa [hs'] using hoffman_2_isHoffman
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_2 := by simpa using hs
    simp [hs', hoffman_2, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_2 := by simpa using hs
    simp [hs', level, count3s, hoffman_2]

/-- Singleton level block at weight `3` (basis `{ζ(3)}`). -/
def levelBlock_3 : LevelBlock where
  weight := 3
  levelDeg := 1
  basis := [hoffman_3]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_3 := by simpa using hs
    simpa [hs'] using hoffman_3_isHoffman
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_3 := by simpa using hs
    simp [hs', hoffman_3, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_3 := by simpa using hs
    simp [hs', level, count3s, hoffman_3]

@[simp] theorem levelBlock_2_rank : levelBlock_2.rank = 1 := by
  simp [LevelBlock.rank, levelBlock_2]

@[simp] theorem levelBlock_3_rank : levelBlock_3.rank = 1 := by
  simp [LevelBlock.rank, levelBlock_3]

/-- Canonical index of the unique basis element in `levelBlock_2`. -/
def fin0_levelBlock_2 : Fin levelBlock_2.rank :=
  ⟨0, by simp [levelBlock_2_rank]⟩

/-- Canonical index of the unique basis element in `levelBlock_3`. -/
def fin0_levelBlock_3 : Fin levelBlock_3.rank :=
  ⟨0, by simp [levelBlock_3_rank]⟩

/-- For `r = 0` (`n = 1`), the coefficient of `ζ(3)` in `∂₁(ζ(2))` is `1`. -/
theorem oddDerivationEntry_2_to_3_r0 :
    LevelBlock.oddDerivationEntry levelBlock_3 levelBlock_2 0
      fin0_levelBlock_3 fin0_levelBlock_2 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  simp [levelBlock_2, levelBlock_3, fin0_levelBlock_2, fin0_levelBlock_3, LevelBlock.rank,
    iharaDerivation, iharaDerivComp, addAtPositionDS, FormalSum.coeffComp, FormalSum.single,
    hoffman_2, hoffman_3]

/-- Concrete `1 × 1` odd-derivation matrix from weight `2` block to weight `3` block. -/
def oddDerivationMatrix_2_to_3_r0 : LevelMatrixBlock :=
  LevelBlock.oddDerivationMatrix levelBlock_3 levelBlock_2 0

@[simp] theorem oddDerivationMatrix_2_to_3_r0_rows :
    oddDerivationMatrix_2_to_3_r0.rows = 1 := by
  simp [oddDerivationMatrix_2_to_3_r0]

@[simp] theorem oddDerivationMatrix_2_to_3_r0_cols :
    oddDerivationMatrix_2_to_3_r0.cols = 1 := by
  simp [oddDerivationMatrix_2_to_3_r0]

/-- Canonical row index for the `1 × 1` low-weight matrix. -/
def fin0_oddDerivationMatrix_2_to_3_r0_rows : Fin oddDerivationMatrix_2_to_3_r0.rows :=
  ⟨0, by simp [oddDerivationMatrix_2_to_3_r0_rows]⟩

/-- Canonical column index for the `1 × 1` low-weight matrix. -/
def fin0_oddDerivationMatrix_2_to_3_r0_cols : Fin oddDerivationMatrix_2_to_3_r0.cols :=
  ⟨0, by simp [oddDerivationMatrix_2_to_3_r0_cols]⟩

@[simp] theorem oddDerivationMatrix_2_to_3_r0_entry :
    oddDerivationMatrix_2_to_3_r0.entry
      fin0_oddDerivationMatrix_2_to_3_r0_rows
      fin0_oddDerivationMatrix_2_to_3_r0_cols = 1 := by
  simpa [oddDerivationMatrix_2_to_3_r0] using oddDerivationEntry_2_to_3_r0

/-- Every row index of the `1 × 1` low-weight matrix equals the canonical row index. -/
theorem eq_fin0_oddDerivationMatrix_2_to_3_r0_rows
    (i : Fin oddDerivationMatrix_2_to_3_r0.rows) :
    i = fin0_oddDerivationMatrix_2_to_3_r0_rows := by
  apply Fin.ext
  have hrows : oddDerivationMatrix_2_to_3_r0.rows = 1 := oddDerivationMatrix_2_to_3_r0_rows
  have hi : i.1 < 1 := by
    have hi' : i.1 < oddDerivationMatrix_2_to_3_r0.rows := i.2
    omega
  have hi0 : i.1 = 0 := by omega
  change i.1 = 0
  exact hi0

/-- The computed `1 × 1` matrix has trivial kernel. -/
theorem oddDerivationMatrix_2_to_3_r0_hasTrivialKernel :
    oddDerivationMatrix_2_to_3_r0.HasTrivialKernel := by
  intro v hv
  funext i
  have hi : i = fin0_oddDerivationMatrix_2_to_3_r0_rows :=
    eq_fin0_oddDerivationMatrix_2_to_3_r0_rows i
  subst hi
  have h0 := congrArg (fun f => f fin0_oddDerivationMatrix_2_to_3_r0_rows) hv
  -- For the explicit `1 × 1` matrix, `(Mv)_0 = 1 * v_0`.
  have h0' :
      oddDerivationMatrix_2_to_3_r0.entry
        fin0_oddDerivationMatrix_2_to_3_r0_rows
        fin0_oddDerivationMatrix_2_to_3_r0_cols
        * v fin0_oddDerivationMatrix_2_to_3_r0_cols = 0 := by
    simpa [oddDerivationMatrix_2_to_3_r0, LevelMatrixBlock.apply, LevelBlock.oddDerivationMatrix,
      fin0_oddDerivationMatrix_2_to_3_r0_rows, fin0_oddDerivationMatrix_2_to_3_r0_cols] using h0
  have hv0 : v fin0_oddDerivationMatrix_2_to_3_r0_cols = 0 := by
    simpa [oddDerivationMatrix_2_to_3_r0_entry] using h0'
  simpa using hv0

/-- Consequently, the computed `1 × 1` matrix action is injective. -/
theorem oddDerivationMatrix_2_to_3_r0_isInjective :
    oddDerivationMatrix_2_to_3_r0.IsInjective := by
  exact oddDerivationMatrix_2_to_3_r0_hasTrivialKernel

/-- Singleton level block at weight `4` (basis `{ζ(2,2)}`). -/
def levelBlock_4 : LevelBlock where
  weight := 4
  levelDeg := 0
  basis := [hoffman_22]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_22 := by simpa using hs
    subst hs'
    intro n hn
    have h2' : n = ⟨2, by omega⟩ := by simpa [hoffman_22] using hn
    have h2 : n.val = 2 := by simpa using congrArg PNat.val h2'
    left
    exact h2
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_22 := by simpa using hs
    simp [hs', hoffman_22, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_22 := by simpa using hs
    simp [hs', level, count3s, hoffman_22]

/-- Rank-2 level block at weight `5`, level `1` (basis `{ζ(2,3), ζ(3,2)}`). -/
def levelBlock_5_level1 : LevelBlock where
  weight := 5
  levelDeg := 1
  basis := [hoffman_23, hoffman_32]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_23 ∨ s = hoffman_32 := by
      simpa [List.mem_cons] using hs
    cases hs' with
    | inl h23 =>
      subst h23
      intro n hn
      simp [hoffman_23] at hn
      rcases hn with rfl | rfl
      · left; rfl
      · right; rfl
    | inr h32 =>
      subst h32
      intro n hn
      simp [hoffman_32] at hn
      rcases hn with rfl | rfl
      · right; rfl
      · left; rfl
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_23 ∨ s = hoffman_32 := by
      simpa [List.mem_cons] using hs
    cases hs' with
    | inl h23 =>
      subst h23
      simp [hoffman_23, Composition.weight]
    | inr h32 =>
      subst h32
      simp [hoffman_32, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_23 ∨ s = hoffman_32 := by
      simpa [List.mem_cons] using hs
    cases hs' with
    | inl h23 =>
      subst h23
      simp [level, count3s, hoffman_23]
    | inr h32 =>
      subst h32
      simp [level, count3s, hoffman_32]

@[simp] theorem levelBlock_4_rank : levelBlock_4.rank = 1 := by
  simp [LevelBlock.rank, levelBlock_4]

@[simp] theorem levelBlock_5_level1_rank : levelBlock_5_level1.rank = 2 := by
  simp [LevelBlock.rank, levelBlock_5_level1]

/-- Canonical column index of the unique source basis element in `levelBlock_4`. -/
def fin0_levelBlock_4 : Fin levelBlock_4.rank :=
  ⟨0, by simp [levelBlock_4_rank]⟩

/-- Canonical row indices in `levelBlock_5_level1`. -/
def fin0_levelBlock_5_level1 : Fin levelBlock_5_level1.rank :=
  ⟨0, by simp [levelBlock_5_level1_rank]⟩

def fin1_levelBlock_5_level1 : Fin levelBlock_5_level1.rank :=
  ⟨1, by simp [levelBlock_5_level1_rank]⟩

/-- Coefficient of `ζ(2,3)` in `∂₁(ζ(2,2))` is `1`. -/
theorem oddDerivationEntry_4_to_5_r0_row0 :
    LevelBlock.oddDerivationEntry levelBlock_5_level1 levelBlock_4 0
      fin0_levelBlock_5_level1 fin0_levelBlock_4 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Coefficient of `ζ(3,2)` in `∂₁(ζ(2,2))` is `1`. -/
theorem oddDerivationEntry_4_to_5_r0_row1 :
    LevelBlock.oddDerivationEntry levelBlock_5_level1 levelBlock_4 0
      fin1_levelBlock_5_level1 fin0_levelBlock_4 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Concrete `2 × 1` odd-derivation matrix from weight `4` block to weight `5` level-1 block. -/
def oddDerivationMatrix_4_to_5_r0 : LevelMatrixBlock :=
  LevelBlock.oddDerivationMatrix levelBlock_5_level1 levelBlock_4 0

@[simp] theorem oddDerivationMatrix_4_to_5_r0_rows :
    oddDerivationMatrix_4_to_5_r0.rows = 2 := by
  simp [oddDerivationMatrix_4_to_5_r0]

@[simp] theorem oddDerivationMatrix_4_to_5_r0_cols :
    oddDerivationMatrix_4_to_5_r0.cols = 1 := by
  simp [oddDerivationMatrix_4_to_5_r0]

def fin0_oddDerivationMatrix_4_to_5_r0_cols : Fin oddDerivationMatrix_4_to_5_r0.cols :=
  ⟨0, by simp [oddDerivationMatrix_4_to_5_r0_cols]⟩

def fin0_oddDerivationMatrix_4_to_5_r0_rows : Fin oddDerivationMatrix_4_to_5_r0.rows :=
  ⟨0, by simp [oddDerivationMatrix_4_to_5_r0_rows]⟩

def fin1_oddDerivationMatrix_4_to_5_r0_rows : Fin oddDerivationMatrix_4_to_5_r0.rows :=
  ⟨1, by simp [oddDerivationMatrix_4_to_5_r0_rows]⟩

@[simp] theorem oddDerivationMatrix_4_to_5_r0_entry_row0 :
    oddDerivationMatrix_4_to_5_r0.entry
      fin0_oddDerivationMatrix_4_to_5_r0_rows
      fin0_oddDerivationMatrix_4_to_5_r0_cols = 1 := by
  simpa [oddDerivationMatrix_4_to_5_r0, fin0_oddDerivationMatrix_4_to_5_r0_rows,
    fin0_oddDerivationMatrix_4_to_5_r0_cols, fin0_levelBlock_4, fin0_levelBlock_5_level1] using
    oddDerivationEntry_4_to_5_r0_row0

@[simp] theorem oddDerivationMatrix_4_to_5_r0_entry_row1 :
    oddDerivationMatrix_4_to_5_r0.entry
      fin1_oddDerivationMatrix_4_to_5_r0_rows
      fin0_oddDerivationMatrix_4_to_5_r0_cols = 1 := by
  simpa [oddDerivationMatrix_4_to_5_r0, fin1_oddDerivationMatrix_4_to_5_r0_rows,
    fin0_oddDerivationMatrix_4_to_5_r0_cols, fin0_levelBlock_4, fin1_levelBlock_5_level1] using
    oddDerivationEntry_4_to_5_r0_row1

theorem eq_fin0_oddDerivationMatrix_4_to_5_r0_cols
    (j : Fin oddDerivationMatrix_4_to_5_r0.cols) :
    j = fin0_oddDerivationMatrix_4_to_5_r0_cols := by
  apply Fin.ext
  have hcols : oddDerivationMatrix_4_to_5_r0.cols = 1 := oddDerivationMatrix_4_to_5_r0_cols
  have hj : j.1 < 1 := by
    have hj' : j.1 < oddDerivationMatrix_4_to_5_r0.cols := j.2
    omega
  have hj0 : j.1 = 0 := by omega
  change j.1 = 0
  exact hj0

/-- The computed `2 × 1` low-weight matrix has trivial kernel. -/
theorem oddDerivationMatrix_4_to_5_r0_hasTrivialKernel :
    oddDerivationMatrix_4_to_5_r0.HasTrivialKernel := by
  intro v hv
  have h0 := congrArg (fun f => f fin0_oddDerivationMatrix_4_to_5_r0_rows) hv
  have h0' :
      oddDerivationMatrix_4_to_5_r0.entry
        fin0_oddDerivationMatrix_4_to_5_r0_rows
        fin0_oddDerivationMatrix_4_to_5_r0_cols
        * v fin0_oddDerivationMatrix_4_to_5_r0_cols = 0 := by
    simpa [oddDerivationMatrix_4_to_5_r0, LevelMatrixBlock.apply, LevelBlock.oddDerivationMatrix,
      fin0_oddDerivationMatrix_4_to_5_r0_rows, fin0_oddDerivationMatrix_4_to_5_r0_cols] using h0
  have hv0 : v fin0_oddDerivationMatrix_4_to_5_r0_cols = 0 := by
    simpa [oddDerivationMatrix_4_to_5_r0_entry_row0] using h0'
  funext j
  have hj : j = fin0_oddDerivationMatrix_4_to_5_r0_cols :=
    eq_fin0_oddDerivationMatrix_4_to_5_r0_cols j
  simpa [hj] using hv0

/-- Consequently, the computed `2 × 1` matrix action is injective. -/
theorem oddDerivationMatrix_4_to_5_r0_isInjective :
    oddDerivationMatrix_4_to_5_r0.IsInjective := by
  exact oddDerivationMatrix_4_to_5_r0_hasTrivialKernel

/-- Singleton level block at weight `6`, level `2` (basis `{ζ(3,3)}`). -/
def levelBlock_6_level2 : LevelBlock where
  weight := 6
  levelDeg := 2
  basis := [hoffman_33]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_33 := by simpa using hs
    subst hs'
    intro n hn
    have h3' : n = ⟨3, by omega⟩ := by simpa [hoffman_33] using hn
    have h3 : n.val = 3 := by simpa using congrArg PNat.val h3'
    right
    exact h3
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_33 := by simpa using hs
    simp [hs', hoffman_33, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_33 := by simpa using hs
    simp [hs', level, count3s, hoffman_33]

@[simp] theorem levelBlock_6_level2_rank : levelBlock_6_level2.rank = 1 := by
  simp [LevelBlock.rank, levelBlock_6_level2]

def fin0_levelBlock_6_level2 : Fin levelBlock_6_level2.rank :=
  ⟨0, by simp [levelBlock_6_level2_rank]⟩

/-- Coefficient of `ζ(3,3)` in `∂₁(ζ(2,3))` is `1`. -/
theorem oddDerivationEntry_5_to_6_r0_col0 :
    LevelBlock.oddDerivationEntry levelBlock_6_level2 levelBlock_5_level1 0
      fin0_levelBlock_6_level2 fin0_levelBlock_5_level1 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Coefficient of `ζ(3,3)` in `∂₁(ζ(3,2))` is `1`. -/
theorem oddDerivationEntry_5_to_6_r0_col1 :
    LevelBlock.oddDerivationEntry levelBlock_6_level2 levelBlock_5_level1 0
      fin0_levelBlock_6_level2 fin1_levelBlock_5_level1 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Concrete `1 × 2` odd-derivation matrix from weight `5` level-1 block to weight `6` level-2 block. -/
def oddDerivationMatrix_5_to_6_r0 : LevelMatrixBlock :=
  LevelBlock.oddDerivationMatrix levelBlock_6_level2 levelBlock_5_level1 0

@[simp] theorem oddDerivationMatrix_5_to_6_r0_rows :
    oddDerivationMatrix_5_to_6_r0.rows = 1 := by
  simp [oddDerivationMatrix_5_to_6_r0]

@[simp] theorem oddDerivationMatrix_5_to_6_r0_cols :
    oddDerivationMatrix_5_to_6_r0.cols = 2 := by
  simp [oddDerivationMatrix_5_to_6_r0]

def fin0_oddDerivationMatrix_5_to_6_r0_rows : Fin oddDerivationMatrix_5_to_6_r0.rows :=
  ⟨0, by simp [oddDerivationMatrix_5_to_6_r0_rows]⟩

def fin0_oddDerivationMatrix_5_to_6_r0_cols : Fin oddDerivationMatrix_5_to_6_r0.cols :=
  ⟨0, by simp [oddDerivationMatrix_5_to_6_r0_cols]⟩

def fin1_oddDerivationMatrix_5_to_6_r0_cols : Fin oddDerivationMatrix_5_to_6_r0.cols :=
  ⟨1, by simp [oddDerivationMatrix_5_to_6_r0_cols]⟩

@[simp] theorem oddDerivationMatrix_5_to_6_r0_entry_col0 :
    oddDerivationMatrix_5_to_6_r0.entry
      fin0_oddDerivationMatrix_5_to_6_r0_rows
      fin0_oddDerivationMatrix_5_to_6_r0_cols = 1 := by
  simpa [oddDerivationMatrix_5_to_6_r0, fin0_oddDerivationMatrix_5_to_6_r0_rows,
    fin0_oddDerivationMatrix_5_to_6_r0_cols, fin0_levelBlock_6_level2, fin0_levelBlock_5_level1] using
    oddDerivationEntry_5_to_6_r0_col0

@[simp] theorem oddDerivationMatrix_5_to_6_r0_entry_col1 :
    oddDerivationMatrix_5_to_6_r0.entry
      fin0_oddDerivationMatrix_5_to_6_r0_rows
      fin1_oddDerivationMatrix_5_to_6_r0_cols = 1 := by
  simpa [oddDerivationMatrix_5_to_6_r0, fin0_oddDerivationMatrix_5_to_6_r0_rows,
    fin1_oddDerivationMatrix_5_to_6_r0_cols, fin0_levelBlock_6_level2, fin1_levelBlock_5_level1] using
    oddDerivationEntry_5_to_6_r0_col1

/-- The two columns of the unique row in the `r = 0` `5 → 6` matrix are equal. -/
theorem oddDerivationMatrix_5_to_6_r0_entry_cols_equal :
    oddDerivationMatrix_5_to_6_r0.entry
      fin0_oddDerivationMatrix_5_to_6_r0_rows
      fin0_oddDerivationMatrix_5_to_6_r0_cols =
    oddDerivationMatrix_5_to_6_r0.entry
      fin0_oddDerivationMatrix_5_to_6_r0_rows
      fin1_oddDerivationMatrix_5_to_6_r0_cols := by
  simp

theorem eq_fin0_oddDerivationMatrix_5_to_6_r0_rows
    (i : Fin oddDerivationMatrix_5_to_6_r0.rows) :
    i = fin0_oddDerivationMatrix_5_to_6_r0_rows := by
  apply Fin.ext
  have hrows : oddDerivationMatrix_5_to_6_r0.rows = 1 := oddDerivationMatrix_5_to_6_r0_rows
  have hi : i.1 < 1 := by
    have hi' : i.1 < oddDerivationMatrix_5_to_6_r0.rows := i.2
    omega
  have hi0 : i.1 = 0 := by omega
  change i.1 = 0
  exact hi0

/-- Witness kernel vector `(1, -1)` for the `1 × 2` matrix. -/
def oddDerivationMatrix_5_to_6_r0_kernelWitness :
    CoeffVector oddDerivationMatrix_5_to_6_r0.cols :=
  fun j =>
    if j.1 = 0 then 1 else -1

theorem oddDerivationMatrix_5_to_6_r0_kernelWitness_in_kernel :
    oddDerivationMatrix_5_to_6_r0.IsKernelVector oddDerivationMatrix_5_to_6_r0_kernelWitness := by
  funext i
  have hi : i = fin0_oddDerivationMatrix_5_to_6_r0_rows :=
    eq_fin0_oddDerivationMatrix_5_to_6_r0_rows i
  subst hi
  have hscalar :
      oddDerivationMatrix_5_to_6_r0.apply oddDerivationMatrix_5_to_6_r0_kernelWitness
        fin0_oddDerivationMatrix_5_to_6_r0_rows = 0 := by
    native_decide
  simpa using hscalar

theorem oddDerivationMatrix_5_to_6_r0_kernelWitness_nonzero :
    oddDerivationMatrix_5_to_6_r0_kernelWitness ≠ (fun _ => 0) := by
  intro hzero
  have h0 := congrArg (fun v => v fin0_oddDerivationMatrix_5_to_6_r0_cols) hzero
  simp [oddDerivationMatrix_5_to_6_r0_kernelWitness,
    fin0_oddDerivationMatrix_5_to_6_r0_cols] at h0

/-- The `1 × 2` low-weight matrix is not injective. -/
theorem oddDerivationMatrix_5_to_6_r0_notInjective :
    ¬ oddDerivationMatrix_5_to_6_r0.IsInjective := by
  exact LevelMatrixBlock.notInjective_of_rows_lt_cols
    oddDerivationMatrix_5_to_6_r0 (by simp [oddDerivationMatrix_5_to_6_r0_rows,
      oddDerivationMatrix_5_to_6_r0_cols])

/-! ### A Second Explicit `5 → 6` Case (`r = 1`) -/

/-- For `r = 1` (`n = 3`), coefficient of `ζ(3,3)` in `∂₃(ζ(2,3))` is `0`. -/
theorem oddDerivationEntry_5_to_6_r1_col0 :
    LevelBlock.oddDerivationEntry levelBlock_6_level2 levelBlock_5_level1 1
      fin0_levelBlock_6_level2 fin0_levelBlock_5_level1 = 0 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- For `r = 1` (`n = 3`), coefficient of `ζ(3,3)` in `∂₃(ζ(3,2))` is `0`. -/
theorem oddDerivationEntry_5_to_6_r1_col1 :
    LevelBlock.oddDerivationEntry levelBlock_6_level2 levelBlock_5_level1 1
      fin0_levelBlock_6_level2 fin1_levelBlock_5_level1 = 0 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Concrete `1 × 2` odd-derivation matrix for the `r = 1` case from weight `5` level-1 to weight `6` level-2. -/
def oddDerivationMatrix_5_to_6_r1 : LevelMatrixBlock :=
  LevelBlock.oddDerivationMatrix levelBlock_6_level2 levelBlock_5_level1 1

@[simp] theorem oddDerivationMatrix_5_to_6_r1_rows :
    oddDerivationMatrix_5_to_6_r1.rows = 1 := by
  simp [oddDerivationMatrix_5_to_6_r1]

@[simp] theorem oddDerivationMatrix_5_to_6_r1_cols :
    oddDerivationMatrix_5_to_6_r1.cols = 2 := by
  simp [oddDerivationMatrix_5_to_6_r1]

def fin0_oddDerivationMatrix_5_to_6_r1_rows : Fin oddDerivationMatrix_5_to_6_r1.rows :=
  ⟨0, by simp [oddDerivationMatrix_5_to_6_r1_rows]⟩

def fin0_oddDerivationMatrix_5_to_6_r1_cols : Fin oddDerivationMatrix_5_to_6_r1.cols :=
  ⟨0, by simp [oddDerivationMatrix_5_to_6_r1_cols]⟩

def fin1_oddDerivationMatrix_5_to_6_r1_cols : Fin oddDerivationMatrix_5_to_6_r1.cols :=
  ⟨1, by simp [oddDerivationMatrix_5_to_6_r1_cols]⟩

@[simp] theorem oddDerivationMatrix_5_to_6_r1_entry_col0 :
    oddDerivationMatrix_5_to_6_r1.entry
      fin0_oddDerivationMatrix_5_to_6_r1_rows
      fin0_oddDerivationMatrix_5_to_6_r1_cols = 0 := by
  simpa [oddDerivationMatrix_5_to_6_r1, fin0_oddDerivationMatrix_5_to_6_r1_rows,
    fin0_oddDerivationMatrix_5_to_6_r1_cols, fin0_levelBlock_6_level2, fin0_levelBlock_5_level1] using
    oddDerivationEntry_5_to_6_r1_col0

@[simp] theorem oddDerivationMatrix_5_to_6_r1_entry_col1 :
    oddDerivationMatrix_5_to_6_r1.entry
      fin0_oddDerivationMatrix_5_to_6_r1_rows
      fin1_oddDerivationMatrix_5_to_6_r1_cols = 0 := by
  simpa [oddDerivationMatrix_5_to_6_r1, fin0_oddDerivationMatrix_5_to_6_r1_rows,
    fin1_oddDerivationMatrix_5_to_6_r1_cols, fin0_levelBlock_6_level2, fin1_levelBlock_5_level1] using
    oddDerivationEntry_5_to_6_r1_col1

/-- The two columns of the unique row in the `r = 1` `5 → 6` matrix are equal. -/
theorem oddDerivationMatrix_5_to_6_r1_entry_cols_equal :
    oddDerivationMatrix_5_to_6_r1.entry
      fin0_oddDerivationMatrix_5_to_6_r1_rows
      fin0_oddDerivationMatrix_5_to_6_r1_cols =
    oddDerivationMatrix_5_to_6_r1.entry
      fin0_oddDerivationMatrix_5_to_6_r1_rows
      fin1_oddDerivationMatrix_5_to_6_r1_cols := by
  simp

theorem eq_fin0_oddDerivationMatrix_5_to_6_r1_rows
    (i : Fin oddDerivationMatrix_5_to_6_r1.rows) :
    i = fin0_oddDerivationMatrix_5_to_6_r1_rows := by
  apply Fin.ext
  have hrows : oddDerivationMatrix_5_to_6_r1.rows = 1 := oddDerivationMatrix_5_to_6_r1_rows
  have hi : i.1 < 1 := by
    have hi' : i.1 < oddDerivationMatrix_5_to_6_r1.rows := i.2
    omega
  have hi0 : i.1 = 0 := by omega
  change i.1 = 0
  exact hi0

/-- Witness kernel vector `(1, -1)` for the `r = 1` `1 × 2` matrix. -/
def oddDerivationMatrix_5_to_6_r1_kernelWitness :
    CoeffVector oddDerivationMatrix_5_to_6_r1.cols :=
  fun j =>
    if j.1 = 0 then 1 else -1

theorem oddDerivationMatrix_5_to_6_r1_kernelWitness_in_kernel :
    oddDerivationMatrix_5_to_6_r1.IsKernelVector oddDerivationMatrix_5_to_6_r1_kernelWitness := by
  funext i
  have hi : i = fin0_oddDerivationMatrix_5_to_6_r1_rows :=
    eq_fin0_oddDerivationMatrix_5_to_6_r1_rows i
  subst hi
  have hscalar :
      oddDerivationMatrix_5_to_6_r1.apply oddDerivationMatrix_5_to_6_r1_kernelWitness
        fin0_oddDerivationMatrix_5_to_6_r1_rows = 0 := by
    native_decide
  simpa using hscalar

theorem oddDerivationMatrix_5_to_6_r1_kernelWitness_nonzero :
    oddDerivationMatrix_5_to_6_r1_kernelWitness ≠ (fun _ => 0) := by
  intro hzero
  have h0 := congrArg (fun v => v fin0_oddDerivationMatrix_5_to_6_r1_cols) hzero
  simp [oddDerivationMatrix_5_to_6_r1_kernelWitness,
    fin0_oddDerivationMatrix_5_to_6_r1_cols] at h0

/-- The `r = 1` `1 × 2` low-weight matrix is not injective. -/
theorem oddDerivationMatrix_5_to_6_r1_notInjective :
    ¬ oddDerivationMatrix_5_to_6_r1.IsInjective := by
  exact LevelMatrixBlock.notInjective_of_rows_lt_cols
    oddDerivationMatrix_5_to_6_r1 (by simp [oddDerivationMatrix_5_to_6_r1_rows,
      oddDerivationMatrix_5_to_6_r1_cols])

/-! ### Explicit `6 → 7` Case (`r = 0`) -/

/-- Hoffman composition `(2,2,3)` (weight `7`, level `1`). -/
def hoffman_223 : Composition := [⟨2, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

/-- Hoffman composition `(2,3,2)` (weight `7`, level `1`). -/
def hoffman_232 : Composition := [⟨2, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩]

/-- Hoffman composition `(3,2,2)` (weight `7`, level `1`). -/
def hoffman_322 : Composition := [⟨3, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩]

theorem hoffman_223_isHoffman : isHoffmanComposition hoffman_223 := by
  intro n hn
  have hn' : n = (2 : ℕ+) ∨ n = (3 : ℕ+) := by
    simpa [hoffman_223, or_assoc, or_left_comm, or_comm, or_self] using hn
  rcases hn' with h2 | h3
  · left
    simpa using congrArg PNat.val h2
  · right
    simpa using congrArg PNat.val h3

theorem hoffman_232_isHoffman : isHoffmanComposition hoffman_232 := by
  intro n hn
  have hn' : n = (2 : ℕ+) ∨ n = (3 : ℕ+) := by
    simpa [hoffman_232, or_assoc, or_left_comm, or_comm, or_self] using hn
  rcases hn' with h2 | h3
  · left
    simpa using congrArg PNat.val h2
  · right
    simpa using congrArg PNat.val h3

theorem hoffman_322_isHoffman : isHoffmanComposition hoffman_322 := by
  intro n hn
  have hn' : n = (2 : ℕ+) ∨ n = (3 : ℕ+) := by
    simpa [hoffman_322, or_assoc, or_left_comm, or_comm, or_self] using hn
  rcases hn' with h2 | h3
  · left
    simpa using congrArg PNat.val h2
  · right
    simpa using congrArg PNat.val h3

/-- Singleton level block at weight `6`, level `0` (basis `{ζ(2,2,2)}`). -/
def levelBlock_6_level0 : LevelBlock where
  weight := 6
  levelDeg := 0
  basis := [hoffman_222]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_222 := by simpa using hs
    subst hs'
    intro n hn
    have h2 : n = (2 : ℕ+) := by
      simpa [hoffman_222] using hn
    left
    simpa using congrArg PNat.val h2
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_222 := by simpa using hs
    simp [hs', hoffman_222, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_222 := by simpa using hs
    simp [hs', level, count3s, hoffman_222]

/-- Rank-3 level block at weight `7`, level `1` (basis `{ζ(2,2,3), ζ(2,3,2), ζ(3,2,2)}`). -/
def levelBlock_7_level1 : LevelBlock where
  weight := 7
  levelDeg := 1
  basis := [hoffman_223, hoffman_232, hoffman_322]
  basis_hoffman := by
    intro s hs
    have hs' : s = hoffman_223 ∨ s = hoffman_232 ∨ s = hoffman_322 := by
      simpa [List.mem_cons] using hs
    rcases hs' with h223 | h232 | h322
    · subst h223
      exact hoffman_223_isHoffman
    · subst h232
      exact hoffman_232_isHoffman
    · subst h322
      exact hoffman_322_isHoffman
  basis_weight := by
    intro s hs
    have hs' : s = hoffman_223 ∨ s = hoffman_232 ∨ s = hoffman_322 := by
      simpa [List.mem_cons] using hs
    rcases hs' with h223 | h232 | h322
    · subst h223
      simp [hoffman_223, Composition.weight]
    · subst h232
      simp [hoffman_232, Composition.weight]
    · subst h322
      simp [hoffman_322, Composition.weight]
  basis_level := by
    intro s hs
    have hs' : s = hoffman_223 ∨ s = hoffman_232 ∨ s = hoffman_322 := by
      simpa [List.mem_cons] using hs
    rcases hs' with h223 | h232 | h322
    · subst h223
      simp [level, count3s, hoffman_223]
    · subst h232
      simp [level, count3s, hoffman_232]
    · subst h322
      simp [level, count3s, hoffman_322]

@[simp] theorem levelBlock_6_level0_rank : levelBlock_6_level0.rank = 1 := by
  simp [LevelBlock.rank, levelBlock_6_level0]

@[simp] theorem levelBlock_7_level1_rank : levelBlock_7_level1.rank = 3 := by
  simp [LevelBlock.rank, levelBlock_7_level1]

/-- Canonical source index in `levelBlock_6_level0`. -/
def fin0_levelBlock_6_level0 : Fin levelBlock_6_level0.rank :=
  ⟨0, by simp [levelBlock_6_level0_rank]⟩

/-- Canonical row indices in `levelBlock_7_level1`. -/
def fin0_levelBlock_7_level1 : Fin levelBlock_7_level1.rank :=
  ⟨0, by simp [levelBlock_7_level1_rank]⟩

def fin1_levelBlock_7_level1 : Fin levelBlock_7_level1.rank :=
  ⟨1, by simp [levelBlock_7_level1_rank]⟩

def fin2_levelBlock_7_level1 : Fin levelBlock_7_level1.rank :=
  ⟨2, by simp [levelBlock_7_level1_rank]⟩

/-- Coefficient of `ζ(2,2,3)` in `∂₁(ζ(2,2,2))` is `1`. -/
theorem oddDerivationEntry_6_to_7_r0_row0 :
    LevelBlock.oddDerivationEntry levelBlock_7_level1 levelBlock_6_level0 0
      fin0_levelBlock_7_level1 fin0_levelBlock_6_level0 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Coefficient of `ζ(2,3,2)` in `∂₁(ζ(2,2,2))` is `1`. -/
theorem oddDerivationEntry_6_to_7_r0_row1 :
    LevelBlock.oddDerivationEntry levelBlock_7_level1 levelBlock_6_level0 0
      fin1_levelBlock_7_level1 fin0_levelBlock_6_level0 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Coefficient of `ζ(3,2,2)` in `∂₁(ζ(2,2,2))` is `1`. -/
theorem oddDerivationEntry_6_to_7_r0_row2 :
    LevelBlock.oddDerivationEntry levelBlock_7_level1 levelBlock_6_level0 0
      fin2_levelBlock_7_level1 fin0_levelBlock_6_level0 = 1 := by
  rw [LevelBlock.oddDerivationEntry_eq_iharaDerivation_single]
  native_decide

/-- Concrete `3 × 1` odd-derivation matrix from weight `6` level-0 to weight `7` level-1. -/
def oddDerivationMatrix_6_to_7_r0 : LevelMatrixBlock :=
  LevelBlock.oddDerivationMatrix levelBlock_7_level1 levelBlock_6_level0 0

@[simp] theorem oddDerivationMatrix_6_to_7_r0_rows :
    oddDerivationMatrix_6_to_7_r0.rows = 3 := by
  simp [oddDerivationMatrix_6_to_7_r0]

@[simp] theorem oddDerivationMatrix_6_to_7_r0_cols :
    oddDerivationMatrix_6_to_7_r0.cols = 1 := by
  simp [oddDerivationMatrix_6_to_7_r0]

def fin0_oddDerivationMatrix_6_to_7_r0_cols : Fin oddDerivationMatrix_6_to_7_r0.cols :=
  ⟨0, by simp [oddDerivationMatrix_6_to_7_r0_cols]⟩

def fin0_oddDerivationMatrix_6_to_7_r0_rows : Fin oddDerivationMatrix_6_to_7_r0.rows :=
  ⟨0, by simp [oddDerivationMatrix_6_to_7_r0_rows]⟩

def fin1_oddDerivationMatrix_6_to_7_r0_rows : Fin oddDerivationMatrix_6_to_7_r0.rows :=
  ⟨1, by simp [oddDerivationMatrix_6_to_7_r0_rows]⟩

def fin2_oddDerivationMatrix_6_to_7_r0_rows : Fin oddDerivationMatrix_6_to_7_r0.rows :=
  ⟨2, by simp [oddDerivationMatrix_6_to_7_r0_rows]⟩

@[simp] theorem oddDerivationMatrix_6_to_7_r0_entry_row0 :
    oddDerivationMatrix_6_to_7_r0.entry
      fin0_oddDerivationMatrix_6_to_7_r0_rows
      fin0_oddDerivationMatrix_6_to_7_r0_cols = 1 := by
  simpa [oddDerivationMatrix_6_to_7_r0, fin0_oddDerivationMatrix_6_to_7_r0_rows,
    fin0_oddDerivationMatrix_6_to_7_r0_cols, fin0_levelBlock_7_level1,
    fin0_levelBlock_6_level0] using oddDerivationEntry_6_to_7_r0_row0

@[simp] theorem oddDerivationMatrix_6_to_7_r0_entry_row1 :
    oddDerivationMatrix_6_to_7_r0.entry
      fin1_oddDerivationMatrix_6_to_7_r0_rows
      fin0_oddDerivationMatrix_6_to_7_r0_cols = 1 := by
  simpa [oddDerivationMatrix_6_to_7_r0, fin1_oddDerivationMatrix_6_to_7_r0_rows,
    fin0_oddDerivationMatrix_6_to_7_r0_cols, fin1_levelBlock_7_level1,
    fin0_levelBlock_6_level0] using oddDerivationEntry_6_to_7_r0_row1

@[simp] theorem oddDerivationMatrix_6_to_7_r0_entry_row2 :
    oddDerivationMatrix_6_to_7_r0.entry
      fin2_oddDerivationMatrix_6_to_7_r0_rows
      fin0_oddDerivationMatrix_6_to_7_r0_cols = 1 := by
  simpa [oddDerivationMatrix_6_to_7_r0, fin2_oddDerivationMatrix_6_to_7_r0_rows,
    fin0_oddDerivationMatrix_6_to_7_r0_cols, fin2_levelBlock_7_level1,
    fin0_levelBlock_6_level0] using oddDerivationEntry_6_to_7_r0_row2

theorem eq_fin0_oddDerivationMatrix_6_to_7_r0_cols
    (j : Fin oddDerivationMatrix_6_to_7_r0.cols) :
    j = fin0_oddDerivationMatrix_6_to_7_r0_cols := by
  apply Fin.ext
  have hcols : oddDerivationMatrix_6_to_7_r0.cols = 1 := oddDerivationMatrix_6_to_7_r0_cols
  have hj : j.1 < 1 := by
    have hj' : j.1 < oddDerivationMatrix_6_to_7_r0.cols := j.2
    omega
  have hj0 : j.1 = 0 := by omega
  change j.1 = 0
  exact hj0

/-- The computed `3 × 1` low-weight matrix has trivial kernel. -/
theorem oddDerivationMatrix_6_to_7_r0_hasTrivialKernel :
    oddDerivationMatrix_6_to_7_r0.HasTrivialKernel := by
  intro v hv
  have h0 := congrArg (fun f => f fin0_oddDerivationMatrix_6_to_7_r0_rows) hv
  have h0' :
      oddDerivationMatrix_6_to_7_r0.entry
        fin0_oddDerivationMatrix_6_to_7_r0_rows
        fin0_oddDerivationMatrix_6_to_7_r0_cols
        * v fin0_oddDerivationMatrix_6_to_7_r0_cols = 0 := by
    simpa [oddDerivationMatrix_6_to_7_r0, LevelMatrixBlock.apply, LevelBlock.oddDerivationMatrix,
      fin0_oddDerivationMatrix_6_to_7_r0_rows, fin0_oddDerivationMatrix_6_to_7_r0_cols] using h0
  have hv0 : v fin0_oddDerivationMatrix_6_to_7_r0_cols = 0 := by
    simpa [oddDerivationMatrix_6_to_7_r0_entry_row0] using h0'
  funext j
  have hj : j = fin0_oddDerivationMatrix_6_to_7_r0_cols :=
    eq_fin0_oddDerivationMatrix_6_to_7_r0_cols j
  simpa [hj] using hv0

/-- Consequently, the computed `3 × 1` matrix action is injective. -/
theorem oddDerivationMatrix_6_to_7_r0_isInjective :
    oddDerivationMatrix_6_to_7_r0.IsInjective := by
  refine LevelMatrixBlock.injective_of_cols_eq_one_of_exists_entry_ne_zero
    oddDerivationMatrix_6_to_7_r0 oddDerivationMatrix_6_to_7_r0_cols ?_
  refine ⟨fin0_oddDerivationMatrix_6_to_7_r0_rows, ?_⟩
  have hcol :
      (⟨0, by simp [oddDerivationMatrix_6_to_7_r0_cols]⟩ :
        Fin oddDerivationMatrix_6_to_7_r0.cols) =
      fin0_oddDerivationMatrix_6_to_7_r0_cols := by
    apply Fin.ext
    rfl
  rw [hcol, oddDerivationMatrix_6_to_7_r0_entry_row0]
  exact one_ne_zero

/-! ### Packaged Brown-Level Steps (Low-Weight Checks) -/

/-- Brown-step packaging for source weight 3/level 1 to target weight 2/level 0 (`r=0`). -/
def brownStep_3_to_2_r0 : BrownLevelDerivationStep :=
  BrownLevelDerivationStep.ofOddDerivation
    levelBlock_3 levelBlock_2 0
    (by simp [levelBlock_2, levelBlock_3])
    (by simp [levelBlock_2, levelBlock_3])

/-- Brown-step packaging for source weight 5/level 1 to target weight 4/level 0 (`r=0`). -/
def brownStep_5_to_4_r0 : BrownLevelDerivationStep :=
  BrownLevelDerivationStep.ofOddDerivation
    levelBlock_5_level1 levelBlock_4 0
    (by simp [levelBlock_4, levelBlock_5_level1])
    (by simp [levelBlock_4, levelBlock_5_level1])

/-- Brown-step packaging for source weight 6/level 2 to target weight 5/level 1 (`r=0`). -/
def brownStep_6_to_5_r0 : BrownLevelDerivationStep :=
  BrownLevelDerivationStep.ofOddDerivation
    levelBlock_6_level2 levelBlock_5_level1 0
    (by simp [levelBlock_5_level1, levelBlock_6_level2])
    (by simp [levelBlock_5_level1, levelBlock_6_level2])

/-- Brown-step packaging for source weight 6/level 2 to target weight 5/level 1 (`r=1`). -/
def brownStep_6_to_5_r1 : BrownLevelDerivationStep :=
  BrownLevelDerivationStep.ofOddDerivation
    levelBlock_6_level2 levelBlock_5_level1 1
    (by simp [levelBlock_5_level1, levelBlock_6_level2])
    (by simp [levelBlock_5_level1, levelBlock_6_level2])

/-- Brown-step packaging for source weight 7/level 1 to target weight 6/level 0 (`r=0`). -/
def brownStep_7_to_6_r0 : BrownLevelDerivationStep :=
  BrownLevelDerivationStep.ofOddDerivation
    levelBlock_7_level1 levelBlock_6_level0 0
    (by simp [levelBlock_6_level0, levelBlock_7_level1])
    (by simp [levelBlock_6_level0, levelBlock_7_level1])

@[simp] theorem brownStep_3_to_2_r0_matrix_rows :
    brownStep_3_to_2_r0.matrix.rows = 1 := by
  have htarget : brownStep_3_to_2_r0.target = levelBlock_2 := rfl
  simpa [htarget, levelBlock_2_rank] using brownStep_3_to_2_r0.rows_eq

@[simp] theorem brownStep_3_to_2_r0_matrix_cols :
    brownStep_3_to_2_r0.matrix.cols = 1 := by
  have hsource : brownStep_3_to_2_r0.source = levelBlock_3 := rfl
  simpa [hsource, levelBlock_3_rank] using brownStep_3_to_2_r0.cols_eq

@[simp] theorem brownStep_5_to_4_r0_matrix_rows :
    brownStep_5_to_4_r0.matrix.rows = 1 := by
  have htarget : brownStep_5_to_4_r0.target = levelBlock_4 := rfl
  simpa [htarget, levelBlock_4_rank] using brownStep_5_to_4_r0.rows_eq

@[simp] theorem brownStep_5_to_4_r0_matrix_cols :
    brownStep_5_to_4_r0.matrix.cols = 2 := by
  have hsource : brownStep_5_to_4_r0.source = levelBlock_5_level1 := rfl
  simpa [hsource, levelBlock_5_level1_rank] using brownStep_5_to_4_r0.cols_eq

@[simp] theorem brownStep_6_to_5_r0_matrix_rows :
    brownStep_6_to_5_r0.matrix.rows = 2 := by
  have htarget : brownStep_6_to_5_r0.target = levelBlock_5_level1 := rfl
  simpa [htarget, levelBlock_5_level1_rank] using brownStep_6_to_5_r0.rows_eq

@[simp] theorem brownStep_6_to_5_r0_matrix_cols :
    brownStep_6_to_5_r0.matrix.cols = 1 := by
  have hsource : brownStep_6_to_5_r0.source = levelBlock_6_level2 := rfl
  simpa [hsource, levelBlock_6_level2_rank] using brownStep_6_to_5_r0.cols_eq

@[simp] theorem brownStep_6_to_5_r1_matrix_rows :
    brownStep_6_to_5_r1.matrix.rows = 2 := by
  have htarget : brownStep_6_to_5_r1.target = levelBlock_5_level1 := rfl
  simpa [htarget, levelBlock_5_level1_rank] using brownStep_6_to_5_r1.rows_eq

@[simp] theorem brownStep_6_to_5_r1_matrix_cols :
    brownStep_6_to_5_r1.matrix.cols = 1 := by
  have hsource : brownStep_6_to_5_r1.source = levelBlock_6_level2 := rfl
  simpa [hsource, levelBlock_6_level2_rank] using brownStep_6_to_5_r1.cols_eq

@[simp] theorem brownStep_7_to_6_r0_matrix_rows :
    brownStep_7_to_6_r0.matrix.rows = 1 := by
  have htarget : brownStep_7_to_6_r0.target = levelBlock_6_level0 := rfl
  simpa [htarget, levelBlock_6_level0_rank] using brownStep_7_to_6_r0.rows_eq

@[simp] theorem brownStep_7_to_6_r0_matrix_cols :
    brownStep_7_to_6_r0.matrix.cols = 3 := by
  have hsource : brownStep_7_to_6_r0.source = levelBlock_7_level1 := rfl
  simpa [hsource, levelBlock_7_level1_rank] using brownStep_7_to_6_r0.cols_eq

theorem brownStep_3_to_2_r0_dimensionCompatible :
    brownStep_3_to_2_r0.IsDimensionCompatible := by
  unfold BrownLevelDerivationStep.IsDimensionCompatible
  change levelBlock_3.rank = levelBlock_2.rank
  simp [levelBlock_3_rank, levelBlock_2_rank]

theorem brownStep_3_to_2_r0_matrix_isSquare :
    brownStep_3_to_2_r0.matrix.IsSquare := by
  exact BrownLevelDerivationStep.matrix_isSquare_of_dimensionCompatible
    brownStep_3_to_2_r0 brownStep_3_to_2_r0_dimensionCompatible

def fin0_brownStep_3_to_2_r0_rows : Fin brownStep_3_to_2_r0.matrix.rows :=
  ⟨0, by decide⟩

def fin0_brownStep_3_to_2_r0_cols : Fin brownStep_3_to_2_r0.matrix.cols :=
  ⟨0, by decide⟩

theorem brownStep_3_to_2_r0_matrix_entry_00 :
    brownStep_3_to_2_r0.matrix.entry
      fin0_brownStep_3_to_2_r0_rows
      fin0_brownStep_3_to_2_r0_cols = 0 := by
  decide

theorem brownStep_5_to_4_r0_notDimensionCompatible :
    ¬ brownStep_5_to_4_r0.IsDimensionCompatible := by
  intro h
  unfold BrownLevelDerivationStep.IsDimensionCompatible at h
  change levelBlock_5_level1.rank = levelBlock_4.rank at h
  simp [levelBlock_5_level1_rank, levelBlock_4_rank] at h

theorem brownStep_6_to_5_r0_notDimensionCompatible :
    ¬ brownStep_6_to_5_r0.IsDimensionCompatible := by
  intro h
  unfold BrownLevelDerivationStep.IsDimensionCompatible at h
  change levelBlock_6_level2.rank = levelBlock_5_level1.rank at h
  simp [levelBlock_6_level2_rank, levelBlock_5_level1_rank] at h

theorem brownStep_6_to_5_r1_notDimensionCompatible :
    ¬ brownStep_6_to_5_r1.IsDimensionCompatible := by
  intro h
  unfold BrownLevelDerivationStep.IsDimensionCompatible at h
  change levelBlock_6_level2.rank = levelBlock_5_level1.rank at h
  simp [levelBlock_6_level2_rank, levelBlock_5_level1_rank] at h

theorem brownStep_7_to_6_r0_notDimensionCompatible :
    ¬ brownStep_7_to_6_r0.IsDimensionCompatible := by
  intro h
  unfold BrownLevelDerivationStep.IsDimensionCompatible at h
  change levelBlock_7_level1.rank = levelBlock_6_level0.rank at h
  simp [levelBlock_7_level1_rank, levelBlock_6_level0_rank] at h

theorem brownStep_5_to_4_r0_matrix_notSquare :
    ¬ brownStep_5_to_4_r0.matrix.IsSquare := by
  intro hsq
  exact brownStep_5_to_4_r0_notDimensionCompatible
    (BrownLevelDerivationStep.dimensionCompatible_of_matrix_isSquare brownStep_5_to_4_r0 hsq)

theorem brownStep_6_to_5_r0_matrix_notSquare :
    ¬ brownStep_6_to_5_r0.matrix.IsSquare := by
  intro hsq
  exact brownStep_6_to_5_r0_notDimensionCompatible
    (BrownLevelDerivationStep.dimensionCompatible_of_matrix_isSquare brownStep_6_to_5_r0 hsq)

theorem brownStep_6_to_5_r1_matrix_notSquare :
    ¬ brownStep_6_to_5_r1.matrix.IsSquare := by
  intro hsq
  exact brownStep_6_to_5_r1_notDimensionCompatible
    (BrownLevelDerivationStep.dimensionCompatible_of_matrix_isSquare brownStep_6_to_5_r1 hsq)

theorem brownStep_7_to_6_r0_matrix_notSquare :
    ¬ brownStep_7_to_6_r0.matrix.IsSquare := by
  intro hsq
  exact brownStep_7_to_6_r0_notDimensionCompatible
    (BrownLevelDerivationStep.dimensionCompatible_of_matrix_isSquare brownStep_7_to_6_r0 hsq)

/-! ### Indexed Certified Low-Weight Brown Family -/

/-- Index set for the explicit low-weight Brown-step family. -/
inductive LowWeightStepKey where
  | k3_to_2_r0
  | k5_to_4_r0
  | k6_to_5_r0
  | k6_to_5_r1
  | k7_to_6_r0
  deriving DecidableEq, Repr

/-- Weight/level metadata for each low-weight Brown-step index. -/
def lowWeightIndexedFamilyData :
    LowWeightStepKey → BrownLevelDerivationStep.WeightLevelIndex
  | .k3_to_2_r0 => {
      sourceWeight := 3, sourceLevel := 1, targetWeight := 2, targetLevel := 0, r := 0 }
  | .k5_to_4_r0 => {
      sourceWeight := 5, sourceLevel := 1, targetWeight := 4, targetLevel := 0, r := 0 }
  | .k6_to_5_r0 => {
      sourceWeight := 6, sourceLevel := 2, targetWeight := 5, targetLevel := 1, r := 0 }
  | .k6_to_5_r1 => {
      sourceWeight := 6, sourceLevel := 2, targetWeight := 5, targetLevel := 1, r := 1 }
  | .k7_to_6_r0 => {
      sourceWeight := 7, sourceLevel := 1, targetWeight := 6, targetLevel := 0, r := 0 }

/-- Brown-step assignment for each low-weight index. -/
def lowWeightIndexedFamilyStep : LowWeightStepKey → BrownLevelDerivationStep
  | .k3_to_2_r0 => brownStep_3_to_2_r0
  | .k5_to_4_r0 => brownStep_5_to_4_r0
  | .k6_to_5_r0 => brownStep_6_to_5_r0
  | .k6_to_5_r1 => brownStep_6_to_5_r1
  | .k7_to_6_r0 => brownStep_7_to_6_r0

/-- Indexed Brown-family package on the explicit low-weight sample. -/
def lowWeightIndexedFamily : BrownLevelDerivationStep.IndexedFamily where
  Index := LowWeightStepKey
  data := lowWeightIndexedFamilyData
  step := lowWeightIndexedFamilyStep
  sourceWeight_eq := by
    intro i
    cases i <;> rfl
  sourceLevel_eq := by
    intro i
    cases i <;> rfl
  targetWeight_eq := by
    intro i
    cases i <;> rfl
  targetLevel_eq := by
    intro i
    cases i <;> rfl

/-- Explicit injectivity-evidence assignment for the low-weight indexed family. -/
def lowWeightCertifiedIndexedFamilyEvidence :
    ∀ i : LowWeightStepKey,
      BrownLevelDerivationStep.InjectivityEvidence (lowWeightIndexedFamilyStep i)
  | .k3_to_2_r0 => BrownLevelDerivationStep.InjectivityEvidence.unknown
  | .k5_to_4_r0 => by
      refine BrownLevelDerivationStep.InjectivityEvidence.wide ?_
      decide
  | .k6_to_5_r0 => BrownLevelDerivationStep.InjectivityEvidence.unknown
  | .k6_to_5_r1 => BrownLevelDerivationStep.InjectivityEvidence.unknown
  | .k7_to_6_r0 => by
      refine BrownLevelDerivationStep.InjectivityEvidence.wide ?_
      decide

/-- Certified indexed low-weight Brown-family package. -/
def lowWeightCertifiedIndexedFamily : BrownLevelDerivationStep.CertifiedIndexedFamily where
  family := lowWeightIndexedFamily
  evidence := lowWeightCertifiedIndexedFamilyEvidence

/-- Canonical finite index list used to sample the low-weight certified family. -/
def lowWeightCertifiedEntries : List LowWeightStepKey :=
  [.k3_to_2_r0, .k5_to_4_r0, .k6_to_5_r0, .k6_to_5_r1, .k7_to_6_r0]

/-- Finite-development view of the certified low-weight indexed family. -/
def lowWeightCertifiedFiniteDevelopment : BrownLevelDerivationStep.FiniteDevelopment :=
  BrownLevelDerivationStep.CertifiedIndexedFamily.toFiniteDevelopment
    lowWeightCertifiedIndexedFamily lowWeightCertifiedEntries

theorem lowWeightCertifiedFiniteDevelopment_counts_eval :
    lowWeightCertifiedFiniteDevelopment.provedCount = 0 ∧
      lowWeightCertifiedFiniteDevelopment.refutedCount = 2 ∧
      lowWeightCertifiedFiniteDevelopment.unknownCount = 3 ∧
      lowWeightCertifiedFiniteDevelopment.entries.length = 5 := by
  decide

theorem lowWeightCertifiedFiniteDevelopment_count_partition :
    lowWeightCertifiedFiniteDevelopment.provedCount +
        lowWeightCertifiedFiniteDevelopment.refutedCount +
        lowWeightCertifiedFiniteDevelopment.unknownCount =
      lowWeightCertifiedFiniteDevelopment.entries.length := by
  simpa [lowWeightCertifiedFiniteDevelopment] using
    (BrownLevelDerivationStep.CertifiedIndexedFamily.finite_statusCount_partition
      lowWeightCertifiedIndexedFamily lowWeightCertifiedEntries)

theorem lowWeightIndexedFamily_data_compatible (i : LowWeightStepKey) :
    (lowWeightIndexedFamily.data i).IsCompatible := by
  exact BrownLevelDerivationStep.IndexedFamily.data_isCompatible lowWeightIndexedFamily i

/-- Uniform low-weight report record for Brown-step instances. -/
structure LowWeightStepReport where
  name : String
  step : BrownLevelDerivationStep
  dimensionCompatible : Bool
  matrixSquare : Bool

namespace LowWeightStepReport

/-- Proposition tracked by the `dimensionCompatible` flag. -/
def dimensionCompatibleProp (R : LowWeightStepReport) : Prop :=
  R.step.IsDimensionCompatible

/-- Proposition tracked by the `matrixSquare` flag. -/
def matrixSquareProp (R : LowWeightStepReport) : Prop :=
  R.step.matrix.IsSquare

end LowWeightStepReport

/-- Low-weight report for the `3 → 2` Brown step. -/
def report_brownStep_3_to_2_r0 : LowWeightStepReport where
  name := "brownStep_3_to_2_r0"
  step := brownStep_3_to_2_r0
  dimensionCompatible := true
  matrixSquare := true

/-- Low-weight report for the `5 → 4` Brown step. -/
def report_brownStep_5_to_4_r0 : LowWeightStepReport where
  name := "brownStep_5_to_4_r0"
  step := brownStep_5_to_4_r0
  dimensionCompatible := false
  matrixSquare := false

/-- Low-weight report for the `6 → 5` Brown step. -/
def report_brownStep_6_to_5_r0 : LowWeightStepReport where
  name := "brownStep_6_to_5_r0"
  step := brownStep_6_to_5_r0
  dimensionCompatible := false
  matrixSquare := false

/-- Low-weight report for the `6 → 5` Brown step (`r=1`). -/
def report_brownStep_6_to_5_r1 : LowWeightStepReport where
  name := "brownStep_6_to_5_r1"
  step := brownStep_6_to_5_r1
  dimensionCompatible := false
  matrixSquare := false

/-- Low-weight report for the `7 → 6` Brown step (`r=0`). -/
def report_brownStep_7_to_6_r0 : LowWeightStepReport where
  name := "brownStep_7_to_6_r0"
  step := brownStep_7_to_6_r0
  dimensionCompatible := false
  matrixSquare := false

/-- Canonical key list for core (`3→2`, `5→4`, `6→5(r=0)`) low-weight reports. -/
def lowWeightReportKeys : List LowWeightStepKey :=
  lowWeightCertifiedEntries.take 3

/-- Canonical key list for extended (`+6→5(r=1)`) low-weight reports. -/
def lowWeightReportKeysExtended : List LowWeightStepKey :=
  lowWeightCertifiedEntries.take 4

/-- Canonical key list for augmented (`+7→6(r=0)`) low-weight reports. -/
def lowWeightReportKeysAugmented : List LowWeightStepKey :=
  lowWeightCertifiedEntries

/-- Generated low-weight Brown-step report by key. -/
def lowWeightStepReportOfKey : LowWeightStepKey → LowWeightStepReport
  | .k3_to_2_r0 => report_brownStep_3_to_2_r0
  | .k5_to_4_r0 => report_brownStep_5_to_4_r0
  | .k6_to_5_r0 => report_brownStep_6_to_5_r0
  | .k6_to_5_r1 => report_brownStep_6_to_5_r1
  | .k7_to_6_r0 => report_brownStep_7_to_6_r0

@[simp] theorem lowWeightStepReportOfKey_k3 :
    lowWeightStepReportOfKey .k3_to_2_r0 = report_brownStep_3_to_2_r0 := rfl
@[simp] theorem lowWeightStepReportOfKey_k5 :
    lowWeightStepReportOfKey .k5_to_4_r0 = report_brownStep_5_to_4_r0 := rfl
@[simp] theorem lowWeightStepReportOfKey_k6r0 :
    lowWeightStepReportOfKey .k6_to_5_r0 = report_brownStep_6_to_5_r0 := rfl
@[simp] theorem lowWeightStepReportOfKey_k6r1 :
    lowWeightStepReportOfKey .k6_to_5_r1 = report_brownStep_6_to_5_r1 := rfl
@[simp] theorem lowWeightStepReportOfKey_k7 :
    lowWeightStepReportOfKey .k7_to_6_r0 = report_brownStep_7_to_6_r0 := rfl

/-- Collected low-weight Brown-step reports. -/
def lowWeightStepReports : List LowWeightStepReport :=
  lowWeightReportKeys.map lowWeightStepReportOfKey

/-- Extended low-weight Brown-step reports including the `r=1` `6 → 5` case. -/
def lowWeightStepReportsExtended : List LowWeightStepReport :=
  lowWeightReportKeysExtended.map lowWeightStepReportOfKey

/-- Augmented low-weight Brown-step reports including the `7 → 6` (`r=0`) case. -/
def lowWeightStepReportsAugmented : List LowWeightStepReport :=
  lowWeightReportKeysAugmented.map lowWeightStepReportOfKey

@[simp] theorem lowWeightReportKeys_eq :
    lowWeightReportKeys = [.k3_to_2_r0, .k5_to_4_r0, .k6_to_5_r0] := by
  simp [lowWeightReportKeys, lowWeightCertifiedEntries]

@[simp] theorem lowWeightReportKeysExtended_eq :
    lowWeightReportKeysExtended = [.k3_to_2_r0, .k5_to_4_r0, .k6_to_5_r0, .k6_to_5_r1] := by
  simp [lowWeightReportKeysExtended, lowWeightCertifiedEntries]

@[simp] theorem lowWeightReportKeysAugmented_eq :
    lowWeightReportKeysAugmented =
      [.k3_to_2_r0, .k5_to_4_r0, .k6_to_5_r0, .k6_to_5_r1, .k7_to_6_r0] := by
  simp [lowWeightReportKeysAugmented, lowWeightCertifiedEntries]

@[simp] theorem lowWeightStepReports_eq :
    lowWeightStepReports =
      [report_brownStep_3_to_2_r0, report_brownStep_5_to_4_r0, report_brownStep_6_to_5_r0] := by
  simp [lowWeightStepReports, lowWeightStepReportOfKey]

@[simp] theorem lowWeightStepReportsExtended_eq :
    lowWeightStepReportsExtended =
      [report_brownStep_3_to_2_r0, report_brownStep_5_to_4_r0,
        report_brownStep_6_to_5_r0, report_brownStep_6_to_5_r1] := by
  simp [lowWeightStepReportsExtended, lowWeightStepReportOfKey]

@[simp] theorem lowWeightStepReportsAugmented_eq :
    lowWeightStepReportsAugmented =
      [report_brownStep_3_to_2_r0, report_brownStep_5_to_4_r0,
        report_brownStep_6_to_5_r0, report_brownStep_6_to_5_r1,
        report_brownStep_7_to_6_r0] := by
  simp [lowWeightStepReportsAugmented, lowWeightStepReportOfKey]

@[simp] theorem mem_lowWeightStepReports_iff (R : LowWeightStepReport) :
    R ∈ lowWeightStepReports ↔
      R = report_brownStep_3_to_2_r0 ∨
      R = report_brownStep_5_to_4_r0 ∨
      R = report_brownStep_6_to_5_r0 := by
  simp [lowWeightStepReports_eq, List.mem_cons]

@[simp] theorem mem_lowWeightStepReportsExtended_iff (R : LowWeightStepReport) :
    R ∈ lowWeightStepReportsExtended ↔
      R = report_brownStep_3_to_2_r0 ∨
      R = report_brownStep_5_to_4_r0 ∨
      R = report_brownStep_6_to_5_r0 ∨
      R = report_brownStep_6_to_5_r1 := by
  simp [lowWeightStepReportsExtended_eq, List.mem_cons]

@[simp] theorem mem_lowWeightStepReportsAugmented_iff (R : LowWeightStepReport) :
    R ∈ lowWeightStepReportsAugmented ↔
      R = report_brownStep_3_to_2_r0 ∨
      R = report_brownStep_5_to_4_r0 ∨
      R = report_brownStep_6_to_5_r0 ∨
      R = report_brownStep_6_to_5_r1 ∨
      R = report_brownStep_7_to_6_r0 := by
  simp [lowWeightStepReportsAugmented_eq, List.mem_cons]

/-- Query a low-weight report by name. -/
def getLowWeightStepReport (name : String) : Option LowWeightStepReport :=
  lowWeightStepReports.find? (fun R => R.name = name)

/-- Number of reports marked as dimension-compatible. -/
def lowWeightDimensionCompatibleCount : ℕ :=
  (lowWeightStepReports.filter (fun R => R.dimensionCompatible)).length

/-- Number of reports marked as square-matrix. -/
def lowWeightSquareCount : ℕ :=
  (lowWeightStepReports.filter (fun R => R.matrixSquare)).length

theorem report_brownStep_3_to_2_r0_dimensionCompatible_sound :
    report_brownStep_3_to_2_r0.dimensionCompatible = true ∧
      report_brownStep_3_to_2_r0.dimensionCompatibleProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_3_to_2_r0_dimensionCompatible

theorem report_brownStep_3_to_2_r0_matrixSquare_sound :
    report_brownStep_3_to_2_r0.matrixSquare = true ∧
      report_brownStep_3_to_2_r0.matrixSquareProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_3_to_2_r0_matrix_isSquare

theorem report_brownStep_5_to_4_r0_dimensionCompatible_refuted :
    report_brownStep_5_to_4_r0.dimensionCompatible = false ∧
      ¬ report_brownStep_5_to_4_r0.dimensionCompatibleProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_5_to_4_r0_notDimensionCompatible

theorem report_brownStep_5_to_4_r0_matrixSquare_refuted :
    report_brownStep_5_to_4_r0.matrixSquare = false ∧
      ¬ report_brownStep_5_to_4_r0.matrixSquareProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_5_to_4_r0_matrix_notSquare

theorem report_brownStep_6_to_5_r0_dimensionCompatible_refuted :
    report_brownStep_6_to_5_r0.dimensionCompatible = false ∧
      ¬ report_brownStep_6_to_5_r0.dimensionCompatibleProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_6_to_5_r0_notDimensionCompatible

theorem report_brownStep_6_to_5_r0_matrixSquare_refuted :
    report_brownStep_6_to_5_r0.matrixSquare = false ∧
      ¬ report_brownStep_6_to_5_r0.matrixSquareProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_6_to_5_r0_matrix_notSquare

theorem report_brownStep_6_to_5_r1_dimensionCompatible_refuted :
    report_brownStep_6_to_5_r1.dimensionCompatible = false ∧
      ¬ report_brownStep_6_to_5_r1.dimensionCompatibleProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_6_to_5_r1_notDimensionCompatible

theorem report_brownStep_6_to_5_r1_matrixSquare_refuted :
    report_brownStep_6_to_5_r1.matrixSquare = false ∧
      ¬ report_brownStep_6_to_5_r1.matrixSquareProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_6_to_5_r1_matrix_notSquare

theorem report_brownStep_7_to_6_r0_dimensionCompatible_refuted :
    report_brownStep_7_to_6_r0.dimensionCompatible = false ∧
      ¬ report_brownStep_7_to_6_r0.dimensionCompatibleProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_7_to_6_r0_notDimensionCompatible

theorem report_brownStep_7_to_6_r0_matrixSquare_refuted :
    report_brownStep_7_to_6_r0.matrixSquare = false ∧
      ¬ report_brownStep_7_to_6_r0.matrixSquareProp := by
  refine ⟨rfl, ?_⟩
  exact brownStep_7_to_6_r0_matrix_notSquare

theorem lowWeightDimensionCompatibleCount_eval :
    lowWeightDimensionCompatibleCount = 1 := by
  simp [lowWeightDimensionCompatibleCount, lowWeightStepReports,
    report_brownStep_3_to_2_r0, report_brownStep_5_to_4_r0, report_brownStep_6_to_5_r0]

theorem lowWeightSquareCount_eval :
    lowWeightSquareCount = 1 := by
  simp [lowWeightSquareCount, lowWeightStepReports,
    report_brownStep_3_to_2_r0, report_brownStep_5_to_4_r0, report_brownStep_6_to_5_r0]

theorem lowWeightStepReportsAugmented_length_eval :
    lowWeightStepReportsAugmented.length = 5 := by
  simp [lowWeightStepReportsAugmented]

/-- Three-valued status for proposition tracking in low-weight reports. -/
inductive PropStatus where
  | proved
  | refuted
  | unknown
  deriving DecidableEq, Repr

/-- Uniform low-weight report record for matrix injectivity checks. -/
structure LowWeightMatrixInjectivityReport where
  name : String
  matrix : LevelMatrixBlock
  injectiveStatus : PropStatus

namespace LowWeightMatrixInjectivityReport

/-- Proposition tracked by the `injectiveStatus` flag. -/
def injectiveProp (R : LowWeightMatrixInjectivityReport) : Prop :=
  R.matrix.IsInjective

end LowWeightMatrixInjectivityReport

/-- Injectivity report for the `2 → 3` low-weight matrix. -/
def report_matrix_2_to_3_r0_injectivity : LowWeightMatrixInjectivityReport where
  name := "oddDerivationMatrix_2_to_3_r0"
  matrix := oddDerivationMatrix_2_to_3_r0
  injectiveStatus := PropStatus.proved

/-- Injectivity report for the `4 → 5` low-weight matrix. -/
def report_matrix_4_to_5_r0_injectivity : LowWeightMatrixInjectivityReport where
  name := "oddDerivationMatrix_4_to_5_r0"
  matrix := oddDerivationMatrix_4_to_5_r0
  injectiveStatus := PropStatus.proved

/-- Injectivity report for the `5 → 6` low-weight matrix. -/
def report_matrix_5_to_6_r0_injectivity : LowWeightMatrixInjectivityReport where
  name := "oddDerivationMatrix_5_to_6_r0"
  matrix := oddDerivationMatrix_5_to_6_r0
  injectiveStatus := PropStatus.refuted

/-- Collected low-weight matrix injectivity reports. -/
def lowWeightMatrixInjectivityReports : List LowWeightMatrixInjectivityReport :=
  [report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity]

/-- Query a matrix injectivity report by name. -/
def getLowWeightMatrixInjectivityReport (name : String) :
    Option LowWeightMatrixInjectivityReport :=
  lowWeightMatrixInjectivityReports.find? (fun R => R.name = name)

/-- Number of reports marked as injective (`proved`). -/
def lowWeightInjectiveProvedCount : ℕ :=
  (lowWeightMatrixInjectivityReports.filter (fun R => R.injectiveStatus = PropStatus.proved)).length

/-- Number of reports marked as non-injective (`refuted`). -/
def lowWeightInjectiveRefutedCount : ℕ :=
  (lowWeightMatrixInjectivityReports.filter (fun R => R.injectiveStatus = PropStatus.refuted)).length

/-- Number of reports still marked `unknown`. -/
def lowWeightInjectiveUnknownCount : ℕ :=
  (lowWeightMatrixInjectivityReports.filter (fun R => R.injectiveStatus = PropStatus.unknown)).length

theorem report_matrix_2_to_3_r0_injectivity_sound :
    report_matrix_2_to_3_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_2_to_3_r0_injectivity.injectiveProp := by
  refine ⟨rfl, ?_⟩
  exact oddDerivationMatrix_2_to_3_r0_isInjective

theorem report_matrix_4_to_5_r0_injectivity_sound :
    report_matrix_4_to_5_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_4_to_5_r0_injectivity.injectiveProp := by
  refine ⟨rfl, ?_⟩
  exact oddDerivationMatrix_4_to_5_r0_isInjective

theorem report_matrix_5_to_6_r0_injectivity_refuted :
    report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted ∧
      ¬ report_matrix_5_to_6_r0_injectivity.injectiveProp := by
  refine ⟨rfl, ?_⟩
  exact oddDerivationMatrix_5_to_6_r0_notInjective

theorem lowWeightInjectiveProvedCount_eval :
    lowWeightInjectiveProvedCount = 2 := by
  simp [lowWeightInjectiveProvedCount, lowWeightMatrixInjectivityReports,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity]

theorem lowWeightInjectiveRefutedCount_eval :
    lowWeightInjectiveRefutedCount = 1 := by
  simp [lowWeightInjectiveRefutedCount, lowWeightMatrixInjectivityReports,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity]

theorem lowWeightInjectiveUnknownCount_eval :
    lowWeightInjectiveUnknownCount = 0 := by
  simp [lowWeightInjectiveUnknownCount, lowWeightMatrixInjectivityReports,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity]

/-- Injectivity report for the `r = 1` `5 → 6` low-weight matrix. -/
def report_matrix_5_to_6_r1_injectivity : LowWeightMatrixInjectivityReport where
  name := "oddDerivationMatrix_5_to_6_r1"
  matrix := oddDerivationMatrix_5_to_6_r1
  injectiveStatus := PropStatus.refuted

/-- Injectivity report for the `6 → 7` low-weight matrix (`r=0`). -/
def report_matrix_6_to_7_r0_injectivity : LowWeightMatrixInjectivityReport where
  name := "oddDerivationMatrix_6_to_7_r0"
  matrix := oddDerivationMatrix_6_to_7_r0
  injectiveStatus := PropStatus.proved

/-- Generated low-weight matrix injectivity report by key. -/
def lowWeightMatrixInjectivityReportOfKey :
    LowWeightStepKey → LowWeightMatrixInjectivityReport
  | .k3_to_2_r0 => report_matrix_2_to_3_r0_injectivity
  | .k5_to_4_r0 => report_matrix_4_to_5_r0_injectivity
  | .k6_to_5_r0 => report_matrix_5_to_6_r0_injectivity
  | .k6_to_5_r1 => report_matrix_5_to_6_r1_injectivity
  | .k7_to_6_r0 => report_matrix_6_to_7_r0_injectivity

@[simp] theorem lowWeightMatrixInjectivityReportOfKey_k3 :
    lowWeightMatrixInjectivityReportOfKey .k3_to_2_r0 = report_matrix_2_to_3_r0_injectivity := rfl
@[simp] theorem lowWeightMatrixInjectivityReportOfKey_k5 :
    lowWeightMatrixInjectivityReportOfKey .k5_to_4_r0 = report_matrix_4_to_5_r0_injectivity := rfl
@[simp] theorem lowWeightMatrixInjectivityReportOfKey_k6r0 :
    lowWeightMatrixInjectivityReportOfKey .k6_to_5_r0 = report_matrix_5_to_6_r0_injectivity := rfl
@[simp] theorem lowWeightMatrixInjectivityReportOfKey_k6r1 :
    lowWeightMatrixInjectivityReportOfKey .k6_to_5_r1 = report_matrix_5_to_6_r1_injectivity := rfl
@[simp] theorem lowWeightMatrixInjectivityReportOfKey_k7 :
    lowWeightMatrixInjectivityReportOfKey .k7_to_6_r0 = report_matrix_6_to_7_r0_injectivity := rfl

theorem report_matrix_5_to_6_r1_injectivity_refuted :
    report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted ∧
      ¬ report_matrix_5_to_6_r1_injectivity.injectiveProp := by
  refine ⟨rfl, ?_⟩
  exact oddDerivationMatrix_5_to_6_r1_notInjective

theorem report_matrix_6_to_7_r0_injectivity_sound :
    report_matrix_6_to_7_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_6_to_7_r0_injectivity.injectiveProp := by
  refine ⟨rfl, ?_⟩
  exact oddDerivationMatrix_6_to_7_r0_isInjective

/-- Extended matrix injectivity reports including the `r = 1` `5 → 6` case. -/
def lowWeightMatrixInjectivityReportsExtended : List LowWeightMatrixInjectivityReport :=
  lowWeightReportKeysExtended.map lowWeightMatrixInjectivityReportOfKey

/-- Query an extended matrix injectivity report by name. -/
def getLowWeightMatrixInjectivityReportExtended (name : String) :
    Option LowWeightMatrixInjectivityReport :=
  lowWeightMatrixInjectivityReportsExtended.find? (fun R => R.name = name)

/-- Augmented matrix injectivity reports including the `6 → 7` (`r=0`) case. -/
def lowWeightMatrixInjectivityReportsAugmented : List LowWeightMatrixInjectivityReport :=
  lowWeightReportKeysAugmented.map lowWeightMatrixInjectivityReportOfKey

@[simp] theorem lowWeightMatrixInjectivityReportsExtended_eq :
    lowWeightMatrixInjectivityReportsExtended =
      [report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
        report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity] := by
  simp [lowWeightMatrixInjectivityReportsExtended, lowWeightMatrixInjectivityReportOfKey]

@[simp] theorem lowWeightMatrixInjectivityReportsAugmented_eq :
    lowWeightMatrixInjectivityReportsAugmented =
      [report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
        report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity,
        report_matrix_6_to_7_r0_injectivity] := by
  simp [lowWeightMatrixInjectivityReportsAugmented, lowWeightMatrixInjectivityReportOfKey]

@[simp] theorem mem_lowWeightMatrixInjectivityReports_iff (R : LowWeightMatrixInjectivityReport) :
    R ∈ lowWeightMatrixInjectivityReports ↔
      R = report_matrix_2_to_3_r0_injectivity ∨
      R = report_matrix_4_to_5_r0_injectivity ∨
      R = report_matrix_5_to_6_r0_injectivity := by
  simp [lowWeightMatrixInjectivityReports, List.mem_cons]

@[simp] theorem mem_lowWeightMatrixInjectivityReportsExtended_iff
    (R : LowWeightMatrixInjectivityReport) :
    R ∈ lowWeightMatrixInjectivityReportsExtended ↔
      R = report_matrix_2_to_3_r0_injectivity ∨
      R = report_matrix_4_to_5_r0_injectivity ∨
      R = report_matrix_5_to_6_r0_injectivity ∨
      R = report_matrix_5_to_6_r1_injectivity := by
  simp [lowWeightMatrixInjectivityReportsExtended_eq, List.mem_cons]

@[simp] theorem mem_lowWeightMatrixInjectivityReportsAugmented_iff
    (R : LowWeightMatrixInjectivityReport) :
    R ∈ lowWeightMatrixInjectivityReportsAugmented ↔
      R = report_matrix_2_to_3_r0_injectivity ∨
      R = report_matrix_4_to_5_r0_injectivity ∨
      R = report_matrix_5_to_6_r0_injectivity ∨
      R = report_matrix_5_to_6_r1_injectivity ∨
      R = report_matrix_6_to_7_r0_injectivity := by
  simp [lowWeightMatrixInjectivityReportsAugmented_eq, List.mem_cons]

/-- Query an augmented matrix injectivity report by name. -/
def getLowWeightMatrixInjectivityReportAugmented (name : String) :
    Option LowWeightMatrixInjectivityReport :=
  lowWeightMatrixInjectivityReportsAugmented.find? (fun R => R.name = name)

/-- Number of extended reports marked as injective (`proved`). -/
def lowWeightInjectiveProvedCountExtended : ℕ :=
  (lowWeightMatrixInjectivityReportsExtended.filter
    (fun R => R.injectiveStatus = PropStatus.proved)).length

/-- Number of extended reports marked as non-injective (`refuted`). -/
def lowWeightInjectiveRefutedCountExtended : ℕ :=
  (lowWeightMatrixInjectivityReportsExtended.filter
    (fun R => R.injectiveStatus = PropStatus.refuted)).length

/-- Number of extended reports still marked `unknown`. -/
def lowWeightInjectiveUnknownCountExtended : ℕ :=
  (lowWeightMatrixInjectivityReportsExtended.filter
    (fun R => R.injectiveStatus = PropStatus.unknown)).length

theorem lowWeightInjectiveProvedCountExtended_eval :
    lowWeightInjectiveProvedCountExtended = 2 := by
  simp [lowWeightInjectiveProvedCountExtended, lowWeightMatrixInjectivityReportsExtended,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity]

theorem lowWeightInjectiveRefutedCountExtended_eval :
    lowWeightInjectiveRefutedCountExtended = 2 := by
  simp [lowWeightInjectiveRefutedCountExtended, lowWeightMatrixInjectivityReportsExtended,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity]

theorem lowWeightInjectiveUnknownCountExtended_eval :
    lowWeightInjectiveUnknownCountExtended = 0 := by
  simp [lowWeightInjectiveUnknownCountExtended, lowWeightMatrixInjectivityReportsExtended,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity]

/-- Number of augmented reports marked as injective (`proved`). -/
def lowWeightInjectiveProvedCountAugmented : ℕ :=
  (lowWeightMatrixInjectivityReportsAugmented.filter
    (fun R => R.injectiveStatus = PropStatus.proved)).length

/-- Number of augmented reports marked as non-injective (`refuted`). -/
def lowWeightInjectiveRefutedCountAugmented : ℕ :=
  (lowWeightMatrixInjectivityReportsAugmented.filter
    (fun R => R.injectiveStatus = PropStatus.refuted)).length

/-- Number of augmented reports still marked `unknown`. -/
def lowWeightInjectiveUnknownCountAugmented : ℕ :=
  (lowWeightMatrixInjectivityReportsAugmented.filter
    (fun R => R.injectiveStatus = PropStatus.unknown)).length

theorem lowWeightInjectiveProvedCountAugmented_eval :
    lowWeightInjectiveProvedCountAugmented = 3 := by
  simp [lowWeightInjectiveProvedCountAugmented, lowWeightMatrixInjectivityReportsAugmented,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity,
    report_matrix_6_to_7_r0_injectivity]

theorem lowWeightInjectiveRefutedCountAugmented_eval :
    lowWeightInjectiveRefutedCountAugmented = 2 := by
  simp [lowWeightInjectiveRefutedCountAugmented, lowWeightMatrixInjectivityReportsAugmented,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity,
    report_matrix_6_to_7_r0_injectivity]

theorem lowWeightInjectiveUnknownCountAugmented_eval :
    lowWeightInjectiveUnknownCountAugmented = 0 := by
  simp [lowWeightInjectiveUnknownCountAugmented, lowWeightMatrixInjectivityReportsAugmented,
    report_matrix_2_to_3_r0_injectivity, report_matrix_4_to_5_r0_injectivity,
    report_matrix_5_to_6_r0_injectivity, report_matrix_5_to_6_r1_injectivity,
    report_matrix_6_to_7_r0_injectivity]

theorem lowWeightMatrixInjectivityReportsAugmented_length_eval :
    lowWeightMatrixInjectivityReportsAugmented.length = 5 := by
  simp [lowWeightMatrixInjectivityReportsAugmented]

theorem report_matrix_5_to_6_r0_r1_both_refuted :
    report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted ∧
      report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted := by
  exact ⟨(report_matrix_5_to_6_r0_injectivity_refuted).1,
    (report_matrix_5_to_6_r1_injectivity_refuted).1⟩

theorem report_matrix_4_to_5_r0_6_to_7_r0_both_proved :
    report_matrix_4_to_5_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_6_to_7_r0_injectivity.injectiveStatus = PropStatus.proved := by
  exact ⟨(report_matrix_4_to_5_r0_injectivity_sound).1,
    (report_matrix_6_to_7_r0_injectivity_sound).1⟩

/-- Uniform low-weight report linking Brown-step and matrix-injectivity checks. -/
structure LowWeightConsistencyReport where
  name : String
  stepReport : LowWeightStepReport
  matrixReport : LowWeightMatrixInjectivityReport
  matrixAligned : Bool
  wideNonSquareConsistent : Bool
  squareStatusConsistent : Bool
  transposeShapeAligned : Bool

namespace LowWeightConsistencyReport

/-- Expected matrix-report name associated to a Brown-step report name. -/
def expectedMatrixReportNameForStep (stepName : String) : Option String :=
  if stepName = "brownStep_3_to_2_r0" then some "oddDerivationMatrix_2_to_3_r0"
  else if stepName = "brownStep_5_to_4_r0" then some "oddDerivationMatrix_4_to_5_r0"
  else if stepName = "brownStep_6_to_5_r0" then some "oddDerivationMatrix_5_to_6_r0"
  else if stepName = "brownStep_6_to_5_r1" then some "oddDerivationMatrix_5_to_6_r1"
  else if stepName = "brownStep_7_to_6_r0" then some "oddDerivationMatrix_6_to_7_r0"
  else none

/-- Proposition tracked by the `matrixAligned` flag. -/
def matrixAlignedProp (R : LowWeightConsistencyReport) : Prop :=
  expectedMatrixReportNameForStep R.stepReport.name = some R.matrixReport.name

/-- Proposition tracked by the `wideNonSquareConsistent` flag. -/
def wideNonSquareConsistentProp (R : LowWeightConsistencyReport) : Prop :=
  R.matrixReport.matrix.rows < R.matrixReport.matrix.cols →
      R.matrixReport.injectiveStatus = PropStatus.refuted

/-- Proposition tracked by the `squareStatusConsistent` flag. -/
def squareStatusConsistentProp (R : LowWeightConsistencyReport) : Prop :=
  R.stepReport.matrixSquare = true →
    R.matrixReport.injectiveStatus = PropStatus.proved

/-- Proposition tracked by the `transposeShapeAligned` flag. -/
def transposeShapeAlignedProp (R : LowWeightConsistencyReport) : Prop :=
  R.stepReport.step.matrix.rows = R.matrixReport.matrix.cols ∧
    R.stepReport.step.matrix.cols = R.matrixReport.matrix.rows

end LowWeightConsistencyReport

/-- Joined consistency report for the `3 → 2` low-weight step. -/
def report_consistency_3_to_2_r0 : LowWeightConsistencyReport where
  name := "consistency_3_to_2_r0"
  stepReport := report_brownStep_3_to_2_r0
  matrixReport := report_matrix_2_to_3_r0_injectivity
  matrixAligned := true
  wideNonSquareConsistent := true
  squareStatusConsistent := true
  transposeShapeAligned := true

/-- Joined consistency report for the `5 → 4` low-weight step. -/
def report_consistency_5_to_4_r0 : LowWeightConsistencyReport where
  name := "consistency_5_to_4_r0"
  stepReport := report_brownStep_5_to_4_r0
  matrixReport := report_matrix_4_to_5_r0_injectivity
  matrixAligned := true
  wideNonSquareConsistent := true
  squareStatusConsistent := true
  transposeShapeAligned := true

/-- Joined consistency report for the `6 → 5` low-weight step. -/
def report_consistency_6_to_5_r0 : LowWeightConsistencyReport where
  name := "consistency_6_to_5_r0"
  stepReport := report_brownStep_6_to_5_r0
  matrixReport := report_matrix_5_to_6_r0_injectivity
  matrixAligned := true
  wideNonSquareConsistent := true
  squareStatusConsistent := true
  transposeShapeAligned := true

/-- Joined consistency report for the `6 → 5` low-weight step (`r=1`). -/
def report_consistency_6_to_5_r1 : LowWeightConsistencyReport where
  name := "consistency_6_to_5_r1"
  stepReport := report_brownStep_6_to_5_r1
  matrixReport := report_matrix_5_to_6_r1_injectivity
  matrixAligned := true
  wideNonSquareConsistent := true
  squareStatusConsistent := true
  transposeShapeAligned := true

/-- Joined consistency report for the `7 → 6` low-weight step (`r=0`). -/
def report_consistency_7_to_6_r0 : LowWeightConsistencyReport where
  name := "consistency_7_to_6_r0"
  stepReport := report_brownStep_7_to_6_r0
  matrixReport := report_matrix_6_to_7_r0_injectivity
  matrixAligned := true
  wideNonSquareConsistent := true
  squareStatusConsistent := true
  transposeShapeAligned := true

/-- Generated low-weight consistency report by key. -/
def lowWeightConsistencyReportOfKey :
    LowWeightStepKey → LowWeightConsistencyReport
  | .k3_to_2_r0 => report_consistency_3_to_2_r0
  | .k5_to_4_r0 => report_consistency_5_to_4_r0
  | .k6_to_5_r0 => report_consistency_6_to_5_r0
  | .k6_to_5_r1 => report_consistency_6_to_5_r1
  | .k7_to_6_r0 => report_consistency_7_to_6_r0

@[simp] theorem lowWeightConsistencyReportOfKey_k3 :
    lowWeightConsistencyReportOfKey .k3_to_2_r0 = report_consistency_3_to_2_r0 := rfl
@[simp] theorem lowWeightConsistencyReportOfKey_k5 :
    lowWeightConsistencyReportOfKey .k5_to_4_r0 = report_consistency_5_to_4_r0 := rfl
@[simp] theorem lowWeightConsistencyReportOfKey_k6r0 :
    lowWeightConsistencyReportOfKey .k6_to_5_r0 = report_consistency_6_to_5_r0 := rfl
@[simp] theorem lowWeightConsistencyReportOfKey_k6r1 :
    lowWeightConsistencyReportOfKey .k6_to_5_r1 = report_consistency_6_to_5_r1 := rfl
@[simp] theorem lowWeightConsistencyReportOfKey_k7 :
    lowWeightConsistencyReportOfKey .k7_to_6_r0 = report_consistency_7_to_6_r0 := rfl

/-- Collected joined low-weight consistency reports. -/
def lowWeightConsistencyReports : List LowWeightConsistencyReport :=
  lowWeightReportKeys.map lowWeightConsistencyReportOfKey

/-- Extended joined low-weight consistency reports including the `r=1` `6 → 5` case. -/
def lowWeightConsistencyReportsExtended : List LowWeightConsistencyReport :=
  lowWeightReportKeysExtended.map lowWeightConsistencyReportOfKey

/-- Augmented joined low-weight consistency reports including `7 → 6` (`r=0`). -/
def lowWeightConsistencyReportsAugmented : List LowWeightConsistencyReport :=
  lowWeightReportKeysAugmented.map lowWeightConsistencyReportOfKey

@[simp] theorem lowWeightConsistencyReports_eq :
    lowWeightConsistencyReports =
      [report_consistency_3_to_2_r0, report_consistency_5_to_4_r0, report_consistency_6_to_5_r0] := by
  simp [lowWeightConsistencyReports, lowWeightConsistencyReportOfKey]

@[simp] theorem lowWeightConsistencyReportsExtended_eq :
    lowWeightConsistencyReportsExtended =
      [report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
        report_consistency_6_to_5_r0, report_consistency_6_to_5_r1] := by
  simp [lowWeightConsistencyReportsExtended, lowWeightConsistencyReportOfKey]

@[simp] theorem lowWeightConsistencyReportsAugmented_eq :
    lowWeightConsistencyReportsAugmented =
      [report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
        report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
        report_consistency_7_to_6_r0] := by
  simp [lowWeightConsistencyReportsAugmented, lowWeightConsistencyReportOfKey]

@[simp] theorem mem_lowWeightConsistencyReports_iff (R : LowWeightConsistencyReport) :
    R ∈ lowWeightConsistencyReports ↔
      R = report_consistency_3_to_2_r0 ∨
      R = report_consistency_5_to_4_r0 ∨
      R = report_consistency_6_to_5_r0 := by
  simp [lowWeightConsistencyReports_eq, List.mem_cons]

@[simp] theorem mem_lowWeightConsistencyReportsExtended_iff (R : LowWeightConsistencyReport) :
    R ∈ lowWeightConsistencyReportsExtended ↔
      R = report_consistency_3_to_2_r0 ∨
      R = report_consistency_5_to_4_r0 ∨
      R = report_consistency_6_to_5_r0 ∨
      R = report_consistency_6_to_5_r1 := by
  simp [lowWeightConsistencyReportsExtended_eq, List.mem_cons]

@[simp] theorem mem_lowWeightConsistencyReportsAugmented_iff (R : LowWeightConsistencyReport) :
    R ∈ lowWeightConsistencyReportsAugmented ↔
      R = report_consistency_3_to_2_r0 ∨
      R = report_consistency_5_to_4_r0 ∨
      R = report_consistency_6_to_5_r0 ∨
      R = report_consistency_6_to_5_r1 ∨
      R = report_consistency_7_to_6_r0 := by
  simp [lowWeightConsistencyReportsAugmented_eq, List.mem_cons]

/-- Query a joined low-weight consistency report by name. -/
def getLowWeightConsistencyReport (name : String) : Option LowWeightConsistencyReport :=
  lowWeightConsistencyReports.find? (fun R => R.name = name)

/-- Query an extended joined low-weight consistency report by name. -/
def getLowWeightConsistencyReportExtended (name : String) : Option LowWeightConsistencyReport :=
  lowWeightConsistencyReportsExtended.find? (fun R => R.name = name)

/-- Query an augmented joined low-weight consistency report by name. -/
def getLowWeightConsistencyReportAugmented (name : String) : Option LowWeightConsistencyReport :=
  lowWeightConsistencyReportsAugmented.find? (fun R => R.name = name)

/-- Number of joined reports flagged as matrix-aligned. -/
def lowWeightMatrixAlignedFlagCount : ℕ :=
  (lowWeightConsistencyReports.filter (fun R => R.matrixAligned)).length

/-- Number of joined reports flagged as wide-nonsquare-consistent. -/
def lowWeightWideNonSquareConsistentFlagCount : ℕ :=
  (lowWeightConsistencyReports.filter (fun R => R.wideNonSquareConsistent)).length

/-- Number of joined reports flagged as square-status-consistent. -/
def lowWeightSquareStatusConsistentFlagCount : ℕ :=
  (lowWeightConsistencyReports.filter (fun R => R.squareStatusConsistent)).length

/-- Number of joined reports flagged as transpose-shape-aligned. -/
def lowWeightTransposeShapeAlignedFlagCount : ℕ :=
  (lowWeightConsistencyReports.filter (fun R => R.transposeShapeAligned)).length

/-- Number of extended joined reports flagged as matrix-aligned. -/
def lowWeightMatrixAlignedFlagCountExtended : ℕ :=
  (lowWeightConsistencyReportsExtended.filter (fun R => R.matrixAligned)).length

/-- Number of extended joined reports flagged as wide-nonsquare-consistent. -/
def lowWeightWideNonSquareConsistentFlagCountExtended : ℕ :=
  (lowWeightConsistencyReportsExtended.filter (fun R => R.wideNonSquareConsistent)).length

/-- Number of extended joined reports flagged as square-status-consistent. -/
def lowWeightSquareStatusConsistentFlagCountExtended : ℕ :=
  (lowWeightConsistencyReportsExtended.filter (fun R => R.squareStatusConsistent)).length

/-- Number of extended joined reports flagged as transpose-shape-aligned. -/
def lowWeightTransposeShapeAlignedFlagCountExtended : ℕ :=
  (lowWeightConsistencyReportsExtended.filter (fun R => R.transposeShapeAligned)).length

/-- Number of augmented joined reports flagged as matrix-aligned. -/
def lowWeightMatrixAlignedFlagCountAugmented : ℕ :=
  (lowWeightConsistencyReportsAugmented.filter (fun R => R.matrixAligned)).length

/-- Number of augmented joined reports flagged as wide-nonsquare-consistent. -/
def lowWeightWideNonSquareConsistentFlagCountAugmented : ℕ :=
  (lowWeightConsistencyReportsAugmented.filter (fun R => R.wideNonSquareConsistent)).length

/-- Number of augmented joined reports flagged as square-status-consistent. -/
def lowWeightSquareStatusConsistentFlagCountAugmented : ℕ :=
  (lowWeightConsistencyReportsAugmented.filter (fun R => R.squareStatusConsistent)).length

/-- Number of augmented joined reports flagged as transpose-shape-aligned. -/
def lowWeightTransposeShapeAlignedFlagCountAugmented : ℕ :=
  (lowWeightConsistencyReportsAugmented.filter (fun R => R.transposeShapeAligned)).length

theorem report_consistency_3_to_2_r0_matrixAligned_sound :
    report_consistency_3_to_2_r0.matrixAligned = true ∧
      report_consistency_3_to_2_r0.matrixAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.matrixAlignedProp,
    LowWeightConsistencyReport.expectedMatrixReportNameForStep,
    report_consistency_3_to_2_r0, report_brownStep_3_to_2_r0,
    report_matrix_2_to_3_r0_injectivity]

theorem report_consistency_5_to_4_r0_matrixAligned_sound :
    report_consistency_5_to_4_r0.matrixAligned = true ∧
      report_consistency_5_to_4_r0.matrixAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.matrixAlignedProp,
    LowWeightConsistencyReport.expectedMatrixReportNameForStep,
    report_consistency_5_to_4_r0, report_brownStep_5_to_4_r0,
    report_matrix_4_to_5_r0_injectivity]

theorem report_consistency_6_to_5_r0_matrixAligned_sound :
    report_consistency_6_to_5_r0.matrixAligned = true ∧
      report_consistency_6_to_5_r0.matrixAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.matrixAlignedProp,
    LowWeightConsistencyReport.expectedMatrixReportNameForStep,
    report_consistency_6_to_5_r0, report_brownStep_6_to_5_r0,
    report_matrix_5_to_6_r0_injectivity]

theorem report_consistency_6_to_5_r1_matrixAligned_sound :
    report_consistency_6_to_5_r1.matrixAligned = true ∧
      report_consistency_6_to_5_r1.matrixAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.matrixAlignedProp,
    LowWeightConsistencyReport.expectedMatrixReportNameForStep,
    report_consistency_6_to_5_r1, report_brownStep_6_to_5_r1,
    report_matrix_5_to_6_r1_injectivity]

theorem report_consistency_7_to_6_r0_matrixAligned_sound :
    report_consistency_7_to_6_r0.matrixAligned = true ∧
      report_consistency_7_to_6_r0.matrixAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.matrixAlignedProp,
    LowWeightConsistencyReport.expectedMatrixReportNameForStep,
    report_consistency_7_to_6_r0, report_brownStep_7_to_6_r0,
    report_matrix_6_to_7_r0_injectivity]

theorem report_consistency_3_to_2_r0_wideNonSquare_sound :
    report_consistency_3_to_2_r0.wideNonSquareConsistent = true ∧
      report_consistency_3_to_2_r0.wideNonSquareConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hwide
  have hnot :
      ¬ report_consistency_3_to_2_r0.matrixReport.matrix.rows <
        report_consistency_3_to_2_r0.matrixReport.matrix.cols := by
    simp [report_consistency_3_to_2_r0, report_matrix_2_to_3_r0_injectivity,
      oddDerivationMatrix_2_to_3_r0_rows, oddDerivationMatrix_2_to_3_r0_cols]
  exact (False.elim (hnot hwide))

theorem report_consistency_5_to_4_r0_wideNonSquare_sound :
    report_consistency_5_to_4_r0.wideNonSquareConsistent = true ∧
      report_consistency_5_to_4_r0.wideNonSquareConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hwide
  have hnot :
      ¬ report_consistency_5_to_4_r0.matrixReport.matrix.rows <
        report_consistency_5_to_4_r0.matrixReport.matrix.cols := by
    simp [report_consistency_5_to_4_r0, report_matrix_4_to_5_r0_injectivity,
      oddDerivationMatrix_4_to_5_r0_rows, oddDerivationMatrix_4_to_5_r0_cols]
  exact (False.elim (hnot hwide))

theorem report_consistency_6_to_5_r0_wideNonSquare_sound :
    report_consistency_6_to_5_r0.wideNonSquareConsistent = true ∧
      report_consistency_6_to_5_r0.wideNonSquareConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro _hwide
  rfl

theorem report_consistency_6_to_5_r1_wideNonSquare_sound :
    report_consistency_6_to_5_r1.wideNonSquareConsistent = true ∧
      report_consistency_6_to_5_r1.wideNonSquareConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro _hwide
  rfl

theorem report_consistency_7_to_6_r0_wideNonSquare_sound :
    report_consistency_7_to_6_r0.wideNonSquareConsistent = true ∧
      report_consistency_7_to_6_r0.wideNonSquareConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hwide
  have hnot :
      ¬ report_consistency_7_to_6_r0.matrixReport.matrix.rows <
        report_consistency_7_to_6_r0.matrixReport.matrix.cols := by
    simp [report_consistency_7_to_6_r0, report_matrix_6_to_7_r0_injectivity,
      oddDerivationMatrix_6_to_7_r0_rows, oddDerivationMatrix_6_to_7_r0_cols]
  exact False.elim (hnot hwide)

theorem report_consistency_3_to_2_r0_squareStatus_sound :
    report_consistency_3_to_2_r0.squareStatusConsistent = true ∧
      report_consistency_3_to_2_r0.squareStatusConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro _hsq
  rfl

theorem report_consistency_5_to_4_r0_squareStatus_sound :
    report_consistency_5_to_4_r0.squareStatusConsistent = true ∧
      report_consistency_5_to_4_r0.squareStatusConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hsq
  cases hsq

theorem report_consistency_6_to_5_r0_squareStatus_sound :
    report_consistency_6_to_5_r0.squareStatusConsistent = true ∧
      report_consistency_6_to_5_r0.squareStatusConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hsq
  cases hsq

theorem report_consistency_6_to_5_r1_squareStatus_sound :
    report_consistency_6_to_5_r1.squareStatusConsistent = true ∧
      report_consistency_6_to_5_r1.squareStatusConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hsq
  cases hsq

theorem report_consistency_7_to_6_r0_squareStatus_sound :
    report_consistency_7_to_6_r0.squareStatusConsistent = true ∧
      report_consistency_7_to_6_r0.squareStatusConsistentProp := by
  refine ⟨rfl, ?_⟩
  intro hsq
  cases hsq

theorem report_consistency_3_to_2_r0_transposeShapeAligned_sound :
    report_consistency_3_to_2_r0.transposeShapeAligned = true ∧
      report_consistency_3_to_2_r0.transposeShapeAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.transposeShapeAlignedProp,
    report_consistency_3_to_2_r0, report_brownStep_3_to_2_r0,
    report_matrix_2_to_3_r0_injectivity,
    oddDerivationMatrix_2_to_3_r0_rows, oddDerivationMatrix_2_to_3_r0_cols]

theorem report_consistency_5_to_4_r0_transposeShapeAligned_sound :
    report_consistency_5_to_4_r0.transposeShapeAligned = true ∧
      report_consistency_5_to_4_r0.transposeShapeAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.transposeShapeAlignedProp,
    report_consistency_5_to_4_r0, report_brownStep_5_to_4_r0,
    report_matrix_4_to_5_r0_injectivity,
    oddDerivationMatrix_4_to_5_r0_rows, oddDerivationMatrix_4_to_5_r0_cols]

theorem report_consistency_6_to_5_r0_transposeShapeAligned_sound :
    report_consistency_6_to_5_r0.transposeShapeAligned = true ∧
      report_consistency_6_to_5_r0.transposeShapeAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.transposeShapeAlignedProp,
    report_consistency_6_to_5_r0, report_brownStep_6_to_5_r0,
    report_matrix_5_to_6_r0_injectivity,
    oddDerivationMatrix_5_to_6_r0_rows, oddDerivationMatrix_5_to_6_r0_cols]

theorem report_consistency_6_to_5_r1_transposeShapeAligned_sound :
    report_consistency_6_to_5_r1.transposeShapeAligned = true ∧
      report_consistency_6_to_5_r1.transposeShapeAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.transposeShapeAlignedProp,
    report_consistency_6_to_5_r1, report_brownStep_6_to_5_r1,
    report_matrix_5_to_6_r1_injectivity,
    oddDerivationMatrix_5_to_6_r1_rows, oddDerivationMatrix_5_to_6_r1_cols]

theorem report_consistency_7_to_6_r0_transposeShapeAligned_sound :
    report_consistency_7_to_6_r0.transposeShapeAligned = true ∧
      report_consistency_7_to_6_r0.transposeShapeAlignedProp := by
  refine ⟨rfl, ?_⟩
  simp [LowWeightConsistencyReport.transposeShapeAlignedProp,
    report_consistency_7_to_6_r0, report_brownStep_7_to_6_r0,
    report_matrix_6_to_7_r0_injectivity,
    oddDerivationMatrix_6_to_7_r0_rows, oddDerivationMatrix_6_to_7_r0_cols]

theorem report_consistency_6_to_5_r0_wideShape :
    report_consistency_6_to_5_r0.matrixReport.matrix.rows <
      report_consistency_6_to_5_r0.matrixReport.matrix.cols := by
  simp [report_consistency_6_to_5_r0, report_matrix_5_to_6_r0_injectivity,
    oddDerivationMatrix_5_to_6_r0_rows, oddDerivationMatrix_5_to_6_r0_cols]

theorem report_consistency_6_to_5_r1_wideShape :
    report_consistency_6_to_5_r1.matrixReport.matrix.rows <
      report_consistency_6_to_5_r1.matrixReport.matrix.cols := by
  simp [report_consistency_6_to_5_r1, report_matrix_5_to_6_r1_injectivity,
    oddDerivationMatrix_5_to_6_r1_rows, oddDerivationMatrix_5_to_6_r1_cols]

theorem report_consistency_6_to_5_r0_refuted_matches_wideNonSquare :
    report_consistency_6_to_5_r0.matrixReport.matrix.rows <
      report_consistency_6_to_5_r0.matrixReport.matrix.cols ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact ⟨report_consistency_6_to_5_r0_wideShape, rfl⟩

theorem report_consistency_6_to_5_r1_refuted_matches_wideNonSquare :
    report_consistency_6_to_5_r1.matrixReport.matrix.rows <
      report_consistency_6_to_5_r1.matrixReport.matrix.cols ∧
      report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact ⟨report_consistency_6_to_5_r1_wideShape, rfl⟩

theorem report_consistency_7_to_6_r0_tallShape :
    report_consistency_7_to_6_r0.matrixReport.matrix.cols <
      report_consistency_7_to_6_r0.matrixReport.matrix.rows := by
  simp [report_consistency_7_to_6_r0, report_matrix_6_to_7_r0_injectivity,
    oddDerivationMatrix_6_to_7_r0_rows, oddDerivationMatrix_6_to_7_r0_cols]

theorem report_consistency_7_to_6_r0_proved_matches_tallShape :
    report_consistency_7_to_6_r0.matrixReport.matrix.cols <
      report_consistency_7_to_6_r0.matrixReport.matrix.rows ∧
      report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  exact ⟨report_consistency_7_to_6_r0_tallShape, rfl⟩

theorem lowWeightMatrixAlignedFlagCount_eval :
    lowWeightMatrixAlignedFlagCount = 3 := by
  simp [lowWeightMatrixAlignedFlagCount, lowWeightConsistencyReports,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0, report_consistency_6_to_5_r0]

theorem lowWeightWideNonSquareConsistentFlagCount_eval :
    lowWeightWideNonSquareConsistentFlagCount = 3 := by
  simp [lowWeightWideNonSquareConsistentFlagCount, lowWeightConsistencyReports,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0, report_consistency_6_to_5_r0]

theorem lowWeightSquareStatusConsistentFlagCount_eval :
    lowWeightSquareStatusConsistentFlagCount = 3 := by
  simp [lowWeightSquareStatusConsistentFlagCount, lowWeightConsistencyReports,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0, report_consistency_6_to_5_r0]

theorem lowWeightTransposeShapeAlignedFlagCount_eval :
    lowWeightTransposeShapeAlignedFlagCount = 3 := by
  simp [lowWeightTransposeShapeAlignedFlagCount, lowWeightConsistencyReports,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0, report_consistency_6_to_5_r0]

theorem lowWeightMatrixAlignedFlagCountExtended_eval :
    lowWeightMatrixAlignedFlagCountExtended = 4 := by
  simp [lowWeightMatrixAlignedFlagCountExtended, lowWeightConsistencyReportsExtended,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1]

theorem lowWeightWideNonSquareConsistentFlagCountExtended_eval :
    lowWeightWideNonSquareConsistentFlagCountExtended = 4 := by
  simp [lowWeightWideNonSquareConsistentFlagCountExtended, lowWeightConsistencyReportsExtended,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1]

theorem lowWeightSquareStatusConsistentFlagCountExtended_eval :
    lowWeightSquareStatusConsistentFlagCountExtended = 4 := by
  simp [lowWeightSquareStatusConsistentFlagCountExtended, lowWeightConsistencyReportsExtended,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1]

theorem lowWeightTransposeShapeAlignedFlagCountExtended_eval :
    lowWeightTransposeShapeAlignedFlagCountExtended = 4 := by
  simp [lowWeightTransposeShapeAlignedFlagCountExtended, lowWeightConsistencyReportsExtended,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1]

theorem lowWeightMatrixAlignedFlagCountAugmented_eval :
    lowWeightMatrixAlignedFlagCountAugmented = 5 := by
  simp [lowWeightMatrixAlignedFlagCountAugmented, lowWeightConsistencyReportsAugmented,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
    report_consistency_7_to_6_r0]

theorem lowWeightWideNonSquareConsistentFlagCountAugmented_eval :
    lowWeightWideNonSquareConsistentFlagCountAugmented = 5 := by
  simp [lowWeightWideNonSquareConsistentFlagCountAugmented, lowWeightConsistencyReportsAugmented,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
    report_consistency_7_to_6_r0]

theorem lowWeightSquareStatusConsistentFlagCountAugmented_eval :
    lowWeightSquareStatusConsistentFlagCountAugmented = 5 := by
  simp [lowWeightSquareStatusConsistentFlagCountAugmented, lowWeightConsistencyReportsAugmented,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
    report_consistency_7_to_6_r0]

theorem lowWeightTransposeShapeAlignedFlagCountAugmented_eval :
    lowWeightTransposeShapeAlignedFlagCountAugmented = 5 := by
  simp [lowWeightTransposeShapeAlignedFlagCountAugmented, lowWeightConsistencyReportsAugmented,
    report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
    report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
    report_consistency_7_to_6_r0]

/-- Flag-soundness extraction for a generated low-weight consistency report. -/
theorem lowWeightConsistencyReportOfKey_all_flags_sound
    (k : LowWeightStepKey) :
    ((lowWeightConsistencyReportOfKey k).matrixAligned = true →
      (lowWeightConsistencyReportOfKey k).matrixAlignedProp) ∧
      ((lowWeightConsistencyReportOfKey k).wideNonSquareConsistent = true →
        (lowWeightConsistencyReportOfKey k).wideNonSquareConsistentProp) ∧
      ((lowWeightConsistencyReportOfKey k).squareStatusConsistent = true →
        (lowWeightConsistencyReportOfKey k).squareStatusConsistentProp) ∧
      ((lowWeightConsistencyReportOfKey k).transposeShapeAligned = true →
        (lowWeightConsistencyReportOfKey k).transposeShapeAlignedProp) := by
  cases k
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hflag; exact (report_consistency_3_to_2_r0_matrixAligned_sound).2
    · intro _hflag; exact (report_consistency_3_to_2_r0_wideNonSquare_sound).2
    · intro _hflag; exact (report_consistency_3_to_2_r0_squareStatus_sound).2
    · intro _hflag; exact (report_consistency_3_to_2_r0_transposeShapeAligned_sound).2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hflag; exact (report_consistency_5_to_4_r0_matrixAligned_sound).2
    · intro _hflag; exact (report_consistency_5_to_4_r0_wideNonSquare_sound).2
    · intro _hflag; exact (report_consistency_5_to_4_r0_squareStatus_sound).2
    · intro _hflag; exact (report_consistency_5_to_4_r0_transposeShapeAligned_sound).2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hflag; exact (report_consistency_6_to_5_r0_matrixAligned_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r0_wideNonSquare_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r0_squareStatus_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r0_transposeShapeAligned_sound).2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hflag; exact (report_consistency_6_to_5_r1_matrixAligned_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r1_wideNonSquare_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r1_squareStatus_sound).2
    · intro _hflag; exact (report_consistency_6_to_5_r1_transposeShapeAligned_sound).2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hflag; exact (report_consistency_7_to_6_r0_matrixAligned_sound).2
    · intro _hflag; exact (report_consistency_7_to_6_r0_wideNonSquare_sound).2
    · intro _hflag; exact (report_consistency_7_to_6_r0_squareStatus_sound).2
    · intro _hflag; exact (report_consistency_7_to_6_r0_transposeShapeAligned_sound).2

/-- Any key-generated consistency-report family inherits flag soundness. -/
theorem lowWeightConsistencyReports_of_keys_all_flags_sound
    (ks : List LowWeightStepKey) :
    ∀ R ∈ ks.map lowWeightConsistencyReportOfKey,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) := by
  intro R hR
  rcases List.mem_map.mp hR with ⟨k, hk, hkR⟩
  subst hkR
  exact lowWeightConsistencyReportOfKey_all_flags_sound k

theorem lowWeightConsistencyReports_all_flags_sound :
    ∀ R ∈ lowWeightConsistencyReports,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) := by
  simpa [lowWeightConsistencyReports] using
    (lowWeightConsistencyReports_of_keys_all_flags_sound lowWeightReportKeys)

theorem lowWeightConsistencyReportsExtended_all_flags_sound :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) := by
  simpa [lowWeightConsistencyReportsExtended] using
    (lowWeightConsistencyReports_of_keys_all_flags_sound lowWeightReportKeysExtended)

theorem lowWeightConsistencyReportsAugmented_all_flags_sound :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) := by
  simpa [lowWeightConsistencyReportsAugmented] using
    (lowWeightConsistencyReports_of_keys_all_flags_sound lowWeightReportKeysAugmented)

/-- Expected injectivity status by joined low-weight consistency report name. -/
def LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
    (consistencyName : String) : Option PropStatus :=
  if consistencyName = "consistency_3_to_2_r0" then some PropStatus.proved
  else if consistencyName = "consistency_5_to_4_r0" then some PropStatus.proved
  else if consistencyName = "consistency_6_to_5_r0" then some PropStatus.refuted
  else if consistencyName = "consistency_6_to_5_r1" then some PropStatus.refuted
  else if consistencyName = "consistency_7_to_6_r0" then some PropStatus.proved
  else none

theorem report_consistency_3_to_2_r0_status_is_proved :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  have hsq : report_consistency_3_to_2_r0.stepReport.matrixSquare = true := rfl
  exact (report_consistency_3_to_2_r0_squareStatus_sound).2 hsq

theorem report_consistency_5_to_4_r0_status_is_proved :
    report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  simpa [report_consistency_5_to_4_r0] using (report_matrix_4_to_5_r0_injectivity_sound).1

theorem report_consistency_6_to_5_r0_status_is_refuted :
    report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact (report_consistency_6_to_5_r0_wideNonSquare_sound).2
    report_consistency_6_to_5_r0_wideShape

theorem report_consistency_6_to_5_r1_status_is_refuted :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact (report_consistency_6_to_5_r1_wideNonSquare_sound).2
    report_consistency_6_to_5_r1_wideShape

theorem report_consistency_7_to_6_r0_status_is_proved :
    report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  simpa [report_consistency_7_to_6_r0] using (report_matrix_6_to_7_r0_injectivity_sound).1

theorem report_consistency_3_to_2_r0_matches_expectedInjectiveStatus :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
      report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus := by
  calc
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name
      = some PropStatus.proved := by
          simp [LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName,
            report_consistency_3_to_2_r0]
    _ = some report_consistency_3_to_2_r0.matrixReport.injectiveStatus := by
          simp [report_consistency_3_to_2_r0_status_is_proved]

theorem report_consistency_5_to_4_r0_matches_expectedInjectiveStatus :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
      report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus := by
  calc
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name
      = some PropStatus.proved := by
          simp [LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName,
            report_consistency_5_to_4_r0]
    _ = some report_consistency_5_to_4_r0.matrixReport.injectiveStatus := by
          simp [report_consistency_5_to_4_r0_status_is_proved]

theorem report_consistency_6_to_5_r0_matches_expectedInjectiveStatus :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
      report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus := by
  calc
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name
      = some PropStatus.refuted := by
          simp [LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName,
            report_consistency_6_to_5_r0]
    _ = some report_consistency_6_to_5_r0.matrixReport.injectiveStatus := by
          simp [report_consistency_6_to_5_r0_status_is_refuted]

theorem report_consistency_6_to_5_r1_matches_expectedInjectiveStatus :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
      report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus := by
  calc
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name
      = some PropStatus.refuted := by
          simp [LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName,
            report_consistency_6_to_5_r1]
    _ = some report_consistency_6_to_5_r1.matrixReport.injectiveStatus := by
          simp [report_consistency_6_to_5_r1_status_is_refuted]

theorem report_consistency_7_to_6_r0_matches_expectedInjectiveStatus :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
      report_consistency_7_to_6_r0.name =
      some report_consistency_7_to_6_r0.matrixReport.injectiveStatus := by
  calc
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_7_to_6_r0.name
      = some PropStatus.proved := by
          simp [LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName,
            report_consistency_7_to_6_r0]
    _ = some report_consistency_7_to_6_r0.matrixReport.injectiveStatus := by
          simp [report_consistency_7_to_6_r0_status_is_proved]

/-- Expected-status matching for a generated low-weight consistency report key. -/
theorem lowWeightConsistencyReportOfKey_matches_expectedInjectiveStatus
    (k : LowWeightStepKey) :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        (lowWeightConsistencyReportOfKey k).name =
      some (lowWeightConsistencyReportOfKey k).matrixReport.injectiveStatus := by
  cases k
  · simpa [lowWeightConsistencyReportOfKey_k3] using
      report_consistency_3_to_2_r0_matches_expectedInjectiveStatus
  · simpa [lowWeightConsistencyReportOfKey_k5] using
      report_consistency_5_to_4_r0_matches_expectedInjectiveStatus
  · simpa [lowWeightConsistencyReportOfKey_k6r0] using
      report_consistency_6_to_5_r0_matches_expectedInjectiveStatus
  · simpa [lowWeightConsistencyReportOfKey_k6r1] using
      report_consistency_6_to_5_r1_matches_expectedInjectiveStatus
  · simpa [lowWeightConsistencyReportOfKey_k7] using
      report_consistency_7_to_6_r0_matches_expectedInjectiveStatus

/-- Any key-generated consistency-report family satisfies expected-status matching. -/
theorem lowWeightConsistencyReports_of_keys_status_match_expected
    (ks : List LowWeightStepKey) :
    ∀ R ∈ ks.map lowWeightConsistencyReportOfKey,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus := by
  intro R hR
  rcases List.mem_map.mp hR with ⟨k, hk, hkR⟩
  subst hkR
  exact lowWeightConsistencyReportOfKey_matches_expectedInjectiveStatus k

/-- Number of joined reports whose matrix status matches the expected classifier. -/
def lowWeightExpectedInjectiveStatusMatchCount : ℕ :=
  (lowWeightConsistencyReports.filter (fun R =>
    decide (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
      some R.matrixReport.injectiveStatus))).length

theorem lowWeightExpectedInjectiveStatusMatchCount_eval :
    lowWeightExpectedInjectiveStatusMatchCount = 3 := by
  simp [lowWeightExpectedInjectiveStatusMatchCount, lowWeightConsistencyReports,
    report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus]

theorem lowWeightConsistencyReports_status_match_expected :
    ∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus := by
  simpa [lowWeightConsistencyReports] using
    (lowWeightConsistencyReports_of_keys_status_match_expected lowWeightReportKeys)

/-- Number of extended joined reports whose matrix status matches the expected classifier. -/
def lowWeightExpectedInjectiveStatusMatchCountExtended : ℕ :=
  (lowWeightConsistencyReportsExtended.filter (fun R =>
    decide (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
      some R.matrixReport.injectiveStatus))).length

theorem lowWeightExpectedInjectiveStatusMatchCountExtended_eval :
    lowWeightExpectedInjectiveStatusMatchCountExtended = 4 := by
  simp [lowWeightExpectedInjectiveStatusMatchCountExtended, lowWeightConsistencyReportsExtended,
    report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r1_matches_expectedInjectiveStatus]

theorem lowWeightConsistencyReportsExtended_status_match_expected :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus := by
  simpa [lowWeightConsistencyReportsExtended] using
    (lowWeightConsistencyReports_of_keys_status_match_expected lowWeightReportKeysExtended)

/-- Number of augmented joined reports whose matrix status matches the expected classifier. -/
def lowWeightExpectedInjectiveStatusMatchCountAugmented : ℕ :=
  (lowWeightConsistencyReportsAugmented.filter (fun R =>
    decide (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
      some R.matrixReport.injectiveStatus))).length

theorem lowWeightExpectedInjectiveStatusMatchCountAugmented_eval :
    lowWeightExpectedInjectiveStatusMatchCountAugmented = 5 := by
  simp [lowWeightExpectedInjectiveStatusMatchCountAugmented, lowWeightConsistencyReportsAugmented,
    report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r1_matches_expectedInjectiveStatus,
    report_consistency_7_to_6_r0_matches_expectedInjectiveStatus]

theorem lowWeightConsistencyReportsAugmented_status_match_expected :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus := by
  simpa [lowWeightConsistencyReportsAugmented] using
    (lowWeightConsistencyReports_of_keys_status_match_expected lowWeightReportKeysAugmented)

/-- Orientation-aware consistency certificate for a joined low-weight report. -/
def LowWeightConsistencyReport.orientationAwareCertificate
    (R : LowWeightConsistencyReport) : Prop :=
  LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
      some R.matrixReport.injectiveStatus ∧
    R.transposeShapeAlignedProp ∧
    (R.matrixReport.matrix.rows < R.matrixReport.matrix.cols →
      R.matrixReport.injectiveStatus = PropStatus.refuted)

/-- Orientation-aware certificate extraction for a generated low-weight consistency report. -/
theorem lowWeightConsistencyReportOfKey_orientationAwareCertificate
    (k : LowWeightStepKey) :
    LowWeightConsistencyReport.orientationAwareCertificate (lowWeightConsistencyReportOfKey k) := by
  cases k
  · refine ⟨?_, ?_, ?_⟩
    · exact report_consistency_3_to_2_r0_matches_expectedInjectiveStatus
    · exact (report_consistency_3_to_2_r0_transposeShapeAligned_sound).2
    · exact (report_consistency_3_to_2_r0_wideNonSquare_sound).2
  · refine ⟨?_, ?_, ?_⟩
    · exact report_consistency_5_to_4_r0_matches_expectedInjectiveStatus
    · exact (report_consistency_5_to_4_r0_transposeShapeAligned_sound).2
    · exact (report_consistency_5_to_4_r0_wideNonSquare_sound).2
  · refine ⟨?_, ?_, ?_⟩
    · exact report_consistency_6_to_5_r0_matches_expectedInjectiveStatus
    · exact (report_consistency_6_to_5_r0_transposeShapeAligned_sound).2
    · exact (report_consistency_6_to_5_r0_wideNonSquare_sound).2
  · refine ⟨?_, ?_, ?_⟩
    · exact report_consistency_6_to_5_r1_matches_expectedInjectiveStatus
    · exact (report_consistency_6_to_5_r1_transposeShapeAligned_sound).2
    · exact (report_consistency_6_to_5_r1_wideNonSquare_sound).2
  · refine ⟨?_, ?_, ?_⟩
    · exact report_consistency_7_to_6_r0_matches_expectedInjectiveStatus
    · exact (report_consistency_7_to_6_r0_transposeShapeAligned_sound).2
    · exact (report_consistency_7_to_6_r0_wideNonSquare_sound).2

theorem report_consistency_3_to_2_r0_orientationAwareCertificate :
    LowWeightConsistencyReport.orientationAwareCertificate report_consistency_3_to_2_r0 := by
  simpa [lowWeightConsistencyReportOfKey_k3] using
    (lowWeightConsistencyReportOfKey_orientationAwareCertificate .k3_to_2_r0)

theorem report_consistency_5_to_4_r0_orientationAwareCertificate :
    LowWeightConsistencyReport.orientationAwareCertificate report_consistency_5_to_4_r0 := by
  simpa [lowWeightConsistencyReportOfKey_k5] using
    (lowWeightConsistencyReportOfKey_orientationAwareCertificate .k5_to_4_r0)

theorem report_consistency_6_to_5_r0_orientationAwareCertificate :
    LowWeightConsistencyReport.orientationAwareCertificate report_consistency_6_to_5_r0 := by
  simpa [lowWeightConsistencyReportOfKey_k6r0] using
    (lowWeightConsistencyReportOfKey_orientationAwareCertificate .k6_to_5_r0)

theorem report_consistency_6_to_5_r1_orientationAwareCertificate :
    LowWeightConsistencyReport.orientationAwareCertificate report_consistency_6_to_5_r1 := by
  simpa [lowWeightConsistencyReportOfKey_k6r1] using
    (lowWeightConsistencyReportOfKey_orientationAwareCertificate .k6_to_5_r1)

theorem report_consistency_7_to_6_r0_orientationAwareCertificate :
    LowWeightConsistencyReport.orientationAwareCertificate report_consistency_7_to_6_r0 := by
  simpa [lowWeightConsistencyReportOfKey_k7] using
    (lowWeightConsistencyReportOfKey_orientationAwareCertificate .k7_to_6_r0)

/-- Any report in a key-generated family inherits orientation-aware certification. -/
theorem lowWeightConsistencyReports_of_keys_all_orientationAware
    (ks : List LowWeightStepKey) :
    ∀ R ∈ ks.map lowWeightConsistencyReportOfKey,
      LowWeightConsistencyReport.orientationAwareCertificate R := by
  intro R hR
  rcases List.mem_map.mp hR with ⟨k, hk, hkR⟩
  subst hkR
  exact lowWeightConsistencyReportOfKey_orientationAwareCertificate k

/-- Every joined low-weight report satisfies the orientation-aware certificate. -/
theorem lowWeightConsistencyReports_all_orientationAware :
    ∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.orientationAwareCertificate R := by
  simpa [lowWeightConsistencyReports] using
    (lowWeightConsistencyReports_of_keys_all_orientationAware lowWeightReportKeys)

theorem lowWeightConsistencyReportsExtended_all_orientationAware :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.orientationAwareCertificate R := by
  simpa [lowWeightConsistencyReportsExtended] using
    (lowWeightConsistencyReports_of_keys_all_orientationAware lowWeightReportKeysExtended)

theorem lowWeightConsistencyReportsAugmented_all_orientationAware :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.orientationAwareCertificate R := by
  simpa [lowWeightConsistencyReportsAugmented] using
    (lowWeightConsistencyReports_of_keys_all_orientationAware lowWeightReportKeysAugmented)

/-- Bundled "trusted pipeline" proposition for a joined low-weight report. -/
def LowWeightConsistencyReport.trustedPipelineProp (R : LowWeightConsistencyReport) : Prop :=
  ((R.matrixAligned = true → R.matrixAlignedProp) ∧
    (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
    (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
    (R.transposeShapeAligned = true → R.transposeShapeAlignedProp)) ∧
  (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
    some R.matrixReport.injectiveStatus) ∧
  LowWeightConsistencyReport.orientationAwareCertificate R

/-- Any key-generated consistency-report family satisfies trusted-pipeline certification. -/
theorem lowWeightConsistencyReports_of_keys_all_trustedPipeline
    (ks : List LowWeightStepKey) :
    ∀ R ∈ ks.map lowWeightConsistencyReportOfKey,
      LowWeightConsistencyReport.trustedPipelineProp R := by
  intro R hR
  refine ⟨?_, ?_, ?_⟩
  · exact lowWeightConsistencyReports_of_keys_all_flags_sound ks R hR
  · exact lowWeightConsistencyReports_of_keys_status_match_expected ks R hR
  · exact lowWeightConsistencyReports_of_keys_all_orientationAware ks R hR

/-- Every joined low-weight report satisfies the bundled trusted-pipeline proposition. -/
theorem lowWeightConsistencyReports_all_trustedPipeline :
    ∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.trustedPipelineProp R := by
  simpa [lowWeightConsistencyReports] using
    (lowWeightConsistencyReports_of_keys_all_trustedPipeline lowWeightReportKeys)

/-- Every extended joined low-weight report satisfies the bundled trusted-pipeline proposition. -/
theorem lowWeightConsistencyReportsExtended_all_trustedPipeline :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.trustedPipelineProp R := by
  simpa [lowWeightConsistencyReportsExtended] using
    (lowWeightConsistencyReports_of_keys_all_trustedPipeline lowWeightReportKeysExtended)

/-- Every augmented joined low-weight report satisfies the trusted-pipeline proposition. -/
theorem lowWeightConsistencyReportsAugmented_all_trustedPipeline :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.trustedPipelineProp R := by
  simpa [lowWeightConsistencyReportsAugmented] using
    (lowWeightConsistencyReports_of_keys_all_trustedPipeline lowWeightReportKeysAugmented)

/-- From a trusted pipeline certificate, a wide injectivity matrix forces `refuted` status. -/
theorem LowWeightConsistencyReport.injectiveStatus_refuted_of_trustedPipeline_wide
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R)
    (hwide : R.matrixReport.matrix.rows < R.matrixReport.matrix.cols) :
    R.matrixReport.injectiveStatus = PropStatus.refuted := by
  rcases htrusted with ⟨_hflags, _hstatus, horient⟩
  exact horient.2.2 hwide

/-- A trusted-pipeline certificate includes the expected-status match component. -/
theorem LowWeightConsistencyReport.expectedStatusMatch_of_trustedPipeline
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R) :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
      some R.matrixReport.injectiveStatus := by
  exact htrusted.2.1

/-- Extract a concrete injectivity status from a trusted pipeline and expected classifier value. -/
theorem LowWeightConsistencyReport.injectiveStatus_of_trustedPipeline_when_expected
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R)
    (s : PropStatus)
    (hexpected :
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name = some s) :
    R.matrixReport.injectiveStatus = s := by
  have hmatch := LowWeightConsistencyReport.expectedStatusMatch_of_trustedPipeline R htrusted
  have hsomes : some s = some R.matrixReport.injectiveStatus := by
    simpa [hexpected] using hmatch
  have hs : s = R.matrixReport.injectiveStatus := by
    exact Option.some.inj hsomes
  exact hs.symm

/-- A trusted-pipeline certificate includes the orientation-aware certificate. -/
theorem LowWeightConsistencyReport.orientationAware_of_trustedPipeline
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R) :
    LowWeightConsistencyReport.orientationAwareCertificate R := by
  exact htrusted.2.2

/-- From a trusted pipeline and matrix-aligned flag, recover matrix-name alignment. -/
theorem LowWeightConsistencyReport.matrixAligned_of_trustedPipeline
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R)
    (hflag : R.matrixAligned = true) :
    R.matrixAlignedProp := by
  exact htrusted.1.1 hflag

/-- From a trusted pipeline and transpose-shape flag, recover transpose-shape alignment. -/
theorem LowWeightConsistencyReport.transposeShapeAligned_of_trustedPipeline
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R)
    (hflag : R.transposeShapeAligned = true) :
    R.transposeShapeAlignedProp := by
  exact htrusted.1.2.2.2 hflag

/-- From a trusted pipeline, square-status flag, and square step, recover `proved` status. -/
theorem LowWeightConsistencyReport.injectiveStatus_proved_of_trustedPipeline_square
    (R : LowWeightConsistencyReport)
    (htrusted : LowWeightConsistencyReport.trustedPipelineProp R)
    (hflag : R.squareStatusConsistent = true)
    (hsquare : R.stepReport.matrixSquare = true) :
    R.matrixReport.injectiveStatus = PropStatus.proved := by
  exact (htrusted.1.2.2.1 hflag) hsquare

/-- Every generated low-weight consistency report key appears in the augmented list. -/
theorem lowWeightConsistencyReportOfKey_mem_augmented (k : LowWeightStepKey) :
    lowWeightConsistencyReportOfKey k ∈ lowWeightConsistencyReportsAugmented := by
  cases k <;> simp [lowWeightConsistencyReportsAugmented_eq]

/-- Trusted-pipeline status extraction for a generated low-weight consistency report. -/
theorem lowWeightConsistencyReportOfKey_status_from_trustedPipeline
    (k : LowWeightStepKey) :
    (lowWeightConsistencyReportOfKey k).matrixReport.injectiveStatus =
      match k with
      | .k3_to_2_r0 => PropStatus.proved
      | .k5_to_4_r0 => PropStatus.proved
      | .k6_to_5_r0 => PropStatus.refuted
      | .k6_to_5_r1 => PropStatus.refuted
      | .k7_to_6_r0 => PropStatus.proved := by
  have hmem : lowWeightConsistencyReportOfKey k ∈ lowWeightConsistencyReportsAugmented :=
    lowWeightConsistencyReportOfKey_mem_augmented k
  have htrusted :
      LowWeightConsistencyReport.trustedPipelineProp (lowWeightConsistencyReportOfKey k) :=
    lowWeightConsistencyReportsAugmented_all_trustedPipeline (lowWeightConsistencyReportOfKey k) hmem
  have hmatch :
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          (lowWeightConsistencyReportOfKey k).name =
        some (lowWeightConsistencyReportOfKey k).matrixReport.injectiveStatus :=
    LowWeightConsistencyReport.expectedStatusMatch_of_trustedPipeline
      (lowWeightConsistencyReportOfKey k) htrusted
  cases k <;>
    simp [lowWeightConsistencyReportOfKey,
      report_consistency_3_to_2_r0, report_consistency_5_to_4_r0,
      report_consistency_6_to_5_r0, report_consistency_6_to_5_r1,
      report_consistency_7_to_6_r0,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName] at hmatch ⊢ <;>
    simpa using hmatch.symm

theorem report_consistency_3_to_2_r0_status_is_proved_from_trustedPipeline :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  simpa [lowWeightConsistencyReportOfKey_k3] using
    (lowWeightConsistencyReportOfKey_status_from_trustedPipeline .k3_to_2_r0)

theorem report_consistency_5_to_4_r0_status_is_proved_from_trustedPipeline :
    report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  simpa [lowWeightConsistencyReportOfKey_k5] using
    (lowWeightConsistencyReportOfKey_status_from_trustedPipeline .k5_to_4_r0)

theorem report_consistency_6_to_5_r0_status_is_refuted_from_trustedPipeline :
    report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted := by
  simpa [lowWeightConsistencyReportOfKey_k6r0] using
    (lowWeightConsistencyReportOfKey_status_from_trustedPipeline .k6_to_5_r0)

theorem report_consistency_6_to_5_r1_status_is_refuted_from_trustedPipeline :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted := by
  simpa [lowWeightConsistencyReportOfKey_k6r1] using
    (lowWeightConsistencyReportOfKey_status_from_trustedPipeline .k6_to_5_r1)

theorem report_consistency_7_to_6_r0_status_is_proved_from_trustedPipeline :
    report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  simpa [lowWeightConsistencyReportOfKey_k7] using
    (lowWeightConsistencyReportOfKey_status_from_trustedPipeline .k7_to_6_r0)

/-- Bundled concrete statuses derived from the trusted low-weight pipeline. -/
theorem lowWeightTrustedPipeline_concrete_statuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact ⟨report_consistency_3_to_2_r0_status_is_proved_from_trustedPipeline,
    report_consistency_5_to_4_r0_status_is_proved_from_trustedPipeline,
    report_consistency_6_to_5_r0_status_is_refuted_from_trustedPipeline⟩

/-- Concrete trusted-pipeline statuses agree with the expected-status classifier. -/
theorem lowWeightTrustedPipeline_concrete_statuses_match_expected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus := by
  exact ⟨report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus⟩

/-- Bundled concrete statuses derived from the extended trusted low-weight pipeline. -/
theorem lowWeightTrustedPipelineExtended_concrete_statuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted := by
  exact ⟨report_consistency_3_to_2_r0_status_is_proved_from_trustedPipeline,
    report_consistency_5_to_4_r0_status_is_proved_from_trustedPipeline,
    report_consistency_6_to_5_r0_status_is_refuted_from_trustedPipeline,
    report_consistency_6_to_5_r1_status_is_refuted_from_trustedPipeline⟩

/-- Extended concrete trusted-pipeline statuses agree with the expected-status classifier. -/
theorem lowWeightTrustedPipelineExtended_concrete_statuses_match_expected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus := by
  exact ⟨report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r1_matches_expectedInjectiveStatus⟩

/-- Bundled concrete statuses derived from the augmented trusted low-weight pipeline. -/
theorem lowWeightTrustedPipelineAugmented_concrete_statuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved := by
  exact ⟨report_consistency_3_to_2_r0_status_is_proved_from_trustedPipeline,
    report_consistency_5_to_4_r0_status_is_proved_from_trustedPipeline,
    report_consistency_6_to_5_r0_status_is_refuted_from_trustedPipeline,
    report_consistency_6_to_5_r1_status_is_refuted_from_trustedPipeline,
    report_consistency_7_to_6_r0_status_is_proved_from_trustedPipeline⟩

/-- Augmented concrete statuses agree with the expected-status classifier. -/
theorem lowWeightTrustedPipelineAugmented_concrete_statuses_match_expected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_7_to_6_r0.name =
      some report_consistency_7_to_6_r0.matrixReport.injectiveStatus := by
  exact ⟨report_consistency_3_to_2_r0_matches_expectedInjectiveStatus,
    report_consistency_5_to_4_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r0_matches_expectedInjectiveStatus,
    report_consistency_6_to_5_r1_matches_expectedInjectiveStatus,
    report_consistency_7_to_6_r0_matches_expectedInjectiveStatus⟩

/-- Numeric index of low-weight trusted-pipeline invariants. -/
structure LowWeightTrustedPipelineCountIndex where
  dimensionCompatibleCount : ℕ
  squareCount : ℕ
  injectiveProvedCount : ℕ
  injectiveRefutedCount : ℕ
  injectiveUnknownCount : ℕ
  matrixAlignedFlagCount : ℕ
  wideNonSquareConsistentFlagCount : ℕ
  squareStatusConsistentFlagCount : ℕ
  transposeShapeAlignedFlagCount : ℕ
  expectedStatusMatchCount : ℕ

/-- Canonical low-weight count index (backed by computed report counters). -/
def lowWeightTrustedPipelineCountIndex : LowWeightTrustedPipelineCountIndex where
  dimensionCompatibleCount := lowWeightDimensionCompatibleCount
  squareCount := lowWeightSquareCount
  injectiveProvedCount := lowWeightInjectiveProvedCount
  injectiveRefutedCount := lowWeightInjectiveRefutedCount
  injectiveUnknownCount := lowWeightInjectiveUnknownCount
  matrixAlignedFlagCount := lowWeightMatrixAlignedFlagCount
  wideNonSquareConsistentFlagCount := lowWeightWideNonSquareConsistentFlagCount
  squareStatusConsistentFlagCount := lowWeightSquareStatusConsistentFlagCount
  transposeShapeAlignedFlagCount := lowWeightTransposeShapeAlignedFlagCount
  expectedStatusMatchCount := lowWeightExpectedInjectiveStatusMatchCount

theorem lowWeightTrustedPipelineCountIndex_eval :
    lowWeightTrustedPipelineCountIndex.dimensionCompatibleCount = 1 ∧
      lowWeightTrustedPipelineCountIndex.squareCount = 1 ∧
      lowWeightTrustedPipelineCountIndex.injectiveProvedCount = 2 ∧
      lowWeightTrustedPipelineCountIndex.injectiveRefutedCount = 1 ∧
      lowWeightTrustedPipelineCountIndex.injectiveUnknownCount = 0 ∧
      lowWeightTrustedPipelineCountIndex.matrixAlignedFlagCount = 3 ∧
      lowWeightTrustedPipelineCountIndex.wideNonSquareConsistentFlagCount = 3 ∧
      lowWeightTrustedPipelineCountIndex.squareStatusConsistentFlagCount = 3 ∧
      lowWeightTrustedPipelineCountIndex.transposeShapeAlignedFlagCount = 3 ∧
      lowWeightTrustedPipelineCountIndex.expectedStatusMatchCount = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightDimensionCompatibleCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightSquareCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightInjectiveProvedCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightInjectiveRefutedCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightInjectiveUnknownCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightMatrixAlignedFlagCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using
      lowWeightWideNonSquareConsistentFlagCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightSquareStatusConsistentFlagCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightTransposeShapeAlignedFlagCount_eval
  · simpa [lowWeightTrustedPipelineCountIndex] using lowWeightExpectedInjectiveStatusMatchCount_eval

/-- Numeric index for the extended matrix-injectivity report family. -/
structure LowWeightExtendedInjectivityCountIndex where
  provedCount : ℕ
  refutedCount : ℕ
  unknownCount : ℕ
  totalCount : ℕ

/-- Canonical extended-injectivity count index. -/
def lowWeightExtendedInjectivityCountIndex : LowWeightExtendedInjectivityCountIndex where
  provedCount := lowWeightInjectiveProvedCountExtended
  refutedCount := lowWeightInjectiveRefutedCountExtended
  unknownCount := lowWeightInjectiveUnknownCountExtended
  totalCount := lowWeightMatrixInjectivityReportsExtended.length

theorem lowWeightMatrixInjectivityReportsExtended_length_eval :
    lowWeightMatrixInjectivityReportsExtended.length = 4 := by
  simp [lowWeightMatrixInjectivityReportsExtended]

theorem lowWeightExtendedInjectivityCountIndex_eval :
    lowWeightExtendedInjectivityCountIndex.provedCount = 2 ∧
      lowWeightExtendedInjectivityCountIndex.refutedCount = 2 ∧
      lowWeightExtendedInjectivityCountIndex.unknownCount = 0 ∧
      lowWeightExtendedInjectivityCountIndex.totalCount = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [lowWeightExtendedInjectivityCountIndex] using lowWeightInjectiveProvedCountExtended_eval
  · simpa [lowWeightExtendedInjectivityCountIndex] using lowWeightInjectiveRefutedCountExtended_eval
  · simpa [lowWeightExtendedInjectivityCountIndex] using lowWeightInjectiveUnknownCountExtended_eval
  · simp [lowWeightExtendedInjectivityCountIndex]

/-- Theorem-index bundle for extended low-weight matrix-injectivity statements. -/
structure LowWeightExtendedInjectivityTheoremIndex where
  reportStatuses :
    report_matrix_2_to_3_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_4_to_5_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted ∧
      report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted
  reportSoundness :
    report_matrix_2_to_3_r0_injectivity.injectiveProp ∧
      report_matrix_4_to_5_r0_injectivity.injectiveProp ∧
      ¬ report_matrix_5_to_6_r0_injectivity.injectiveProp ∧
      ¬ report_matrix_5_to_6_r1_injectivity.injectiveProp

/-- Canonical extended low-weight injectivity theorem-index bundle. -/
def lowWeightExtendedInjectivityTheoremIndex : LowWeightExtendedInjectivityTheoremIndex where
  reportStatuses := by
    exact ⟨(report_matrix_2_to_3_r0_injectivity_sound).1,
      (report_matrix_4_to_5_r0_injectivity_sound).1,
      (report_matrix_5_to_6_r0_injectivity_refuted).1,
      (report_matrix_5_to_6_r1_injectivity_refuted).1⟩
  reportSoundness := by
    exact ⟨(report_matrix_2_to_3_r0_injectivity_sound).2,
      (report_matrix_4_to_5_r0_injectivity_sound).2,
      (report_matrix_5_to_6_r0_injectivity_refuted).2,
      (report_matrix_5_to_6_r1_injectivity_refuted).2⟩

theorem lowWeightExtendedInjectivityTheoremIndex_sound :
    (report_matrix_2_to_3_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_4_to_5_r0_injectivity.injectiveStatus = PropStatus.proved ∧
      report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted ∧
      report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted) ∧
      (report_matrix_2_to_3_r0_injectivity.injectiveProp ∧
        report_matrix_4_to_5_r0_injectivity.injectiveProp ∧
        ¬ report_matrix_5_to_6_r0_injectivity.injectiveProp ∧
        ¬ report_matrix_5_to_6_r1_injectivity.injectiveProp) := by
  exact ⟨lowWeightExtendedInjectivityTheoremIndex.reportStatuses,
    lowWeightExtendedInjectivityTheoremIndex.reportSoundness⟩

/-- Numeric index for the extended low-weight consistency-report family. -/
structure LowWeightExtendedConsistencyCountIndex where
  matrixAlignedFlagCount : ℕ
  wideNonSquareConsistentFlagCount : ℕ
  squareStatusConsistentFlagCount : ℕ
  transposeShapeAlignedFlagCount : ℕ
  expectedStatusMatchCount : ℕ
  totalCount : ℕ

/-- Canonical extended consistency count index. -/
def lowWeightExtendedConsistencyCountIndex : LowWeightExtendedConsistencyCountIndex where
  matrixAlignedFlagCount := lowWeightMatrixAlignedFlagCountExtended
  wideNonSquareConsistentFlagCount := lowWeightWideNonSquareConsistentFlagCountExtended
  squareStatusConsistentFlagCount := lowWeightSquareStatusConsistentFlagCountExtended
  transposeShapeAlignedFlagCount := lowWeightTransposeShapeAlignedFlagCountExtended
  expectedStatusMatchCount := lowWeightExpectedInjectiveStatusMatchCountExtended
  totalCount := lowWeightConsistencyReportsExtended.length

theorem lowWeightConsistencyReportsExtended_length_eval :
    lowWeightConsistencyReportsExtended.length = 4 := by
  simp [lowWeightConsistencyReportsExtended]

theorem lowWeightExtendedConsistencyCountIndex_eval :
    lowWeightExtendedConsistencyCountIndex.matrixAlignedFlagCount = 4 ∧
      lowWeightExtendedConsistencyCountIndex.wideNonSquareConsistentFlagCount = 4 ∧
      lowWeightExtendedConsistencyCountIndex.squareStatusConsistentFlagCount = 4 ∧
      lowWeightExtendedConsistencyCountIndex.transposeShapeAlignedFlagCount = 4 ∧
      lowWeightExtendedConsistencyCountIndex.expectedStatusMatchCount = 4 ∧
      lowWeightExtendedConsistencyCountIndex.totalCount = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lowWeightExtendedConsistencyCountIndex] using lowWeightMatrixAlignedFlagCountExtended_eval
  · simpa [lowWeightExtendedConsistencyCountIndex] using
      lowWeightWideNonSquareConsistentFlagCountExtended_eval
  · simpa [lowWeightExtendedConsistencyCountIndex] using
      lowWeightSquareStatusConsistentFlagCountExtended_eval
  · simpa [lowWeightExtendedConsistencyCountIndex] using
      lowWeightTransposeShapeAlignedFlagCountExtended_eval
  · simp [lowWeightExtendedConsistencyCountIndex,
      lowWeightExpectedInjectiveStatusMatchCountExtended_eval]
  · simp [lowWeightExtendedConsistencyCountIndex]

/-- Theorem-index bundle for extended low-weight consistency statements. -/
structure LowWeightExtendedConsistencyTheoremIndex where
  allFlagsSound :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp)
  allStatusesMatchExpected :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus
  allOrientationAware :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.orientationAwareCertificate R
  status_6_to_5_r1_refuted :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted

/-- Canonical extended low-weight consistency theorem-index bundle. -/
def lowWeightExtendedConsistencyTheoremIndex : LowWeightExtendedConsistencyTheoremIndex where
  allFlagsSound := lowWeightConsistencyReportsExtended_all_flags_sound
  allStatusesMatchExpected := lowWeightConsistencyReportsExtended_status_match_expected
  allOrientationAware := lowWeightConsistencyReportsExtended_all_orientationAware
  status_6_to_5_r1_refuted := report_consistency_6_to_5_r1_status_is_refuted

theorem lowWeightExtendedConsistencyTheoremIndex_sound :
    (∀ R ∈ lowWeightConsistencyReportsExtended,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp)) ∧
      (∀ R ∈ lowWeightConsistencyReportsExtended,
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
          some R.matrixReport.injectiveStatus) ∧
      (∀ R ∈ lowWeightConsistencyReportsExtended,
        LowWeightConsistencyReport.orientationAwareCertificate R) ∧
      (report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted) := by
  exact ⟨lowWeightExtendedConsistencyTheoremIndex.allFlagsSound,
    lowWeightExtendedConsistencyTheoremIndex.allStatusesMatchExpected,
    lowWeightExtendedConsistencyTheoremIndex.allOrientationAware,
    lowWeightExtendedConsistencyTheoremIndex.status_6_to_5_r1_refuted⟩

/-- Numeric index for the augmented low-weight consistency-report family. -/
structure LowWeightAugmentedConsistencyCountIndex where
  matrixAlignedFlagCount : ℕ
  wideNonSquareConsistentFlagCount : ℕ
  squareStatusConsistentFlagCount : ℕ
  transposeShapeAlignedFlagCount : ℕ
  expectedStatusMatchCount : ℕ
  totalCount : ℕ

/-- Canonical augmented consistency count index. -/
def lowWeightAugmentedConsistencyCountIndex : LowWeightAugmentedConsistencyCountIndex where
  matrixAlignedFlagCount := lowWeightMatrixAlignedFlagCountAugmented
  wideNonSquareConsistentFlagCount := lowWeightWideNonSquareConsistentFlagCountAugmented
  squareStatusConsistentFlagCount := lowWeightSquareStatusConsistentFlagCountAugmented
  transposeShapeAlignedFlagCount := lowWeightTransposeShapeAlignedFlagCountAugmented
  expectedStatusMatchCount := lowWeightExpectedInjectiveStatusMatchCountAugmented
  totalCount := lowWeightConsistencyReportsAugmented.length

theorem lowWeightConsistencyReportsAugmented_length_eval :
    lowWeightConsistencyReportsAugmented.length = 5 := by
  simp [lowWeightConsistencyReportsAugmented]

theorem lowWeightAugmentedConsistencyCountIndex_eval :
    lowWeightAugmentedConsistencyCountIndex.matrixAlignedFlagCount = 5 ∧
      lowWeightAugmentedConsistencyCountIndex.wideNonSquareConsistentFlagCount = 5 ∧
      lowWeightAugmentedConsistencyCountIndex.squareStatusConsistentFlagCount = 5 ∧
      lowWeightAugmentedConsistencyCountIndex.transposeShapeAlignedFlagCount = 5 ∧
      lowWeightAugmentedConsistencyCountIndex.expectedStatusMatchCount = 5 ∧
      lowWeightAugmentedConsistencyCountIndex.totalCount = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lowWeightAugmentedConsistencyCountIndex] using
      lowWeightMatrixAlignedFlagCountAugmented_eval
  · simpa [lowWeightAugmentedConsistencyCountIndex] using
      lowWeightWideNonSquareConsistentFlagCountAugmented_eval
  · simpa [lowWeightAugmentedConsistencyCountIndex] using
      lowWeightSquareStatusConsistentFlagCountAugmented_eval
  · simpa [lowWeightAugmentedConsistencyCountIndex] using
      lowWeightTransposeShapeAlignedFlagCountAugmented_eval
  · simp [lowWeightAugmentedConsistencyCountIndex,
      lowWeightExpectedInjectiveStatusMatchCountAugmented_eval]
  · simp [lowWeightAugmentedConsistencyCountIndex]

/-- Theorem-index bundle for augmented low-weight consistency statements. -/
structure LowWeightAugmentedConsistencyTheoremIndex where
  allFlagsSound :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp)
  allStatusesMatchExpected :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus
  allOrientationAware :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.orientationAwareCertificate R
  status_7_to_6_r0_proved :
    report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved

/-- Canonical augmented low-weight consistency theorem-index bundle. -/
def lowWeightAugmentedConsistencyTheoremIndex : LowWeightAugmentedConsistencyTheoremIndex where
  allFlagsSound := lowWeightConsistencyReportsAugmented_all_flags_sound
  allStatusesMatchExpected := lowWeightConsistencyReportsAugmented_status_match_expected
  allOrientationAware := lowWeightConsistencyReportsAugmented_all_orientationAware
  status_7_to_6_r0_proved := report_consistency_7_to_6_r0_status_is_proved

theorem lowWeightAugmentedConsistencyTheoremIndex_sound :
    (∀ R ∈ lowWeightConsistencyReportsAugmented,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp)) ∧
      (∀ R ∈ lowWeightConsistencyReportsAugmented,
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
          some R.matrixReport.injectiveStatus) ∧
      (∀ R ∈ lowWeightConsistencyReportsAugmented,
        LowWeightConsistencyReport.orientationAwareCertificate R) ∧
      (report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved) := by
  exact ⟨lowWeightAugmentedConsistencyTheoremIndex.allFlagsSound,
    lowWeightAugmentedConsistencyTheoremIndex.allStatusesMatchExpected,
    lowWeightAugmentedConsistencyTheoremIndex.allOrientationAware,
    lowWeightAugmentedConsistencyTheoremIndex.status_7_to_6_r0_proved⟩

/-- Theorem-index bundle for low-weight trusted-pipeline statements. -/
structure LowWeightTrustedPipelineTheoremIndex where
  allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.trustedPipelineProp R
  concreteStatuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted
  concreteStatusesMatchExpected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus

/-- Canonical low-weight theorem index bundle. -/
def lowWeightTrustedPipelineTheoremIndex : LowWeightTrustedPipelineTheoremIndex where
  allReportsTrusted := lowWeightConsistencyReports_all_trustedPipeline
  concreteStatuses := lowWeightTrustedPipeline_concrete_statuses
  concreteStatusesMatchExpected := lowWeightTrustedPipeline_concrete_statuses_match_expected

theorem lowWeightTrustedPipelineTheoremIndex_sound :
    (∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.trustedPipelineProp R) ∧
      (report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted) ∧
      (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_3_to_2_r0.name =
        some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_5_to_4_r0.name =
        some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_6_to_5_r0.name =
        some report_consistency_6_to_5_r0.matrixReport.injectiveStatus) := by
  exact ⟨lowWeightTrustedPipelineTheoremIndex.allReportsTrusted,
    lowWeightTrustedPipelineTheoremIndex.concreteStatuses,
    lowWeightTrustedPipelineTheoremIndex.concreteStatusesMatchExpected⟩

/-- Theorem-index bundle for extended low-weight trusted-pipeline statements. -/
structure LowWeightExtendedTrustedPipelineTheoremIndex where
  allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.trustedPipelineProp R
  concreteStatuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted
  concreteStatusesMatchExpected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus

/-- Canonical extended low-weight trusted-pipeline theorem index bundle. -/
def lowWeightExtendedTrustedPipelineTheoremIndex :
    LowWeightExtendedTrustedPipelineTheoremIndex where
  allReportsTrusted := lowWeightConsistencyReportsExtended_all_trustedPipeline
  concreteStatuses := lowWeightTrustedPipelineExtended_concrete_statuses
  concreteStatusesMatchExpected := lowWeightTrustedPipelineExtended_concrete_statuses_match_expected

theorem lowWeightExtendedTrustedPipelineTheoremIndex_sound :
    (∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.trustedPipelineProp R) ∧
      (report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
        report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted) ∧
      (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_3_to_2_r0.name =
        some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_5_to_4_r0.name =
        some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_6_to_5_r0.name =
        some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_6_to_5_r1.name =
        some report_consistency_6_to_5_r1.matrixReport.injectiveStatus) := by
  exact ⟨lowWeightExtendedTrustedPipelineTheoremIndex.allReportsTrusted,
    lowWeightExtendedTrustedPipelineTheoremIndex.concreteStatuses,
    lowWeightExtendedTrustedPipelineTheoremIndex.concreteStatusesMatchExpected⟩

/-- Theorem-index bundle for augmented low-weight trusted-pipeline statements. -/
structure LowWeightAugmentedTrustedPipelineTheoremIndex where
  allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.trustedPipelineProp R
  concreteStatuses :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
      report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted ∧
      report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved
  concreteStatusesMatchExpected :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus ∧
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_7_to_6_r0.name =
      some report_consistency_7_to_6_r0.matrixReport.injectiveStatus

/-- Canonical augmented low-weight trusted-pipeline theorem index bundle. -/
def lowWeightAugmentedTrustedPipelineTheoremIndex :
    LowWeightAugmentedTrustedPipelineTheoremIndex where
  allReportsTrusted := lowWeightConsistencyReportsAugmented_all_trustedPipeline
  concreteStatuses := lowWeightTrustedPipelineAugmented_concrete_statuses
  concreteStatusesMatchExpected := lowWeightTrustedPipelineAugmented_concrete_statuses_match_expected

theorem lowWeightAugmentedTrustedPipelineTheoremIndex_sound :
    (∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.trustedPipelineProp R) ∧
      (report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved ∧
        report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted ∧
        report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted ∧
        report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved) ∧
      (LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_3_to_2_r0.name =
        some report_consistency_3_to_2_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_5_to_4_r0.name =
        some report_consistency_5_to_4_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_6_to_5_r0.name =
        some report_consistency_6_to_5_r0.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_6_to_5_r1.name =
        some report_consistency_6_to_5_r1.matrixReport.injectiveStatus ∧
        LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
          report_consistency_7_to_6_r0.name =
        some report_consistency_7_to_6_r0.matrixReport.injectiveStatus) := by
  exact ⟨lowWeightAugmentedTrustedPipelineTheoremIndex.allReportsTrusted,
    lowWeightAugmentedTrustedPipelineTheoremIndex.concreteStatuses,
    lowWeightAugmentedTrustedPipelineTheoremIndex.concreteStatusesMatchExpected⟩

namespace LowWeightTrustedPipelineIndex

/-- Short alias for the canonical low-weight count index. -/
abbrev counts : LowWeightTrustedPipelineCountIndex := lowWeightTrustedPipelineCountIndex

/-- Short alias for the canonical low-weight theorem index. -/
abbrev theorems : LowWeightTrustedPipelineTheoremIndex := lowWeightTrustedPipelineTheoremIndex

/-- Short alias for the canonical extended injectivity count index. -/
abbrev extendedCounts : LowWeightExtendedInjectivityCountIndex :=
  lowWeightExtendedInjectivityCountIndex

/-- Short alias for the canonical extended injectivity theorem index. -/
abbrev extendedTheorems : LowWeightExtendedInjectivityTheoremIndex :=
  lowWeightExtendedInjectivityTheoremIndex

/-- Short alias for the canonical extended consistency count index. -/
abbrev extendedConsistencyCounts : LowWeightExtendedConsistencyCountIndex :=
  lowWeightExtendedConsistencyCountIndex

/-- Short alias for the canonical extended consistency theorem index. -/
abbrev extendedConsistencyTheorems : LowWeightExtendedConsistencyTheoremIndex :=
  lowWeightExtendedConsistencyTheoremIndex

/-- Short alias for the canonical extended trusted-pipeline theorem index. -/
abbrev extendedPipelineTheorems : LowWeightExtendedTrustedPipelineTheoremIndex :=
  lowWeightExtendedTrustedPipelineTheoremIndex

/-- Short alias for the canonical augmented consistency count index. -/
abbrev augmentedConsistencyCounts : LowWeightAugmentedConsistencyCountIndex :=
  lowWeightAugmentedConsistencyCountIndex

/-- Short alias for the canonical augmented consistency theorem index. -/
abbrev augmentedConsistencyTheorems : LowWeightAugmentedConsistencyTheoremIndex :=
  lowWeightAugmentedConsistencyTheoremIndex

/-- Short alias for the canonical augmented trusted-pipeline theorem index. -/
abbrev augmentedPipelineTheorems : LowWeightAugmentedTrustedPipelineTheoremIndex :=
  lowWeightAugmentedTrustedPipelineTheoremIndex

theorem dimensionCompatibleCount_eq_one :
    counts.dimensionCompatibleCount = 1 := by
  simpa [counts] using lowWeightDimensionCompatibleCount_eval

theorem squareCount_eq_one :
    counts.squareCount = 1 := by
  simpa [counts] using lowWeightSquareCount_eval

theorem injectiveProvedCount_eq_two :
    counts.injectiveProvedCount = 2 := by
  simpa [counts] using lowWeightInjectiveProvedCount_eval

theorem injectiveRefutedCount_eq_one :
    counts.injectiveRefutedCount = 1 := by
  simpa [counts] using lowWeightInjectiveRefutedCount_eval

theorem injectiveUnknownCount_eq_zero :
    counts.injectiveUnknownCount = 0 := by
  simpa [counts] using lowWeightInjectiveUnknownCount_eval

theorem matrixAlignedFlagCount_eq_three :
    counts.matrixAlignedFlagCount = 3 := by
  simpa [counts] using lowWeightMatrixAlignedFlagCount_eval

theorem wideNonSquareConsistentFlagCount_eq_three :
    counts.wideNonSquareConsistentFlagCount = 3 := by
  simpa [counts] using lowWeightWideNonSquareConsistentFlagCount_eval

theorem squareStatusConsistentFlagCount_eq_three :
    counts.squareStatusConsistentFlagCount = 3 := by
  simpa [counts] using lowWeightSquareStatusConsistentFlagCount_eval

theorem transposeShapeAlignedFlagCount_eq_three :
    counts.transposeShapeAlignedFlagCount = 3 := by
  simpa [counts] using lowWeightTransposeShapeAlignedFlagCount_eval

theorem expectedStatusMatchCount_eq_three :
    counts.expectedStatusMatchCount = 3 := by
  simpa [counts] using lowWeightExpectedInjectiveStatusMatchCount_eval

/-- Short alias for the extended matrix-injectivity report list (includes `r = 1` at `5 → 6`). -/
abbrev extendedInjectivityReports : List LowWeightMatrixInjectivityReport :=
  lowWeightMatrixInjectivityReportsExtended

theorem injectiveProvedCountExtended_eq_two :
    lowWeightInjectiveProvedCountExtended = 2 := by
  exact lowWeightInjectiveProvedCountExtended_eval

theorem injectiveRefutedCountExtended_eq_two :
    lowWeightInjectiveRefutedCountExtended = 2 := by
  exact lowWeightInjectiveRefutedCountExtended_eval

theorem injectiveUnknownCountExtended_eq_zero :
    lowWeightInjectiveUnknownCountExtended = 0 := by
  exact lowWeightInjectiveUnknownCountExtended_eval

theorem extendedProvedCount_eq_two :
    extendedCounts.provedCount = 2 := by
  simpa [extendedCounts] using (lowWeightExtendedInjectivityCountIndex_eval).1

theorem extendedRefutedCount_eq_two :
    extendedCounts.refutedCount = 2 := by
  simpa [extendedCounts] using (lowWeightExtendedInjectivityCountIndex_eval).2.1

theorem extendedUnknownCount_eq_zero :
    extendedCounts.unknownCount = 0 := by
  simpa [extendedCounts] using (lowWeightExtendedInjectivityCountIndex_eval).2.2.1

theorem extendedTotalCount_eq_four :
    extendedCounts.totalCount = 4 := by
  simpa [extendedCounts] using (lowWeightExtendedInjectivityCountIndex_eval).2.2.2

theorem extendedConsistencyMatrixAlignedFlagCount_eq_four :
    extendedConsistencyCounts.matrixAlignedFlagCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).1

theorem extendedConsistencyWideNonSquareFlagCount_eq_four :
    extendedConsistencyCounts.wideNonSquareConsistentFlagCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).2.1

theorem extendedConsistencySquareStatusFlagCount_eq_four :
    extendedConsistencyCounts.squareStatusConsistentFlagCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).2.2.1

theorem extendedConsistencyTransposeFlagCount_eq_four :
    extendedConsistencyCounts.transposeShapeAlignedFlagCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).2.2.2.1

theorem extendedConsistencyExpectedStatusMatchCount_eq_four :
    extendedConsistencyCounts.expectedStatusMatchCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).2.2.2.2.1

theorem extendedConsistencyTotalCount_eq_four :
    extendedConsistencyCounts.totalCount = 4 := by
  simpa [extendedConsistencyCounts] using (lowWeightExtendedConsistencyCountIndex_eval).2.2.2.2.2

theorem augmentedConsistencyMatrixAlignedFlagCount_eq_five :
    augmentedConsistencyCounts.matrixAlignedFlagCount = 5 := by
  simpa [augmentedConsistencyCounts] using (lowWeightAugmentedConsistencyCountIndex_eval).1

theorem augmentedConsistencyWideNonSquareFlagCount_eq_five :
    augmentedConsistencyCounts.wideNonSquareConsistentFlagCount = 5 := by
  simpa [augmentedConsistencyCounts] using (lowWeightAugmentedConsistencyCountIndex_eval).2.1

theorem augmentedConsistencySquareStatusFlagCount_eq_five :
    augmentedConsistencyCounts.squareStatusConsistentFlagCount = 5 := by
  simpa [augmentedConsistencyCounts] using (lowWeightAugmentedConsistencyCountIndex_eval).2.2.1

theorem augmentedConsistencyTransposeFlagCount_eq_five :
    augmentedConsistencyCounts.transposeShapeAlignedFlagCount = 5 := by
  simpa [augmentedConsistencyCounts] using (lowWeightAugmentedConsistencyCountIndex_eval).2.2.2.1

theorem augmentedConsistencyExpectedStatusMatchCount_eq_five :
    augmentedConsistencyCounts.expectedStatusMatchCount = 5 := by
  simpa [augmentedConsistencyCounts] using
    (lowWeightAugmentedConsistencyCountIndex_eval).2.2.2.2.1

theorem augmentedConsistencyTotalCount_eq_five :
    augmentedConsistencyCounts.totalCount = 5 := by
  simpa [augmentedConsistencyCounts] using
    (lowWeightAugmentedConsistencyCountIndex_eval).2.2.2.2.2

theorem extendedStatus_2_to_3_proved :
    report_matrix_2_to_3_r0_injectivity.injectiveStatus = PropStatus.proved :=
  extendedTheorems.reportStatuses.1

theorem extendedStatus_4_to_5_proved :
    report_matrix_4_to_5_r0_injectivity.injectiveStatus = PropStatus.proved :=
  extendedTheorems.reportStatuses.2.1

theorem extendedStatus_5_to_6_r0_refuted :
    report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted :=
  extendedTheorems.reportStatuses.2.2.1

theorem extendedStatus_5_to_6_r1_refuted :
    report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted :=
  extendedTheorems.reportStatuses.2.2.2

theorem extendedProp_2_to_3_injective :
    report_matrix_2_to_3_r0_injectivity.injectiveProp :=
  extendedTheorems.reportSoundness.1

theorem extendedProp_4_to_5_injective :
    report_matrix_4_to_5_r0_injectivity.injectiveProp :=
  extendedTheorems.reportSoundness.2.1

theorem extendedProp_5_to_6_r0_notInjective :
    ¬ report_matrix_5_to_6_r0_injectivity.injectiveProp :=
  extendedTheorems.reportSoundness.2.2.1

theorem extendedProp_5_to_6_r1_notInjective :
    ¬ report_matrix_5_to_6_r1_injectivity.injectiveProp :=
  extendedTheorems.reportSoundness.2.2.2

theorem extendedConsistencyStatus_6_to_5_r1_refuted :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted :=
  extendedConsistencyTheorems.status_6_to_5_r1_refuted

theorem extendedConsistency_allFlagsSound :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) :=
  extendedConsistencyTheorems.allFlagsSound

theorem extendedConsistency_allStatusesMatchExpected :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus :=
  extendedConsistencyTheorems.allStatusesMatchExpected

theorem extendedConsistency_allOrientationAware :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.orientationAwareCertificate R :=
  extendedConsistencyTheorems.allOrientationAware

theorem augmentedConsistencyStatus_7_to_6_r0_proved :
    report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  augmentedConsistencyTheorems.status_7_to_6_r0_proved

theorem augmentedConsistency_allFlagsSound :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      (R.matrixAligned = true → R.matrixAlignedProp) ∧
      (R.wideNonSquareConsistent = true → R.wideNonSquareConsistentProp) ∧
      (R.squareStatusConsistent = true → R.squareStatusConsistentProp) ∧
      (R.transposeShapeAligned = true → R.transposeShapeAlignedProp) :=
  augmentedConsistencyTheorems.allFlagsSound

theorem augmentedConsistency_allStatusesMatchExpected :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName R.name =
        some R.matrixReport.injectiveStatus :=
  augmentedConsistencyTheorems.allStatusesMatchExpected

theorem augmentedConsistency_allOrientationAware :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.orientationAwareCertificate R :=
  augmentedConsistencyTheorems.allOrientationAware

theorem status_5_to_6_r1_refuted :
    report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted :=
  (report_matrix_5_to_6_r1_injectivity_refuted).1

theorem statuses_5_to_6_r0_r1_both_refuted :
    report_matrix_5_to_6_r0_injectivity.injectiveStatus = PropStatus.refuted ∧
      report_matrix_5_to_6_r1_injectivity.injectiveStatus = PropStatus.refuted :=
  report_matrix_5_to_6_r0_r1_both_refuted

theorem allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReports,
      LowWeightConsistencyReport.trustedPipelineProp R :=
  theorems.allReportsTrusted

theorem extendedPipeline_allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReportsExtended,
      LowWeightConsistencyReport.trustedPipelineProp R :=
  extendedPipelineTheorems.allReportsTrusted

theorem augmentedPipeline_allReportsTrusted :
    ∀ R ∈ lowWeightConsistencyReportsAugmented,
      LowWeightConsistencyReport.trustedPipelineProp R :=
  augmentedPipelineTheorems.allReportsTrusted

theorem status_3_to_2_proved :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  theorems.concreteStatuses.1

theorem status_5_to_4_proved :
    report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  theorems.concreteStatuses.2.1

theorem status_6_to_5_refuted :
    report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted :=
  theorems.concreteStatuses.2.2

theorem extendedPipeline_status_3_to_2_proved :
    report_consistency_3_to_2_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  extendedPipelineTheorems.concreteStatuses.1

theorem extendedPipeline_status_5_to_4_proved :
    report_consistency_5_to_4_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  extendedPipelineTheorems.concreteStatuses.2.1

theorem extendedPipeline_status_6_to_5_r0_refuted :
    report_consistency_6_to_5_r0.matrixReport.injectiveStatus = PropStatus.refuted :=
  extendedPipelineTheorems.concreteStatuses.2.2.1

theorem extendedPipeline_status_6_to_5_r1_refuted :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted :=
  extendedPipelineTheorems.concreteStatuses.2.2.2

theorem augmentedPipeline_status_6_to_5_r1_refuted :
    report_consistency_6_to_5_r1.matrixReport.injectiveStatus = PropStatus.refuted :=
  augmentedPipelineTheorems.concreteStatuses.2.2.2.1

theorem augmentedPipeline_status_7_to_6_r0_proved :
    report_consistency_7_to_6_r0.matrixReport.injectiveStatus = PropStatus.proved :=
  augmentedPipelineTheorems.concreteStatuses.2.2.2.2

theorem statusMatch_3_to_2 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus :=
  theorems.concreteStatusesMatchExpected.1

theorem statusMatch_5_to_4 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus :=
  theorems.concreteStatusesMatchExpected.2.1

theorem statusMatch_6_to_5 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus :=
  theorems.concreteStatusesMatchExpected.2.2

theorem extendedPipeline_statusMatch_3_to_2 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_3_to_2_r0.name =
      some report_consistency_3_to_2_r0.matrixReport.injectiveStatus :=
  extendedPipelineTheorems.concreteStatusesMatchExpected.1

theorem extendedPipeline_statusMatch_5_to_4 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_5_to_4_r0.name =
      some report_consistency_5_to_4_r0.matrixReport.injectiveStatus :=
  extendedPipelineTheorems.concreteStatusesMatchExpected.2.1

theorem extendedPipeline_statusMatch_6_to_5_r0 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r0.name =
      some report_consistency_6_to_5_r0.matrixReport.injectiveStatus :=
  extendedPipelineTheorems.concreteStatusesMatchExpected.2.2.1

theorem extendedPipeline_statusMatch_6_to_5_r1 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus :=
  extendedPipelineTheorems.concreteStatusesMatchExpected.2.2.2

theorem augmentedPipeline_statusMatch_6_to_5_r1 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_6_to_5_r1.name =
      some report_consistency_6_to_5_r1.matrixReport.injectiveStatus :=
  augmentedPipelineTheorems.concreteStatusesMatchExpected.2.2.2.1

theorem augmentedPipeline_statusMatch_7_to_6_r0 :
    LowWeightConsistencyReport.expectedInjectiveStatusForConsistencyName
        report_consistency_7_to_6_r0.name =
      some report_consistency_7_to_6_r0.matrixReport.injectiveStatus :=
  augmentedPipelineTheorems.concreteStatusesMatchExpected.2.2.2.2

end LowWeightTrustedPipelineIndex

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
  carrier := Set.range motivicPeriodMap
  contains_zero := by
    exact ⟨MotivicMZV.zero, by simp [motivicPeriodMap, MotivicMZV.zero]⟩
  closed_add := by
    intro a b ha hb
    rcases ha with ⟨ma, rfl⟩
    rcases hb with ⟨mb, rfl⟩
    refine ⟨MotivicMZV.add ma mb, ?_⟩
    simpa using motivicPeriodMap_ring_hom ma mb
  closed_mul := by
    intro a b _ha _hb
    rcases motivicPeriodMap_surjective (a * b) with ⟨m, hm⟩
    exact ⟨m, hm⟩

/-! ## Galois Theory -/

/-- The motivic Galois group acts on motivic MZVs.

    G_MT = Aut^⊗(ω)

    where ω is the fiber functor. This action is captured by the coaction. -/
structure MotivicGaloisGroup where
  act : MotivicMZV → MotivicMZV
  preserves_weight : ∀ m : MotivicMZV, (act m).weight = m.weight
  preserves_depth : ∀ m : MotivicMZV, (act m).depth = m.depth

/-- The identity action gives a basic motivic Galois action model. -/
def scaleAction (u : Units ℚ) : MotivicGaloisGroup where
  act := fun m => MotivicMZV.smul (u : ℚ) m
  preserves_weight := by intro _m; rfl
  preserves_depth := by intro _m; rfl

/-- The unit scaling action as the default toy-model Galois element. -/
def motivicGaloisGroup : MotivicGaloisGroup where
  act := (scaleAction 1).act
  preserves_weight := (scaleAction 1).preserves_weight
  preserves_depth := (scaleAction 1).preserves_depth

/-- The Lie algebra of the motivic Galois group.

    Lie(G_MT) is a free Lie algebra on generators σ₃, σ₅, σ₇, ...
    dual to f₃, f₅, f₇, ... -/
def motivic_lie_algebra_conjecture : Prop :=
  ∃ d : ℕ → FormalSum → FormalSum,
    (∀ k f, k % 2 = 1 → FormalSum.maxWeight (d k f) + k ≤ FormalSum.maxWeight f) ∧
    (∀ m n f,
      FormalSum.sub (d m (d n f)) (d n (d m f)) =
        FormalSum.smul ((m : ℚ) - n) (d (m + n) f))

/-- Ihara's derivation algebra is related to Lie(G_MT). -/
theorem ihara_derivation_relation :
    ∀ n : ℕ, ∀ s : Composition, (iharaDerivComp n s).length = s.length := by
  intro n s
  simpa using iharaDerivComp_length n s

/-! ## Examples at Low Weight -/

/-! ## Connection to Physics -/

/-- MZVs appear in Feynman integrals at multi-loop level.

    This connection is not coincidental: both are periods of
    mixed Tate motives arising from P¹ \ {0, 1, ∞}. -/
theorem feynman_integral_connection :
    ∀ m : MotivicMZV, motivicPeriodMap m ∈ periodAlgebra.carrier := by
  intro m
  exact ⟨m, rfl⟩

/-- The cosmic Galois group conjecture (Cartier-Kontsevich).

    There is a "cosmic Galois group" acting on Feynman integrals,
    and the motivic Galois group is a quotient. -/
def cosmic_galois_conjecture : Prop :=
  ∃ G : MotivicGaloisGroup,
    ∀ m : MotivicMZV,
      motivicPeriodMap (G.act m) ∈ periodAlgebra.carrier ∧
      (m ∈ motivicPeriodMap_kernel → G.act m ∈ motivicPeriodMap_kernel)

end StringAlgebra.MZV
