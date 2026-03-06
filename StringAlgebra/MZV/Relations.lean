/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.DoubleShuffle

/-!
# Explicit MZV Relations

This file collects explicit relations among multiple zeta values,
providing concrete instances of the general double shuffle framework.

## Main definitions

* `SumFormula` - The sum formula Σ ζ(a,{1}ᵇ) = ζ(a+b)
* `DualityRelation` - Duality relating ζ(s) and ζ(s†)
* `DerivationRelation` - Ihara's derivation relations
* `Ohno` - Ohno's relations generalizing sum and duality

## Mathematical Background

### The Sum Formula

For integers a ≥ 2 and b ≥ 0:
  Σ_{i=0}^{b} ζ(a+i, {1}^{b-i}) = ζ(a+b)

where {1}^k means k copies of 1.

### Duality

The duality involution on compositions:
  (s₁, ..., sₖ)† = (tₖ, ..., t₁)

where t is obtained by reading s in "01-notation" backwards and swapping 0↔1.

Theorem: ζ(s) = ζ(s†) for admissible s.

### Ohno's Relations

Generalize both sum formula and duality. For a composition s and
non-negative integers eᵢ:
  Σ ζ(s₁+e₁, ..., sₖ+eₖ) = Σ ζ(t₁+f₁, ..., tₘ+fₘ)

where the sums run over partitions of a fixed total.

### Derivation Relations

Ihara's derivations D_n satisfy Lie algebra relations and
act on MZVs giving linear relations.

## References

* Hoffman - "Multiple harmonic series"
* Ohno - "A generalization of the duality and sum formulas"
* Ihara, Kaneko, Zagier - "Derivation and double shuffle relations"
* Zagier - "Values of zeta functions and their applications"
-/

namespace StringAlgebra.MZV

open List

/-! ## Helper Definitions -/

/-- Create a composition of repeated 1s: {1}^n = (1, 1, ..., 1) -/
def ones (n : ℕ) : Composition :=
  List.replicate n ⟨1, by omega⟩

/-- The depth of ones n is n -/
theorem ones_depth (n : ℕ) : (ones n).depth = n := by
  simp [ones, Composition.depth]

/-- The weight of ones n is n -/
theorem ones_weight (n : ℕ) : (ones n).weight = n := by
  simp only [ones, Composition.weight]
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.map_cons, List.sum_cons, ih]
      simp only [PNat.mk_coe, Nat.add_comm]

/-! ## The Sum Formula -/

/-- Canonical depth-varying terms in the weight-`n` sum formula:
    `(k,1,...,1)` for `k = 2, ..., n-1`.

    For n ≥ 3, `List.range (n - 2)` gives i ∈ [0, n-3],
    so k = i + 2 ∈ [2, n-1] as required. -/
def sumFormulaTerms (n : ℕ) : List Composition :=
  (List.range (n - 2)).map fun i =>
    let k := i + 2
    (⟨k, by omega⟩ :: ones (n - k))

/-- The sum formula states:
    Σ_{k=2}^{n-1} ζ(k, {1}^{n-k}) = ζ(n)

    This is a fundamental linear relation among MZVs.
    Example at n=3: ζ(2,1) = ζ(3) -/
def sum_formula_general (ζ : Composition → ℚ) (n : ℕ) : Prop :=
  ∀ hn : n ≥ 3,
    List.sum ((sumFormulaTerms n).map ζ) = ζ [⟨n, by omega⟩]

/-- Sum formula at weight 3: ζ(2,1) = ζ(3) -/
def sum_formula_weight3 (ζ : Composition → ℚ) : Prop :=
  ζ zeta21 = ζ zeta3

/-- Sum formula at weight 4: ζ(2,1,1) + ζ(3,1) = ζ(4) -/
def sum_formula_weight4 (ζ : Composition → ℚ) : Prop :=
  let zeta211 : Composition := [⟨2, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]
  let zeta31 : Composition := [⟨3, by omega⟩, ⟨1, by omega⟩]
  let zeta4 : Composition := [⟨4, by omega⟩]
  ζ zeta211 + ζ zeta31 = ζ zeta4

/-- Sum formula at weight 5: ζ(2,1,1,1) + ζ(3,1,1) + ζ(4,1) = ζ(5) -/
def sum_formula_weight5 (ζ : Composition → ℚ) : Prop :=
  let zeta2111 : Composition := [⟨2, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]
  let zeta311 : Composition := [⟨3, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]
  let zeta41 : Composition := [⟨4, by omega⟩, ⟨1, by omega⟩]
  let zeta5 : Composition := [⟨5, by omega⟩]
  ζ zeta2111 + ζ zeta311 + ζ zeta41 = ζ zeta5

/-! ## Duality -/

/-- Convert composition to 01-word for duality computation.

    (s₁, s₂, ..., sₖ) ↦ 0^{s₁-1}10^{s₂-1}1...0^{sₖ-1}1 -/
def compTo01 (s : Composition) : List Bool :=
  s.flatMap fun n =>
    List.replicate (n.val - 1) false ++ [true]

/-- Convert 01-word back to composition.

    Reads runs of 0s followed by 1, counting 0s + 1 for each part.
    Returns none if the word doesn't end with true. -/
def comp01To (w : List Bool) : Option Composition :=
  if h : w = [] then some []
  else if w.getLast (by simp [h]) ≠ true then none
  else some (go w 1 (by omega))
where
  go : List Bool → (acc : ℕ) → acc > 0 → Composition
  | [], _, _ => []
  | false :: rest, acc, h => go rest (acc + 1) (by omega)
  | true :: rest, acc, h => ⟨acc, h⟩ :: go rest 1 (by omega)

/-- The dual composition s† is obtained by:
    1. Convert to 01-word
    2. Reverse
    3. Swap 0↔1
    4. Convert back -/
def dualComp (s : Composition) : Option Composition :=
  let w := compTo01 s
  let w' := w.reverse.map (!·)
  comp01To w'

/-- The duality relation: ζ(s) = ζ(s†) -/
def duality_relation (ζ : Composition → ℚ) (s : Composition) (_hs : Composition.isAdmissible s) : Prop :=
  ∀ t, dualComp s = some t → ζ s = ζ t

/-- Duality at ζ(2,1) = ζ(3) can be verified by computing dualComp -/
def zeta21_eq_zeta3_via_duality (ζ : Composition → ℚ) : Prop :=
  duality_relation ζ zeta21 (by
    unfold Composition.isAdmissible zeta21
    simp) ∧
  ζ zeta21 = ζ zeta3

/-! ## Ohno's Relations -/

/-- All ways to distribute a total `n` among `k` non-negative parts.

    `distributions k n` returns all lists `e` of length `k` with `Σeᵢ = n`. -/
def distributions : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | k + 1, n =>
    (List.range (n + 1)).flatMap fun eᵢ =>
      (distributions k (n - eᵢ)).map (eᵢ :: ·)

/-- Add a list of heights to a composition element-wise.

    Given `s = (s₁, ..., sₖ)` and `e = (e₁, ..., eₖ)`,
    returns `(s₁+e₁, ..., sₖ+eₖ)`. -/
def addHeights (s : Composition) (e : List ℕ) : Composition :=
  (s.zip e).map fun (p, eᵢ) => ⟨p.val + eᵢ, Nat.add_pos_left p.pos eᵢ⟩

/-- The Ohno terms: all compositions obtained by distributing total
    height `n` among the parts of `s`. -/
def ohnoTerms (s : Composition) (n : ℕ) : List Composition :=
  (distributions s.length n).map (addHeights s)

/-- Ohno's relation generalizes the sum formula and duality.

    For an admissible composition `s` and its dual `s†`, and any
    non-negative integer `n`:

    Σ_{Σeᵢ=n} ζ(s₁+e₁,...,sₖ+eₖ) = Σ_{Σfⱼ=n} ζ(s†₁+f₁,...,s†ₗ+fₗ)

    The sums run over all ways to distribute total height `n` among
    the parts of `s` (resp. `s†`). -/
def ohno_relation_conjecture
    (ζ : Composition → ℚ)
    (s : Composition)
    (_hs : Composition.isAdmissible s)
    (n : ℕ) : Prop :=
  ∀ sDual : Composition, dualComp s = some sDual →
    List.sum ((ohnoTerms s n).map ζ) = List.sum ((ohnoTerms sDual n).map ζ)

/-! ## Derivation Relations -/

/-- Modify the i-th element of a composition by adding n to it. -/
def addAtPosition (s : Composition) (i : ℕ) (n : ℕ) : Composition :=
  s.mapIdx fun j p => if j = i then ⟨p.val + n, Nat.add_pos_left p.pos n⟩ else p

/-- Ihara's derivation ∂_n acts on compositions.

    ∂_n(s₁, ..., sₖ) = Σᵢ (s₁, ..., sᵢ + n, ..., sₖ)

    For each position i, we create a term where sᵢ is replaced by sᵢ + n. -/
def iharaDeriv (n : ℕ) (s : Composition) : FormalSum :=
  (List.range s.length).map fun i => (1, addAtPosition s i n)

/-- The derivation ∂₃ acting on ζ(2) -/
def deriv3_zeta2 : Prop :=
  iharaDeriv 3 zeta2 = [(1, [⟨5, by omega⟩])]

/-- Derivations satisfy [∂_m, ∂_n] = (m-n)∂_{m+n} (up to normalization) -/
def derivation_commutator_conjecture (m n : ℕ) : Prop :=
  ∀ f : FormalSum,
    FormalSum.sub
      (iharaDerivation m (iharaDerivation n f))
      (iharaDerivation n (iharaDerivation m f)) =
    FormalSum.smul ((m : ℚ) - n) (iharaDerivation (m + n) f)

/-! ## The Hoffman Basis -/

/-- A composition is Hoffman if all parts are in {2, 3}.

    Hoffman conjectured (and Brown proved) that Hoffman compositions
    form a basis for the ℚ-vector space of MZVs. -/
def isHoffman (s : Composition) : Prop :=
  ∀ p ∈ s, p.val = 2 ∨ p.val = 3

/-- Count Hoffman compositions of weight n -/
def hoffmanCount : ℕ → ℕ
  | 0 => 1  -- Empty composition
  | 1 => 0
  | 2 => 1  -- Just (2)
  | 3 => 1  -- Just (3)
  | n + 4 => hoffmanCount (n + 2) + hoffmanCount (n + 1)

/-- Hoffman compositions exist at every weight ≥ 2.

    NOTE: This is a combinatorial fact (compositions using only 2s and 3s exist
    at every weight ≥ 2), NOT Brown's theorem about spanning. Brown's actual
    theorem — that Hoffman MZVs form a basis — requires motivic machinery. -/
theorem hoffman_composition_exists_alt :
    ∀ w : ℕ, w ≥ 2 → ∃ s : Composition, s.weight = w ∧ isHoffman s := by
  intro w hw
  rcases hoffman_composition_exists w hw with ⟨s, hs, hsw⟩
  refine ⟨s, hsw, ?_⟩
  intro p hp
  exact hs p hp

/-! ## The Broadhurst-Kreimer Conjecture -/

/-- Broadhurst-Kreimer conjecture predicts the number of
    irreducible MZVs at each weight. -/
def bkDimension : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => bkDimension (n + 1) + bkDimension n

/-! ## Small Weight Relations -/

/-! ## Euler's Relation -/

/-- Euler proved: ζ(2n) = (-1)^{n+1} B_{2n} (2π)^{2n} / (2(2n)!)

    where B_{2n} are Bernoulli numbers. So all even zeta values
    are rational multiples of π^{2n}. -/
def euler_even_zeta_conjecture (ζ : Composition → ℚ) (n : ℕ) : Prop :=
  ∀ hn : n ≥ 1,
    ∃ q : ℚ,
      ζ [⟨2 * n, by omega⟩] = q * (ζ [⟨2, by omega⟩]) ^ n

/-- Corollary: ζ(2) = π²/6, ζ(4) = π⁴/90, ζ(6) = π⁶/945, ... -/
def zeta_even_values_conjecture (ζ : Composition → ℚ) : Prop :=
  euler_even_zeta_conjecture ζ 1 ∧
  euler_even_zeta_conjecture ζ 2 ∧
  euler_even_zeta_conjecture ζ 3

/-- Algebraic independence of odd zeta values over ℚ(π).

    Conjecture: ζ(3), ζ(5), ζ(7), ... are algebraically independent over ℚ.
    (Combined with Euler's theorem on even zeta values, this is equivalent to
    algebraic independence over ℚ(π).)

    Formalized as: no non-trivial polynomial relation with rational coefficients
    holds among finitely many odd zeta values. An abstract evaluation map
    `oddζ : ℕ → ℚ` represents ζ(2k+1) for k ≥ 1.

    NOTE: Even the irrationality of ζ(5) is unknown. Apéry proved ζ(3) ∉ ℚ,
    and Rivoal-Ball proved infinitely many ζ(2k+1) are irrational. -/
def odd_zeta_independence_conjecture (oddζ : ℕ → ℚ) : Prop :=
  -- For any non-constant polynomial P in variables {x_k : k ≥ 1} with
  -- ℚ-coefficients, P(ζ(3), ζ(5), ζ(7), ...) ≠ 0.
  --
  -- We express this as: no finite ℚ-linear combination of distinct
  -- monomial evaluations vanishes. A monomial is a finite multiset
  -- of variable indices. The evaluation of monomial {i₁,...,iₖ} at oddζ
  -- is oddζ(i₁) * ... * oddζ(iₖ).
  --
  -- For a proper formalization, use Mathlib's MvPolynomial.
  -- The version below captures the essential content: no non-trivial
  -- ℚ-polynomial relation holds among the values oddζ(k).
  ∀ (terms : List (ℚ × List ℕ)),
    -- non-trivial: at least one non-zero coefficient
    (∃ c ms, (c, ms) ∈ terms ∧ c ≠ 0) →
    -- distinct monomials (no duplicate exponent lists)
    terms.Pairwise (fun a b => a.2 ≠ b.2) →
    -- the polynomial evaluates to non-zero
    (terms.map fun (c, ms) => c * (ms.map oddζ).prod).sum ≠ 0

end StringAlgebra.MZV
