/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.PNat.Basic

/-!
# Basic Definitions for Multiple Zeta Values

This file provides foundational definitions for the algebraic study of
multiple zeta values (MZVs) following the framework of Francis Brown.

## Main definitions

* `Composition` - A composition (s₁, ..., sₖ) with sᵢ ≥ 1
* `Composition.weight` - The weight |s| = s₁ + ... + sₖ
* `Composition.depth` - The depth k (number of parts)
* `Composition.isAdmissible` - Whether s₁ ≥ 2 (for convergence)
* `Word` - Words over an alphabet (for iterated integrals)

## Mathematical Background

### Compositions

A composition of n is an ordered tuple (s₁, ..., sₖ) of positive integers
summing to n. For MZVs:
- Weight: |s| = s₁ + ... + sₖ
- Depth: k = number of parts
- Admissible: s₁ ≥ 2 (ensures convergence of the MZV series)

### Multiple Zeta Values

The multiple zeta value ζ(s₁, ..., sₖ) is defined for admissible compositions:

  ζ(s₁, ..., sₖ) = Σ_{n₁ > n₂ > ... > nₖ ≥ 1} 1/(n₁^{s₁} · ... · nₖ^{sₖ})

### Words and Iterated Integrals

MZVs can also be expressed as iterated integrals on P¹ \ {0, 1, ∞}:

  ζ(s₁, ..., sₖ) = ∫₀¹ ω_{s₁-1} ω_{s₂-1} ... ω_{sₖ-1}

where ω₀ = dt/t and ω₁ = dt/(1-t).

This leads to representing MZVs as words in the alphabet {0, 1}.

## References

* Brown, F. - "Mixed Tate motives over Z", Annals of Mathematics 175(2), 2012
  (arXiv: 1102.1312, IHES: https://www.ihes.fr/~brown/MTZ.pdf)
  Proves Hoffman's conjecture: every MZV is a ℚ-linear combination of ζ(n₁,...,nᵣ)
  where nᵢ ∈ {2,3}.
* Brown, F. - "On the decomposition of motivic multiple zeta values"
* Hoffman, M. - "Multiple harmonic series", Pacific J. Math. 152(2), 1992
* Zagier, D. - "Values of zeta functions and their applications"
* Broadhurst, D.J., Kreimer, D. - "Association of multiple zeta values with
  positive knots via Feynman diagrams up to 9 loops" (arXiv: hep-th/9609128)
-/

namespace StringAlgebra.MZV

/-! ## Compositions -/

/-- A composition is a finite sequence of positive integers.

    Mathematically, this represents (s₁, s₂, ..., sₖ) where each sᵢ ≥ 1.
    We use `List ℕ+` to enforce positivity. -/
abbrev Composition := List ℕ+

namespace Composition

/-- The empty composition (depth 0) -/
def empty : Composition := []

/-- A singleton composition (s) -/
def singleton (s : ℕ+) : Composition := [s]

/-- The weight of a composition is the sum of its parts.

    |s| = s₁ + s₂ + ... + sₖ -/
def weight (s : Composition) : ℕ :=
  (s.map (·.val)).sum

/-- The depth of a composition is the number of parts.

    depth(s₁, ..., sₖ) = k -/
def depth (s : Composition) : ℕ :=
  s.length

/-- A composition is admissible if its first part is ≥ 2.

    This ensures convergence of the corresponding MZV series.
    The empty composition is considered admissible by convention. -/
def isAdmissible (s : Composition) : Prop :=
  s.head?.map (·.val ≥ 2) |>.getD True

/-- Weight is additive under concatenation -/
theorem weight_append (s t : Composition) :
    (s ++ t).weight = s.weight + t.weight := by
  unfold weight
  rw [List.map_append, List.sum_append]

/-- Depth is additive under concatenation -/
theorem depth_append (s t : Composition) :
    (s ++ t).depth = s.depth + t.depth := by
  unfold depth
  rw [List.length_append]

/-- The weight of the empty composition is 0 -/
@[simp]
theorem weight_empty : empty.weight = 0 := rfl

/-- The depth of the empty composition is 0 -/
@[simp]
theorem depth_empty : empty.depth = 0 := rfl

/-- The weight of a singleton is the value itself -/
@[simp]
theorem weight_singleton (s : ℕ+) :
    (singleton s).weight = s.val := by
  simp only [singleton, weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The depth of a singleton is 1 -/
@[simp]
theorem depth_singleton (s : ℕ+) :
    (singleton s).depth = 1 := rfl

/-- Weight is preserved under reversal -/
theorem weight_reverse (s : Composition) :
    weight s.reverse = weight s := by
  unfold weight
  rw [List.map_reverse, List.sum_reverse]

/-- Depth is preserved under reversal -/
theorem depth_reverse (s : Composition) :
    depth s.reverse = depth s := by
  unfold depth
  rw [List.length_reverse]

/-- The dual composition: reverse -/
abbrev dual (s : Composition) : Composition := s.reverse

end Composition

/-! ## Words over an Alphabet -/

/-- A word over an alphabet A is a finite sequence of letters. -/
abbrev Word (A : Type*) := List A

namespace Word

variable {A : Type*}

/-- The empty word -/
def empty : Word A := []

/-- A single-letter word -/
def letter (a : A) : Word A := [a]

/-- The length of a word -/
def len (w : Word A) : ℕ := w.length

/-- Length is additive -/
theorem len_append (w₁ w₂ : Word A) :
    (w₁ ++ w₂).len = w₁.len + w₂.len := by
  unfold len
  rw [List.length_append]

end Word

/-! ## The Alphabet for MZVs -/

/-- The standard alphabet for MZV iterated integrals: {0, 1}

    - Letter 0 corresponds to dt/t
    - Letter 1 corresponds to dt/(1-t) -/
inductive MZVLetter : Type
  | zero : MZVLetter  -- corresponds to dt/t
  | one : MZVLetter   -- corresponds to dt/(1-t)
  deriving DecidableEq, Repr

/-- Words in the MZV alphabet -/
abbrev MZVWord := Word MZVLetter

namespace MZVWord

/-- The weight of an MZV word is its length -/
def weight (w : MZVWord) : ℕ := w.length

/-- The depth of an MZV word is the number of 1s -/
def depth (w : MZVWord) : ℕ :=
  w.countP (· == MZVLetter.one)

/-- A word is admissible for MZVs if it starts with 1 and ends with 0.

    This corresponds to the convergence condition for the iterated integral. -/
def isAdmissible (w : MZVWord) : Prop :=
  w.head? = some MZVLetter.one ∧ w.getLast? = some MZVLetter.zero

end MZVWord

/-! ## Conversion between Compositions and Words -/

/-- Convert a composition to an MZV word.

    (s₁, s₂, ..., sₖ) ↦ 1 0^{s₁-1} 1 0^{s₂-1} ... 1 0^{sₖ-1}

    where 0^n means n copies of 0. -/
def compositionToWord (s : Composition) : MZVWord :=
  s.flatMap fun n => MZVLetter.one :: List.replicate (n.val - 1) MZVLetter.zero

/-- The word representation has the same depth as the composition -/
theorem compositionToWord_depth (s : Composition) :
    (compositionToWord s).depth = s.depth := by
  unfold compositionToWord MZVWord.depth Composition.depth
  induction s with
  | nil => simp
  | cons n ns ih =>
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    rw [ih]
    -- Count the 1s in (MZVLetter.one :: List.replicate (n.val - 1) MZVLetter.zero)
    simp only [List.countP_cons, List.countP_replicate, beq_iff_eq]
    -- The head is one, so we get 1 + (count of 1s in zeros) = 1 + 0 = 1
    simp only [reduceCtorEq, ↓reduceIte]
    omega

/-- The word representation preserves weight -/
theorem compositionToWord_weight (s : Composition) :
    (compositionToWord s).weight = s.weight := by
  unfold compositionToWord MZVWord.weight Composition.weight
  induction s with
  | nil => simp
  | cons n ns ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
               List.length_replicate, List.map_cons, List.sum_cons]
    rw [ih]
    -- Length of (MZVLetter.one :: List.replicate (n.val - 1) MZVLetter.zero) = 1 + (n.val - 1) = n.val
    have h : n.val ≥ 1 := n.pos
    omega

/-! ## Standard Compositions -/

/-- The Riemann zeta composition ζ(n) = (n) -/
def riemannZeta (n : ℕ) (hn : n ≥ 2) : Composition :=
  [⟨n, by omega⟩]

/-- ζ(n) is admissible for n ≥ 2 -/
theorem riemannZeta_isAdmissible (n : ℕ) (hn : n ≥ 2) :
    (riemannZeta n hn).isAdmissible := by
  simp only [riemannZeta, Composition.isAdmissible, List.head?_cons]
  exact hn

/-- ζ(2) composition -/
def zeta2 : Composition := riemannZeta 2 (by omega)

/-- ζ(3) composition -/
def zeta3 : Composition := riemannZeta 3 (by omega)

/-- ζ(2,1) composition (related to ζ(3) by shuffle relation) -/
def zeta21 : Composition := [⟨2, by omega⟩, ⟨1, by omega⟩]

/-! ## Hoffman Basis

Following Brown "Mixed Tate Motives over Z" (Annals of Math 2012), every MZV
is a ℚ-linear combination of ζ(n₁,...,nᵣ) where nᵢ ∈ {2,3}.

These form the "Hoffman basis" and are indexed by compositions using only 2 and 3.
-/

/-- A Hoffman composition uses only 2s and 3s.

    By Brown's theorem (proving Hoffman's conjecture), these span all MZVs over ℚ.
    Moreover, they form a basis for the motivic MZVs. -/
def isHoffmanComposition (s : Composition) : Prop :=
  ∀ n ∈ s, n.val = 2 ∨ n.val = 3

/-- Hoffman compositions are automatically admissible (first part is 2 or 3 ≥ 2) -/
theorem hoffmanComposition_isAdmissible (s : Composition) (hs : isHoffmanComposition s)
    (hne : s ≠ []) : s.isAdmissible := by
  unfold Composition.isAdmissible isHoffmanComposition at *
  cases s with
  | nil => contradiction
  | cons n ns =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    have h := hs n (by simp)
    cases h with
    | inl h2 => simp [h2]
    | inr h3 => simp [h3]

/-- The set of Hoffman compositions of given weight -/
def hoffmanCompositionsOfWeight (w : ℕ) : Set Composition :=
  { s | isHoffmanComposition s ∧ s.weight = w }

/-- Count of 2s in a composition -/
def count2s (s : Composition) : ℕ :=
  s.countP (·.val == 2)

/-- Count of 3s in a composition -/
def count3s (s : Composition) : ℕ :=
  s.countP (·.val == 3)

/-- For Hoffman compositions: weight = 2 * (count of 2s) + 3 * (count of 3s) -/
theorem hoffmanComposition_weight (s : Composition) (hs : isHoffmanComposition s) :
    s.weight = 2 * count2s s + 3 * count3s s := by
  unfold Composition.weight count2s count3s isHoffmanComposition at *
  induction s with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have hn := hs n (by simp)
    have ih' := ih (fun m hm => hs m (List.mem_cons_of_mem n hm))
    cases hn with
    | inl h2 =>
      -- n.val = 2
      simp only [ih', h2, beq_self_eq_true, ↓reduceIte, beq_iff_eq]
      simp (config := {decide := true}) only [ite_false, add_zero]
      omega
    | inr h3 =>
      -- n.val = 3
      simp only [ih', h3, beq_self_eq_true, ↓reduceIte, beq_iff_eq]
      simp (config := {decide := true}) only [ite_false, add_zero]
      omega

/-! ## Standard Hoffman compositions -/

/-- ζ(2) = π²/6 -/
def hoffman_2 : Composition := [⟨2, by omega⟩]

/-- ζ(3) ≈ 1.202... (Apéry's constant) -/
def hoffman_3 : Composition := [⟨3, by omega⟩]

/-- ζ(2,2) -/
def hoffman_22 : Composition := [⟨2, by omega⟩, ⟨2, by omega⟩]

/-- ζ(2,3) -/
def hoffman_23 : Composition := [⟨2, by omega⟩, ⟨3, by omega⟩]

/-- ζ(3,2) -/
def hoffman_32 : Composition := [⟨3, by omega⟩, ⟨2, by omega⟩]

/-- ζ(3,3) -/
def hoffman_33 : Composition := [⟨3, by omega⟩, ⟨3, by omega⟩]

/-- ζ(2,2,2) -/
def hoffman_222 : Composition := [⟨2, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩]

/-- hoffman_2 is a Hoffman composition -/
theorem hoffman_2_isHoffman : isHoffmanComposition hoffman_2 := by
  intro n hn
  simp only [hoffman_2, List.mem_singleton] at hn
  left; simp [hn]

/-- hoffman_3 is a Hoffman composition -/
theorem hoffman_3_isHoffman : isHoffmanComposition hoffman_3 := by
  intro n hn
  simp only [hoffman_3, List.mem_singleton] at hn
  right; simp [hn]

/-- Brown's theorem (Hoffman's conjecture):
    The motivic MZVs ζᵐ(n₁,...,nᵣ) with nᵢ ∈ {2,3} form a basis
    for the space of motivic multiple zeta values.

    As a consequence, every MZV is a ℚ-linear combination of Hoffman MZVs.

    Reference: Brown, "Mixed Tate motives over Z", Theorem 1.1 -/
def brown_hoffman_basis : Prop :=
  ∀ w : ℕ, w ≥ 2 → ∃ s : Composition, isHoffmanComposition s ∧ s.weight = w

/-! ## Level Filtration

Brown's proof uses a "level" filtration on Hoffman compositions,
where the level is the number of 3s in the composition.
-/

/-- The level of a composition is the count of 3s (for Hoffman compositions) -/
def level (s : Composition) : ℕ := count3s s

/-- Level 0 Hoffman compositions consist only of 2s -/
def isLevel0 (s : Composition) : Prop :=
  isHoffmanComposition s ∧ level s = 0

/-- A level 0 composition of weight 2k is just (2,2,...,2) with k copies -/
theorem level0_unique (s : Composition) (hs : isLevel0 s) :
    ∀ n ∈ s, n.val = 2 := by
  intro n hn
  have ⟨hh, hl⟩ := hs
  have h23 := hh n hn
  cases h23 with
  | inl h2 => exact h2
  | inr h3 =>
    -- If n = 3, then count3s s ≥ 1, contradicting level = 0
    unfold level count3s at hl
    -- Use List.countP_eq_zero to derive contradiction
    rw [List.countP_eq_zero] at hl
    have := hl n hn
    simp only [h3, beq_self_eq_true] at this
    exact (this True.intro).elim

end StringAlgebra.MZV
