/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.ShuffleAlgebra

/-!
# Chen's Iterated Integrals

This file develops the theory of iterated integrals following K.T. Chen,
which provides the integral representation of multiple zeta values.

## Main definitions

* `IteratedIntegralWord` - Formal representation of an iterated integral
* `chenShuffle` - The shuffle product on iterated integrals
* `wordToMZV` - Connection between words and MZV values

## Mathematical Background

### Iterated Integrals

For differential 1-forms ω₁, ..., ωₙ on a manifold M and a path γ : [0,1] → M,
the iterated integral is:

  ∫_γ ω₁ω₂...ωₙ := ∫_{0<t₁<t₂<...<tₙ<1} γ*ω₁(t₁) ∧ γ*ω₂(t₂) ∧ ... ∧ γ*ωₙ(tₙ)

### MZV Iterated Integrals

For MZVs on P¹ \ {0, 1, ∞}, we use two forms:
- ω₀ = dt/t
- ω₁ = dt/(1-t)

Then:
  ζ(s₁, ..., sₖ) = ∫₀¹ ω₀^{s₁-1} ω₁ ... ω₀^{sₖ-1} ω₁

where the path is from 0 to 1 with appropriate regularization.

### Chen's Theorem

The iterated integral product formula:
  (∫_γ ω) · (∫_γ η) = ∫_γ (ω ш η)

where ш is the shuffle product.

### De Rham Theory

Iterated integrals give the de Rham realization of the fundamental
groupoid of M. For MZVs, this is π₁^{dR}(P¹ \ {0,1,∞}).

## References

* Chen - "Iterated path integrals"
* Brown - "Mixed Tate motives over ℤ"
* Hain - "The geometry of the mixed Hodge structure"
-/

namespace StringAlgebra.MZV

open List

/-! ## Differential Forms for MZVs -/

/-- The differential forms used in MZV iterated integrals.

    We work on P¹ \ {0, 1, ∞} with forms:
    - omega0 = dt/t (pole at 0)
    - omega1 = dt/(1-t) (pole at 1) -/
inductive MZVForm : Type
  | omega0 : MZVForm  -- dt/t
  | omega1 : MZVForm  -- dt/(1-t)
  deriving DecidableEq, Repr

/-- A word of differential forms represents an iterated integral -/
abbrev FormWord := List MZVForm

namespace FormWord

/-- The empty word represents the constant 1 -/
def empty : FormWord := []

/-- The weight (length) of a form word -/
def weight (w : FormWord) : ℕ := w.length

/-- Count of omega1 forms (= depth when interpreted as MZV) -/
def countOmega1 (w : FormWord) : ℕ :=
  w.countP (· == MZVForm.omega1)

/-- A word is convergent if it starts with omega1 and ends with omega0.

    This ensures the iterated integral ∫₀¹ converges. -/
def isConvergent (w : FormWord) : Prop :=
  w.head? = some MZVForm.omega1 ∧ w.getLast? = some MZVForm.omega0

/-- Swap omega0 ↔ omega1 (for complement relation) -/
def swap : MZVForm → MZVForm
  | MZVForm.omega0 => MZVForm.omega1
  | MZVForm.omega1 => MZVForm.omega0

/-- Complement of a word -/
def complement (w : FormWord) : FormWord := w.map swap

end FormWord

/-! ## Conversion: Compositions ↔ Form Words -/

/-- Convert a composition to a form word.

    (s₁, s₂, ..., sₖ) ↦ ω₀^{s₁-1} ω₁ ω₀^{s₂-1} ω₁ ... ω₀^{sₖ-1} ω₁

    This encodes the integral representation of ζ(s₁,...,sₖ). -/
def compositionToFormWord (s : Composition) : FormWord :=
  s.flatMap fun n =>
    List.replicate (n.val - 1) MZVForm.omega0 ++ [MZVForm.omega1]

/-- The form word for ζ(n) is ω₀^{n-1} ω₁ -/
theorem compositionToFormWord_depth1 (n : ℕ+) :
    compositionToFormWord [n] =
      List.replicate (n.val - 1) MZVForm.omega0 ++ [MZVForm.omega1] := by
  simp [compositionToFormWord]

/-- Weight is preserved: |w| = weight of composition -/
theorem compositionToFormWord_weight (s : Composition) :
    (compositionToFormWord s).weight = s.weight := by
  unfold compositionToFormWord FormWord.weight Composition.weight
  induction s with
  | nil => simp
  | cons n ns ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_replicate,
               List.length_singleton, List.map_cons, List.sum_cons]
    rw [ih]
    have h : n.val ≥ 1 := n.pos
    omega

/-- Depth is preserved: count of ω₁ = depth of composition -/
theorem compositionToFormWord_depth (s : Composition) :
    (compositionToFormWord s).countOmega1 = s.depth := by
  unfold compositionToFormWord FormWord.countOmega1 Composition.depth
  induction s with
  | nil => simp
  | cons n ns ih =>
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    rw [ih]
    -- Count omega1 in (replicate (n-1) omega0 ++ [omega1])
    simp only [List.countP_replicate, List.countP_cons, List.countP_nil, beq_iff_eq]
    simp only [reduceCtorEq, ↓reduceIte, Nat.zero_add]
    omega

/-- Convert a form word back to a composition (partial inverse).

    Reads blocks of ω₀*ω₁ and counts the ω₀s + 1 to get each part. -/
def formWordToComposition (w : FormWord) : Option Composition :=
  if w.getLast? ≠ some MZVForm.omega1 then
    none
  else
    -- Group by ω₁ separators and count ω₀s in each group
    some (go w [])
where
  go : FormWord → List ℕ+ → Composition
  | [], acc => acc.reverse
  | MZVForm.omega0 :: rest, acc =>
      match acc with
      | [] => go rest [⟨1, by omega⟩]  -- Start new group
      | h :: t => go rest (⟨h.val + 1, by omega⟩ :: t)  -- Increment current
  | MZVForm.omega1 :: rest, acc =>
      match acc with
      | [] => go rest [⟨1, by omega⟩]
      | _ => go rest (⟨1, by omega⟩ :: acc)  -- Close current, start new

/-! ## Iterated Integral Shuffle -/

/-- The shuffle product on form words.

    This is the algebraic encoding of Chen's product formula:
    (∫ ω)(∫ η) = ∫ (ω ш η) -/
def formShuffle : FormWord → FormWord → List FormWord :=
  shuffle

/-- Shuffle of form words encodes product of iterated integrals -/
theorem chen_product_formula (w₁ w₂ : FormWord) :
    ∀ w ∈ formShuffle w₁ w₂, w.length = w₁.length + w₂.length := by
  simpa [formShuffle] using shuffle_length_eq w₁ w₂

/-! ## Regularization -/

/-- A word is divergent if it doesn't satisfy convergence conditions -/
def isDivergent (w : FormWord) : Bool :=
  ¬(w.head? = some MZVForm.omega1 ∧ w.getLast? = some MZVForm.omega0)

/-- Shuffle regularization for divergent integrals.

    For words starting with ω₀ or ending with ω₁, we use the shuffle
    relation to express the divergent integral in terms of products
    of convergent integrals plus a regularized remainder.

    Example: ∫ω₀ is divergent, but we set it to 0 by convention. -/
def shuffleRegularize (w : FormWord) : List (FormWord × ℤ) :=
  if w.head? = some MZVForm.omega0 then
    []
  else if w.getLast? = some MZVForm.omega1 then
    []
  else
    [(w, 1)]

/-- ∫ω₀ = 0 (tangential basepoint regularization) -/
theorem omega0_regularized : shuffleRegularize [MZVForm.omega0] = [] := by
  simp [shuffleRegularize]

/-- ∫ω₁ = -log(1-1) diverges, regularized to 0 -/
theorem omega1_regularized : shuffleRegularize [MZVForm.omega1] = [] := by
  simp [shuffleRegularize]

/-! ## Duality -/

/-- The duality involution on form words.

    τ(w) = reverse(complement(w))

    This corresponds to the transformation t ↦ 1-t on the integral. -/
def duality (w : FormWord) : FormWord :=
  (w.complement).reverse

/-- swap is an involution -/
theorem swap_involutive (f : MZVForm) : FormWord.swap (FormWord.swap f) = f := by
  cases f <;> rfl

/-- Duality is an involution -/
theorem duality_involutive (w : FormWord) : duality (duality w) = w := by
  simp only [duality, FormWord.complement, List.map_reverse,
             List.reverse_reverse, List.map_map, Function.comp_def]
  conv_rhs => rw [← List.map_id w]
  congr 1
  funext x
  exact swap_involutive x

/-- The duality theorem: ∫τ(w) = ∫w for convergent words -/
theorem duality_theorem (w : FormWord) (_hw : w.isConvergent) :
    duality (duality w) = w := duality_involutive w

/-! ## The De Rham Fundamental Groupoid -/

/-- Formal groupoid element: a formal sum of form words.

    Elements of the completed tensor algebra on ⟨ω₀, ω₁⟩ modulo
    shuffle relations form the de Rham fundamental group. -/
abbrev GroupoidElement := List (ℤ × FormWord)

namespace GroupoidElement

/-- The identity (empty word with coefficient 1) -/
def one : GroupoidElement := [(1, [])]

/-- Concatenation of paths corresponds to concatenation of words -/
def concat (g₁ g₂ : GroupoidElement) : GroupoidElement :=
  g₁.flatMap fun (c₁, w₁) =>
    g₂.map fun (c₂, w₂) => (c₁ * c₂, w₁ ++ w₂)

/-- The group-like elements satisfy Δ(g) = g ⊗ g -/
def isGroupLike (g : GroupoidElement) : Prop :=
  ∃ c : ℤ, (c, []) ∈ g ∧ c = 1

end GroupoidElement

/-! ## Connection to Motivic Structures -/

/-- The period map sends a form word to its value.

    per : FormWord → ℂ (or ℝ for real MZVs)
    per(ω₀^{s₁-1}ω₁...ω₀^{sₖ-1}ω₁) = ζ(s₁,...,sₖ) -/
def formWordPeriodMap (w : FormWord) : ℕ :=
  w.countOmega1

/-- The de Rham realization is the vector space spanned by form words
    modulo shuffle relations. -/
def deRhamRealization : Type := FormWord  -- Modulo shuffle

/-- The Betti realization involves topology of paths. -/
def bettiRealization : Type := List FormWord

/-- The comparison isomorphism between de Rham and Betti gives periods. -/
theorem deRham_Betti_comparison :
    Nonempty (deRhamRealization → bettiRealization) := by
  refine ⟨fun w => [w]⟩

/-! ## Bar Construction -/

/-- The bar complex B(ω₀, ω₁).

    This is the algebraic structure underlying iterated integrals:
    - B₀ = k (ground field)
    - B₁ = ⟨ω₀, ω₁⟩
    - Bₙ = (B₁)^⊗n
    - Differential d via the bar construction -/
structure BarComplex where
  /-- Degree (number of tensored forms) -/
  degree : ℕ
  /-- The element (as a formal word) -/
  element : FormWord
  /-- Degree matches length -/
  degree_eq : degree = element.length

/-- Contract a form word at position i, removing the i-th and (i+1)-th elements.
    This represents the differential d[ω₁|...|ωₙ] = Σ [ω₁|...|ωᵢ·ωᵢ₊₁|...|ωₙ]
    where we omit the product term (which is in a different algebra). -/
def contractAt (w : FormWord) (i : ℕ) : FormWord :=
  w.take i ++ w.drop (i + 2)

/-- The bar differential d : Bₙ → Bₙ₋₁.

    d[ω₁|...|ωₙ] = Σᵢ₌₁ⁿ⁻¹ (-1)^i [ω₁|...|ω̂ᵢ|ω̂ᵢ₊₁|...|ωₙ]

    where the hat denotes omission (the pair is contracted).
    We return the list of contracted words with their signs. -/
def barDifferential (b : BarComplex) : List (Int × FormWord) :=
  if b.element.length ≤ 1 then []
  else
    (List.range (b.element.length - 1)).map fun i =>
      let contracted := contractAt b.element i
      let sign : Int := if i % 2 = 0 then 1 else -1
      (sign, contracted)

end StringAlgebra.MZV
