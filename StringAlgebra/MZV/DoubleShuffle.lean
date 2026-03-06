/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.ShuffleAlgebra
import StringAlgebra.MZV.StuffleAlgebra
import Mathlib.Algebra.Algebra.Rat

/-!
# Double Shuffle Relations

This file develops the double shuffle relations, which are fundamental constraints
on multiple zeta values arising from the compatibility of shuffle and stuffle products.

## Main definitions

* `DoubleShuffle` - The double shuffle relation structure
* `FiniteDoubleShuffle` - Regularized double shuffle relations
* `Regularization` - Shuffle and stuffle regularization

## Mathematical Background

### The Double Shuffle Relations

For admissible compositions, the MZV evaluation is well-defined and satisfies:

  **Shuffle relation**: Σ_{w ∈ u ш v} ζ(w) = ζ(u) · ζ(v)
  **Stuffle relation**: Σ_{s ∈ s * t} ζ(s) = ζ(s) · ζ(t)

The **double shuffle relations** state that these must be consistent:
when we compute ζ(s)·ζ(t) using both methods, we get the same answer.

### Extended Double Shuffle (EDS)

For non-admissible compositions, MZVs diverge but can be regularized.
The extended double shuffle relations include:

1. **Shuffle regularization**: Use Chen's lemma for iterated integrals
2. **Stuffle regularization**: Use harmonic series regularization
3. **Compatibility**: Both regularizations must agree

### The Finite Double Shuffle Relations

By taking differences of shuffle and stuffle products, one obtains
polynomial relations that do not require regularization:

  Σ_{w ∈ u ш v} ζ(w) - Σ_{s ∈ s * t} ζ(s) = 0

### Depth Reduction

Double shuffle relations can be used to express deeper MZVs in terms
of shallower ones. Key examples:

  ζ(2,1) = ζ(3)  (from ζ(2)ш(1) vs ζ(2)*(1))

## References

* Hoffman - "The algebra of multiple harmonic series"
* Ihara, Kaneko, Zagier - "Derivation and double shuffle relations"
* Brown - "Mixed Tate motives over ℤ"
* Racinet - "Doubles mélanges des polylogarithmes multiples"
-/

namespace StringAlgebra.MZV

open List

/-! ## The Formal MZV Algebra -/

/-- A formal sum of compositions with rational coefficients.

    This represents elements of the formal MZV algebra before
    quotienting by relations. Elements are represented as lists
    of (coefficient, composition) pairs.

    Note: This representation allows duplicate compositions with
    different coefficients. The `normalize` function combines
    like terms. For a canonical representation, use `normalize`
    before comparison.

    Mathematically, this is the free ℚ-module on compositions,
    with the shuffle or stuffle product extending to an algebra. -/
abbrev FormalSum := List (ℚ × Composition)

namespace FormalSum

/-- The zero formal sum -/
def zero : FormalSum := []

/-- A single composition with coefficient 1 -/
def single (s : Composition) : FormalSum := [(1, s)]

/-- Scalar multiplication -/
def smul (c : ℚ) (f : FormalSum) : FormalSum :=
  f.map fun (q, s) => (c * q, s)

/-- Addition of formal sums (concatenation, doesn't combine like terms) -/
def add (f g : FormalSum) : FormalSum := f ++ g

/-- Negation -/
def neg (f : FormalSum) : FormalSum :=
  f.map fun (q, s) => (-q, s)

/-- Subtraction -/
def sub (f g : FormalSum) : FormalSum := add f (neg g)

/-- Combine like terms in a formal sum.

    Groups terms by composition and sums their coefficients.
    Removes terms with zero coefficient. -/
def normalize (f : FormalSum) : FormalSum :=
  let grouped := f.foldl (fun acc (c, s) =>
    match acc.lookup s with
    | some c' => (s, c + c') :: acc.filter (·.1 ≠ s)
    | none => (s, c) :: acc
  ) ([] : List (Composition × ℚ))
  grouped.filter (·.2 ≠ 0) |>.map (fun (s, c) => (c, s))

/-- Convert a list of compositions to a formal sum with coefficient 1 each -/
def ofList (l : List Composition) : FormalSum :=
  l.map fun s => (1, s)

/-- Check if two formal sums are equivalent (equal after normalization) -/
def heuristicEquiv (f g : FormalSum) : Bool :=
  let nf := normalize f
  let ng := normalize g
  nf.length = ng.length ∧ nf.all (ng.contains ·)

/-- Formal-sum evaluation against a coefficient map. -/
def eval (ζ : Composition → ℚ) (f : FormalSum) : ℚ :=
  List.sum (f.map fun (c, s) => c * ζ s)

/-- Semantic equivalence of formal sums under all coefficient maps. -/
def Equivalent (f g : FormalSum) : Prop :=
  ∀ ζ : Composition → ℚ, eval ζ f = eval ζ g

theorem equivalent_refl (f : FormalSum) : Equivalent f f := by
  intro ζ
  rfl

theorem equivalent_symm {f g : FormalSum} (h : Equivalent f g) : Equivalent g f := by
  intro ζ
  symm
  exact h ζ

theorem equivalent_trans {f g h : FormalSum}
    (hfg : Equivalent f g) (hgh : Equivalent g h) : Equivalent f h := by
  intro ζ
  exact Eq.trans (hfg ζ) (hgh ζ)

/-- The total coefficient sum (useful for checking relations) -/
def totalCoeff (f : FormalSum) : ℚ :=
  f.foldl (fun acc (c, _) => acc + c) 0

/-! ### Basic Properties -/

/-- Adding zero on the left is identity -/
theorem add_zero_left (f : FormalSum) : add zero f = f := by
  simp only [add, zero, List.nil_append]

/-- Adding zero on the right is identity -/
theorem add_zero_right (f : FormalSum) : add f zero = f := by
  simp only [add, zero, List.append_nil]

/-- Scalar multiplication by 1 is identity -/
theorem smul_one (f : FormalSum) : smul 1 f = f := by
  simp only [smul, one_mul, List.map_id']

/-- Scalar multiplication by 0 gives zero -/
theorem smul_zero_eq (f : FormalSum) : smul 0 f = f.map fun (_, s) => (0, s) := by
  simp only [smul, zero_mul]

/-- Negation is scalar multiplication by -1 -/
theorem neg_eq_smul_neg_one (f : FormalSum) : neg f = smul (-1) f := by
  simp only [neg, smul, neg_one_mul]

/-- The weight of a formal sum (maximum weight of components) -/
def maxWeight (f : FormalSum) : ℕ :=
  f.foldl (fun acc (_, s) => max acc s.weight) 0

/-- Filter a formal sum to keep only terms of a given weight -/
def filterByWeight (w : ℕ) (f : FormalSum) : FormalSum :=
  f.filter fun (_, s) => s.weight = w

/-- Filter a formal sum to keep only terms of a given depth -/
def filterByDepth (d : ℕ) (f : FormalSum) : FormalSum :=
  f.filter fun (_, s) => s.depth = d

/-- Check if a formal sum is homogeneous (all terms have same weight) -/
def isHomogeneous (f : FormalSum) : Bool :=
  match f with
  | [] => true
  | (_, s) :: rest => rest.all fun (_, t) => t.weight = s.weight

/-- The minimum weight of a formal sum (0 if empty) -/
def minWeight (f : FormalSum) : ℕ :=
  match f with
  | [] => 0
  | (_, s) :: rest => rest.foldl (fun acc (_, t) => min acc t.weight) s.weight

/-- Multiply a formal sum by a single composition (stuffle product) -/
def mulSingle (f : FormalSum) (t : Composition) : FormalSum :=
  f.flatMap fun (c, s) =>
    (stuffle s t).map fun r => (c, r)

end FormalSum

/-! ## Shuffle Product on Formal Sums -/

/-- Shuffle product on compositions induced from shuffling the associated `{0,1}` words.

    This is the mathematically relevant shuffle for MZVs: convert compositions to
    iterated-integral words, shuffle those words, then decode the result back to
    compositions. -/
def shuffleComp (s t : Composition) : List Composition :=
  (shuffle (compositionToWord s) (compositionToWord t)).filterMap wordToComposition

/-- Every term in the shuffle product has the expected total weight. -/
theorem mem_shuffleComp_weight {s t r : Composition} (hr : r ∈ shuffleComp s t) :
    r.weight = s.weight + t.weight := by
  unfold shuffleComp at hr
  simp only [List.mem_filterMap] at hr
  rcases hr with ⟨w, hw, hdecode⟩
  have hlength :
      w.weight = (compositionToWord s).weight + (compositionToWord t).weight := by
    simpa [MZVWord.weight] using
      shuffle_length_eq (compositionToWord s) (compositionToWord t) w hw
  calc
    r.weight = w.weight := wordToComposition_weight hdecode
    _ = (compositionToWord s).weight + (compositionToWord t).weight := hlength
    _ = s.weight + t.weight := by rw [compositionToWord_weight, compositionToWord_weight]

/-- Extend shuffle to formal sums.

    (Σ aᵢ sᵢ) ш (Σ bⱼ tⱼ) = Σᵢⱼ aᵢbⱼ (sᵢ ш tⱼ) -/
def shuffleFormal (f g : FormalSum) : FormalSum :=
  f.flatMap fun (a, s) =>
    g.flatMap fun (b, t) =>
      (shuffleComp s t).map fun r => (a * b, r)

/-! ## Stuffle Product on Formal Sums -/

/-- Extend stuffle to formal sums.

    (Σ aᵢ sᵢ) * (Σ bⱼ tⱼ) = Σᵢⱼ aᵢbⱼ (sᵢ * tⱼ) -/
def stuffleFormal (f g : FormalSum) : FormalSum :=
  f.flatMap fun (a, s) =>
    g.flatMap fun (b, t) =>
      (stuffle s t).map fun r => (a * b, r)

/-! ## The Double Shuffle Relations -/

/-- The double shuffle relation for two compositions.

    DS(s, t) = (s ш t) - (s * t)

    When evaluated on MZVs, this equals zero. -/
def doubleShuffleRelation (s t : Composition) : FormalSum :=
  -- Shuffle of compositions
  let shuffleTerms := FormalSum.ofList (shuffleComp s t)
  -- Stuffle of compositions
  let stuffleTerms := FormalSum.ofList (stuffle s t)
  FormalSum.sub shuffleTerms stuffleTerms

/-- Every term appearing in a double shuffle relation has the expected total weight. -/
theorem mem_doubleShuffleRelation_weight {s t r : Composition} {q : ℚ}
    (h : (q, r) ∈ doubleShuffleRelation s t) :
    r.weight = s.weight + t.weight := by
  unfold doubleShuffleRelation FormalSum.sub FormalSum.add FormalSum.neg FormalSum.ofList at h
  simp only [List.mem_append, List.mem_map] at h
  rcases h with h | h
  · rcases h with ⟨r', hr', hpair⟩
    cases hpair
    exact mem_shuffleComp_weight hr'
  · rcases h with ⟨p, hp, hpair⟩
    rcases hp with ⟨r', hr', hp'⟩
    cases hp'
    cases hpair
    exact stuffle_weight_eq s t r' hr'

/-- A double shuffle relation is a formal sum that equals zero
    when evaluated on MZVs.

    These arise from the equation:
    Σ_{w ∈ u ш v} ζ(w) = Σ_{s ∈ s * t} ζ(s)

    A formal sum is a valid double shuffle relation if it arises as the
    difference of shuffle and stuffle products for some compositions. -/
structure DoubleShuffleRelation where
  /-- The formal sum representing the relation -/
  relation : FormalSum
  /-- There exist compositions s and t such that this is their double shuffle -/
  isRelation : ∃ s t : Composition, relation = doubleShuffleRelation s t

/-- Construct a double shuffle relation from two compositions -/
def DoubleShuffleRelation.of (s t : Composition) : DoubleShuffleRelation where
  relation := doubleShuffleRelation s t
  isRelation := ⟨s, t, rfl⟩

/-! ## Key Examples -/

/-! ## Regularization -/

/-- Truncation helper used for toy models: keep admissible inputs and drop the rest.

    This is not an analytic regularization. It is provided only as a minimal
    example implementing the regularization interface below. -/
noncomputable def truncateToAdmissible (s : Composition) : FormalSum := by
  classical
  exact if Composition.isAdmissible s then [(1, s)] else []

/-- A choice of shuffle and stuffle regularization procedures.

    The actual analytic regularizations used in extended double shuffle are not
    formalized here, so this structure records the interface they should satisfy
    on admissible inputs. -/
structure RegularizationModel where
  shuffleReg : Composition → FormalSum
  stuffleReg : Composition → FormalSum
  shuffleReg_admissible :
    ∀ s : Composition, Composition.isAdmissible s → shuffleReg s = [(1, s)]
  stuffleReg_admissible :
    ∀ s : Composition, Composition.isAdmissible s → stuffleReg s = [(1, s)]

/-- A minimal truncation-based regularization model.

    This model is computationally simple but intentionally weaker than analytic
    shuffle/stuffle regularization on divergent inputs. -/
noncomputable def truncationRegularizationModel : RegularizationModel where
  shuffleReg := truncateToAdmissible
  stuffleReg := truncateToAdmissible
  shuffleReg_admissible := by
    intro s hs
    simp [truncateToAdmissible, hs]
  stuffleReg_admissible := by
    intro s hs
    simp [truncateToAdmissible, hs]

/-- The extended double shuffle (EDS) relations.

    Even for non-admissible compositions, the regularized shuffle
    and stuffle must agree:
    reg_ш(Σ_{w ∈ u ш v} ζ(w)) = reg_*(Σ_{s ∈ s * t} ζ(s)) -/
def extendedDoubleShuffle (R : RegularizationModel) (evalReg : FormalSum → ℚ) : Prop :=
  ∀ s t : Composition,
    evalReg
      (FormalSum.sub
        (shuffleFormal (R.shuffleReg s) (R.shuffleReg t))
        (stuffleFormal (R.stuffleReg s) (R.stuffleReg t))) = 0

/-! ## Finite Double Shuffle -/

/-- Finite double shuffle relations are obtained by subtracting
    shuffle from stuffle, giving relations that don't require
    regularization (divergences cancel).

    FDS(s,t) = ш(s,t) - *(s,t) = 0

    These can be expressed purely polynomially. -/
def finiteDoubleShuffle (s t : Composition) : FormalSum :=
  doubleShuffleRelation s t

/-- The finite double shuffle relations generate all algebraic
    relations between MZVs (conjecturally). -/
def finiteDoubleShuffleBasis (basis : List (Composition × Composition)) : Prop :=
  ∀ r : DoubleShuffleRelation, ∃ p ∈ basis,
    r.relation = finiteDoubleShuffle p.1 p.2

/-- Finite-generation conjecture for double-shuffle relations:
    there exists a finite basis of composition pairs generating all
    registered double-shuffle relations. -/
def fds_generates_relations : Prop :=
  ∃ basis : List (Composition × Composition), finiteDoubleShuffleBasis basis

/-! ## Derivations and Ihara Action -/

/-- Modify the i-th element of a composition by adding n to it.
    Used for implementing Ihara derivations. -/
def addAtPositionDS (s : Composition) (i : ℕ) (n : ℕ) : Composition :=
  s.mapIdx fun j p => if j = i then ⟨p.val + n, Nat.add_pos_left p.pos n⟩ else p

/-- Apply Ihara derivation to a single composition.

    This implementation is a combinatorial weight-raising operator
    on composition indices. It is not Brown's coaction-derived
    odd derivation `∂_{2n+1}`.

    ∂_n(s₁, ..., sₖ) = Σᵢ (s₁, ..., sᵢ + n, ..., sₖ)

    For each position i, we create a term where sᵢ is replaced by sᵢ + n. -/
def iharaDerivComp (n : ℕ) (s : Composition) : FormalSum :=
  (List.range s.length).map fun i => (1, addAtPositionDS s i n)

/-- Alias emphasizing that `iharaDerivComp` raises composition entries by `n`. -/
abbrev weightRaiseDerivComp := iharaDerivComp

theorem iharaDerivComp_length (n : ℕ) (s : Composition) :
    (iharaDerivComp n s).length = s.length := by
  simp [iharaDerivComp]

/-- The Ihara derivation D_n acts on formal sums of compositions.

    This is the linear extension of `weightRaiseDerivComp`.

    D_n(Σ cᵢ sᵢ) = Σᵢ cᵢ · D_n(sᵢ)

    where D_n(s) = Σⱼ (s₁,...,sⱼ+n,...,sₖ) sums over all positions. -/
def iharaDerivation (n : ℕ) (f : FormalSum) : FormalSum :=
  f.flatMap fun (c, s) =>
    (iharaDerivComp n s).map fun (q, t) => (c * q, t)

/-- Alias emphasizing the implemented derivation model is weight-raising. -/
abbrev weightRaiseDerivation := iharaDerivation

@[simp] theorem iharaDerivation_nil (n : ℕ) :
    iharaDerivation n [] = [] := rfl

theorem iharaDerivation_single_coeff (n : ℕ) (c : ℚ) (s : Composition) :
    iharaDerivation n [(c, s)] =
      (iharaDerivComp n s).map (fun (q, t) => (c * q, t)) := by
  simp [iharaDerivation]

theorem iharaDerivation_append (n : ℕ) (f g : FormalSum) :
    iharaDerivation n (f ++ g) = iharaDerivation n f ++ iharaDerivation n g := by
  simp [iharaDerivation, List.flatMap_append]

/-- The weight-raising derivation is additive on formal sums (linearity).

    NOTE: This is NOT the Lie algebra structure of Ihara's derivations.
    The actual Lie algebra structure requires proving that the commutator
    [∂_m, ∂_n] = (m-n)∂_{m+n} (up to normalization), which is the content
    of `derivation_commutator_conjecture` in Relations.lean.
    This theorem only states that the derivation distributes over addition. -/
theorem weightRaiseDerivation_additive (n : ℕ) (f g : FormalSum) :
    iharaDerivation n (f ++ g) = iharaDerivation n f ++ iharaDerivation n g := by
  exact iharaDerivation_append n f g

/-! ## Connection to Motivic Structure -/

/-- The double shuffle relations are motivic.

    They arise from the de Rham/Betti comparison for the
    motivic fundamental group of P¹ \ {0, 1, ∞}. -/
def doubleShuffle_motivic (period : FormalSum → FormalSum) : Prop :=
  ∀ s t : Composition, period (finiteDoubleShuffle s t) = doubleShuffleRelation s t

/-- Motivic compatibility specialized to a concrete relation package. -/
theorem doubleShuffle_motivic_on_relation
    (period : FormalSum → FormalSum)
    (hperiod : doubleShuffle_motivic period)
    (s t : Composition) :
    period (DoubleShuffleRelation.of s t).relation = doubleShuffleRelation s t := by
  simpa [DoubleShuffleRelation.of] using hperiod s t

/-- The coaction on MZVs is compatible with double shuffle.

    Δ(ds relation) = (ds relation) ⊗ 1 + ... -/
def coaction_respects_doubleShuffle
    (coaction : FormalSum → FormalSum × FormalSum) : Prop :=
  ∀ s t : Composition,
    (coaction (doubleShuffleRelation s t)).1 = doubleShuffleRelation s t

/-! ## Dimension Formulas -/

/-- The dimension of the space of MZVs of weight n.

    Conjectured by Zagier:
    d_n = d_{n-2} + d_{n-3}

    with d_0 = 1, d_1 = 0, d_2 = 1.

    This gives: 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, ... -/
def zagierDimension : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => zagierDimension (n + 1) + zagierDimension n

/-- Zagier's dimension formula satisfies the recurrence d_{n+3} = d_{n+1} + d_n,
    which corresponds to the generating function 1/(1 - x² - x³).
    This is immediate from the definition. -/
theorem zagier_dimension_recurrence (n : ℕ) :
    zagierDimension (n + 3) = zagierDimension (n + 1) + zagierDimension n := by
  rfl

/-- Goncharov's conjecture: the double shuffle relations
    give ALL relations between MZVs. -/
def goncharov_conjecture : Prop :=
  fds_generates_relations

end StringAlgebra.MZV
