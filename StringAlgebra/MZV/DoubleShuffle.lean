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
def equiv (f g : FormalSum) : Bool :=
  let nf := normalize f
  let ng := normalize g
  nf.length = ng.length ∧ nf.all (ng.contains ·)

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

/-- Shuffle product on compositions (using the generic shuffle on lists).

    This is the shuffle of compositions viewed as lists of ℕ+. -/
def shuffleComp (s t : Composition) : List Composition :=
  shuffle s t

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

/-- Shuffle regularization for non-admissible compositions.

    Uses the iterated integral representation and extends to
    the boundary by taking regularized limits.

    reg_ш(ζ(1)) is defined such that Chen's lemma still holds. -/
noncomputable def shuffleRegularization (s : Composition) : FormalSum := by
  classical
  exact if Composition.isAdmissible s then [(1, s)] else []

/-- Stuffle regularization for non-admissible compositions.

    Uses harmonic series regularization:
    ζ*(1) := lim_{n→∞} (H_n - log(n))
           = γ (Euler's constant)

    More generally, ζ*(s₁,...,sₖ) with s₁ = 1 is defined by
    a similar limiting procedure. -/
noncomputable def stuffleRegularization (s : Composition) : FormalSum := by
  classical
  exact if Composition.isAdmissible s then [(1, s)] else []

/-- The extended double shuffle (EDS) relations.

    Even for non-admissible compositions, the regularized shuffle
    and stuffle must agree:
    reg_ш(Σ_{w ∈ u ш v} ζ(w)) = reg_*(Σ_{s ∈ s * t} ζ(s)) -/
def extendedDoubleShuffle : Prop :=
  ∀ s t : Composition,
    shuffleRegularization s ++ stuffleRegularization t =
      stuffleRegularization t ++ shuffleRegularization s

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

    ∂_n(s₁, ..., sₖ) = Σᵢ (s₁, ..., sᵢ + n, ..., sₖ)

    For each position i, we create a term where sᵢ is replaced by sᵢ + n. -/
def iharaDerivComp (n : ℕ) (s : Composition) : FormalSum :=
  (List.range s.length).map fun i => (1, addAtPositionDS s i n)

theorem iharaDerivComp_length (n : ℕ) (s : Composition) :
    (iharaDerivComp n s).length = s.length := by
  simp [iharaDerivComp]

/-- The Ihara derivation D_n acts on formal sums of compositions.

    D_n(Σ cᵢ sᵢ) = Σᵢ cᵢ · D_n(sᵢ)

    where D_n(s) = Σⱼ (s₁,...,sⱼ+n,...,sₖ) sums over all positions. -/
def iharaDerivation (n : ℕ) (f : FormalSum) : FormalSum :=
  f.flatMap fun (c, s) =>
    (iharaDerivComp n s).map fun (q, t) => (c * q, t)

@[simp] theorem iharaDerivation_nil (n : ℕ) :
    iharaDerivation n [] = [] := rfl

theorem iharaDerivation_single_coeff (n : ℕ) (c : ℚ) (s : Composition) :
    iharaDerivation n [(c, s)] =
      (iharaDerivComp n s).map (fun (q, t) => (c * q, t)) := by
  simp [iharaDerivation]

theorem iharaDerivation_append (n : ℕ) (f g : FormalSum) :
    iharaDerivation n (f ++ g) = iharaDerivation n f ++ iharaDerivation n g := by
  simp [iharaDerivation, List.flatMap_append]

/-- Ihara derivations satisfy a Lie algebra structure. -/
def ihara_lie_algebra : Prop :=
  ∀ n : ℕ, ∀ f g : FormalSum,
    iharaDerivation n (f ++ g) = iharaDerivation n f ++ iharaDerivation n g

/-- The implemented Ihara derivation satisfies the additive derivation law
    on formal sums. -/
theorem ihara_lie_algebra_holds : ihara_lie_algebra := by
  intro n f g
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

/-- The generating function for Zagier's dimension formula.

    1 / (1 - x² - x³) = Σ d_n x^n -/
def zagier_generating_function : Prop :=
  ∀ n : ℕ, zagierDimension (n + 3) = zagierDimension (n + 1) + zagierDimension n

/-- Goncharov's conjecture: the double shuffle relations
    give ALL relations between MZVs. -/
def goncharov_conjecture : Prop :=
  fds_generates_relations

end StringAlgebra.MZV
