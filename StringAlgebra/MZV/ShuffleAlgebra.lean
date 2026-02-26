/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Shuffle Algebra

This file defines the shuffle product on words, which is fundamental to the
algebraic structure of multiple zeta values.

## Main definitions

* `shuffle` - The shuffle product of two words

## Mathematical Background

### The Shuffle Product

For words w = a₁...aₘ and v = b₁...bₙ, their shuffle product is:

  w ш v = Σ_{σ ∈ Sh(m,n)} σ(a₁...aₘb₁...bₙ)

where Sh(m,n) is the set of (m,n)-shuffles: permutations σ of {1,...,m+n}
such that σ(1) < ... < σ(m) and σ(m+1) < ... < σ(m+n).

Equivalently, by the recursive formula:
  ε ш w = w ш ε = w
  (a·u) ш (b·v) = a·(u ш (b·v)) + b·((a·u) ш v)

### Properties

The shuffle product is:
1. **Commutative**: w ш v = v ш w (as multisets)
2. **Associative**: (u ш v) ш w = u ш (v ш w)
3. **Unital**: ε ш w = w ш ε = w (ε = empty word)

### Connection to MZVs

The shuffle product encodes the product of iterated integrals:
  (∫ω_{w}) · (∫ω_{v}) = ∫ω_{w ш v}

This gives one of the two product structures on MZVs.

## References

* Reutenauer - "Free Lie Algebras"
* Brown - "Mixed Tate motives over ℤ"
* Hoffman - "The algebra of multiple harmonic series"
-/

namespace StringAlgebra.MZV

open List

variable {A : Type*}

/-! ## The Shuffle Product -/

/-- The shuffle product of two words.

    Defined recursively:
    - ε ш w = [w]
    - w ш ε = [w]
    - (a::u) ш (b::v) = a::(u ш (b::v)) + b::((a::u) ш v)

    Returns a list of words (the multiset of shuffled words). -/
def shuffle : Word A → Word A → List (Word A)
  | [], v => [v]
  | u, [] => [u]
  | a :: u, b :: v =>
      (shuffle u (b :: v)).map (a :: ·) ++
      (shuffle (a :: u) v).map (b :: ·)

/-- Notation for shuffle product -/
scoped infixl:70 " ш " => shuffle

/-- Shuffle with empty word on the left gives singleton -/
theorem shuffle_nil_left (w : Word A) : shuffle ([] : Word A) w = [w] := by
  simp only [shuffle]

/-- Shuffle with empty word on the right gives singleton -/
theorem shuffle_nil_right (w : Word A) : shuffle w ([] : Word A) = [w] := by
  cases w <;> simp only [shuffle]

/-- Every shuffle result has length = sum of input lengths -/
theorem shuffle_length_eq (u v : Word A) :
    ∀ w ∈ shuffle u v, w.length = u.length + v.length := by
  match u, v with
  | [], v =>
    simp only [shuffle, List.mem_singleton, forall_eq, List.length_nil, Nat.zero_add]
  | u, [] =>
    cases u with
    | nil => simp only [shuffle, List.mem_singleton, forall_eq, List.length_nil]
    | cons a u' =>
      simp only [shuffle, List.mem_singleton, forall_eq, List.length_nil, Nat.add_zero]
  | a :: u', b :: v' =>
    intro w hw
    simp only [shuffle, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · -- w = a :: w' where w' ∈ shuffle u' (b :: v')
      have ih := shuffle_length_eq u' (b :: v') w' hw'
      simp only [List.length_cons] at ih ⊢
      rw [ih]
      ac_rfl
    · -- w = b :: w' where w' ∈ shuffle (a :: u') v'
      have ih := shuffle_length_eq (a :: u') v' w' hw'
      simp only [List.length_cons] at ih ⊢
      rw [ih]
      ac_rfl

/-- The number of shuffles is the binomial coefficient -/
theorem shuffle_card (u v : Word A) :
    (shuffle u v).length = Nat.choose (u.length + v.length) u.length := by
  match u, v with
  | [], v =>
    simp only [shuffle, List.length_singleton, List.length_nil, Nat.zero_add, Nat.choose_zero_right]
  | u, [] =>
    cases u <;> simp only [shuffle, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.choose_self]
  | a :: u', b :: v' =>
    simp only [shuffle, List.length_append, List.length_map]
    rw [shuffle_card u' (b :: v'), shuffle_card (a :: u') v']
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.choose_succ_succ (u'.length + v'.length + 1) u'.length).symm

/-! ## Properties of Shuffle -/

/-- Shuffle is commutative (as multisets) -/
theorem shuffle_comm (u v : Word A) : (shuffle u v).Perm (shuffle v u) := by
  match u, v with
  | [], v =>
    simp [shuffle, shuffle_nil_right]
  | u, [] =>
    simp [shuffle_nil_left, shuffle_nil_right]
  | a :: u', b :: v' =>
    have h₁ : (shuffle u' (b :: v')).Perm (shuffle (b :: v') u') :=
      shuffle_comm u' (b :: v')
    have h₂ : (shuffle (a :: u') v').Perm (shuffle v' (a :: u')) :=
      shuffle_comm (a :: u') v'
    have h₁' :
        ((shuffle u' (b :: v')).map (a :: ·)).Perm
          ((shuffle (b :: v') u').map (a :: ·)) :=
      List.Perm.map (a :: ·) h₁
    have h₂' :
        ((shuffle (a :: u') v').map (b :: ·)).Perm
          ((shuffle v' (a :: u')).map (b :: ·)) :=
      List.Perm.map (b :: ·) h₂
    have hAppend :
        (((shuffle u' (b :: v')).map (a :: ·)) ++ ((shuffle (a :: u') v').map (b :: ·))).Perm
          (((shuffle (b :: v') u').map (a :: ·)) ++ ((shuffle v' (a :: u')).map (b :: ·))) :=
      List.Perm.append h₁' h₂'
    have hSwap :
        (((shuffle (b :: v') u').map (a :: ·)) ++ ((shuffle v' (a :: u')).map (b :: ·))).Perm
          (((shuffle v' (a :: u')).map (b :: ·)) ++ ((shuffle (b :: v') u').map (a :: ·))) :=
      List.perm_append_comm
    simpa [shuffle] using hAppend.trans hSwap

/-- Associativity specification for shuffle, up to permutation
    after expanding both parenthesizations. -/
def shuffle_assoc : Prop :=
  ∀ u v w : Word A,
    (List.flatMap (fun uv => shuffle uv w) (shuffle u v)).Perm
      (List.flatMap (fun vw => shuffle u vw) (shuffle v w))

/-- The empty word is a left unit -/
theorem shuffle_one_left (w : Word A) :
    shuffle ([] : Word A) w = [w] := shuffle_nil_left w

/-- The empty word is a right unit -/
theorem shuffle_one_right (w : Word A) :
    shuffle w ([] : Word A) = [w] := shuffle_nil_right w

/-! ## Connection to MZVs -/

/-- Shuffle-product relation for a chosen evaluation map on MZV words:
    `ζ(w) * ζ(v) = Σ_{u ∈ w ш v} ζ(u)`. -/
def mzv_shuffle_product {β : Type*} [Semiring β] (ζ : MZVWord → β) (w v : MZVWord) : Prop :=
  ζ w * ζ v = ((shuffle w v).map ζ).sum

/-! ## Lyndon Words -/

/-- A word is Lyndon if it is strictly smaller than all its proper rotations.

    Lyndon words form a basis for the free Lie algebra,
    and their shuffles span the shuffle algebra. -/
def isLyndon [LT A] (w : Word A) : Prop :=
  w ≠ [] ∧ ∀ i, 0 < i → i < w.length → w < w.rotate i

/-- Specification of Chen-Fox-Lyndon factorization:
    unique decomposition into a non-increasing list of Lyndon words. -/
def lyndon_factorization_unique [LinearOrder A] (w : Word A) : Prop :=
  ∃! factors : List (Word A),
    List.flatten factors = w ∧
    (∀ u ∈ factors, isLyndon u) ∧
    List.IsChain (fun u v => v ≤ u) factors

/-! ## Examples -/

/-- Example: shuffle of two single-letter words -/
example (a b : A) : shuffle [a] [b] = [[a, b], [b, a]] := by
  simp only [shuffle, map_cons, map_nil, nil_append, cons_append]

end StringAlgebra.MZV
