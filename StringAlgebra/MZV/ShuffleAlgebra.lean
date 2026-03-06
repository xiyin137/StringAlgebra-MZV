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

/-- Helper: flatMap over mapped list (beta-reduced). -/
theorem flatMap_map_eq {L : List α} {g : α → β} {f : β → List γ} :
    (L.map g).flatMap f = L.flatMap (fun x => f (g x)) := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- Helper: map distributes into flatMap. -/
theorem map_flatMap_eq (L : List α) (f : α → List β) (g : β → γ) :
    (L.flatMap f).map g = L.flatMap (fun x => (f x).map g) := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, ih]

/-- Helper: four-way append permutation (swap middle two). -/
theorem perm_append_swap_middle (A B C D : List α) :
    (A ++ B) ++ (C ++ D) ~ (A ++ C) ++ (B ++ D) := by
  have := List.Perm.append_right D (List.perm_append_comm (l₁ := B) (l₂ := C))
  simp only [List.append_assoc] at this ⊢
  exact List.Perm.append_left A this

/-- Shuffle is associative (as multisets).
    `(u ш v) ш w ≅ u ш (v ш w)` -/
theorem shuffle_assoc (u v w : Word A) :
    ((shuffle u v).flatMap (shuffle · w)).Perm
      ((shuffle v w).flatMap (shuffle u ·)) := by
  match u, v, w with
  | [], v, w =>
    simp [shuffle_nil_left, List.flatMap_cons, List.flatMap_nil]
  | u, [], w =>
    simp [shuffle_nil_right, shuffle_nil_left, List.flatMap_cons, List.flatMap_nil]
  | u, v, [] =>
    simp [shuffle_nil_right]
  | a :: u', b :: v', c :: w' =>
    have ih1 := shuffle_assoc u' (b :: v') (c :: w')
    have ih2 := shuffle_assoc (a :: u') v' (c :: w')
    have ih3 := shuffle_assoc (a :: u') (b :: v') w'
    simp only [shuffle]
    rw [List.flatMap_append, List.flatMap_append]
    simp only [flatMap_map_eq]
    have key_lhs (L : List (Word A)) :
        (L.flatMap (fun s => shuffle (a :: s) (c :: w'))).Perm
          (((L.flatMap (shuffle · (c :: w'))).map (a :: ·)) ++
            ((L.flatMap (fun s => shuffle (a :: s) w')).map (c :: ·))) := by
      have h := (List.flatMap_append_perm L
        (fun s => (shuffle s (c :: w')).map (a :: ·))
        (fun s => (shuffle (a :: s) w').map (c :: ·))).symm
      calc
        L.flatMap (fun s => shuffle (a :: s) (c :: w'))
            = L.flatMap (fun s =>
                (shuffle s (c :: w')).map (a :: ·) ++ (shuffle (a :: s) w').map (c :: ·)) := by
                  simp [shuffle]
        _ ~ (L.flatMap (fun s => (shuffle s (c :: w')).map (a :: ·))) ++
              (L.flatMap (fun s => (shuffle (a :: s) w').map (c :: ·))) := h
        _ = (((L.flatMap (shuffle · (c :: w'))).map (a :: ·)) ++
              ((L.flatMap (fun s => shuffle (a :: s) w')).map (c :: ·))) := by
              rw [← map_flatMap_eq, ← map_flatMap_eq]
    have key_lhs_b (L : List (Word A)) :
        (L.flatMap (fun s => shuffle (b :: s) (c :: w'))).Perm
          (((L.flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
            ((L.flatMap (fun s => shuffle (b :: s) w')).map (c :: ·))) := by
      have h := (List.flatMap_append_perm L
        (fun s => (shuffle s (c :: w')).map (b :: ·))
        (fun s => (shuffle (b :: s) w').map (c :: ·))).symm
      calc
        L.flatMap (fun s => shuffle (b :: s) (c :: w'))
            = L.flatMap (fun s =>
                (shuffle s (c :: w')).map (b :: ·) ++ (shuffle (b :: s) w').map (c :: ·)) := by
                  simp [shuffle]
        _ ~ (L.flatMap (fun s => (shuffle s (c :: w')).map (b :: ·))) ++
              (L.flatMap (fun s => (shuffle (b :: s) w').map (c :: ·))) := h
        _ = (((L.flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
              ((L.flatMap (fun s => shuffle (b :: s) w')).map (c :: ·))) := by
              rw [← map_flatMap_eq, ← map_flatMap_eq]
    have key_rhs_b (L : List (Word A)) :
        (L.flatMap (fun s => shuffle (a :: u') (b :: s))).Perm
          (((L.flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
            ((L.flatMap (shuffle (a :: u') ·)).map (b :: ·))) := by
      have h := (List.flatMap_append_perm L
        (fun s => (shuffle u' (b :: s)).map (a :: ·))
        (fun s => (shuffle (a :: u') s).map (b :: ·))).symm
      calc
        L.flatMap (fun s => shuffle (a :: u') (b :: s))
            = L.flatMap (fun s =>
                (shuffle u' (b :: s)).map (a :: ·) ++ (shuffle (a :: u') s).map (b :: ·)) := by
                  simp [shuffle]
        _ ~ (L.flatMap (fun s => (shuffle u' (b :: s)).map (a :: ·))) ++
              (L.flatMap (fun s => (shuffle (a :: u') s).map (b :: ·))) := h
        _ = (((L.flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
              ((L.flatMap (shuffle (a :: u') ·)).map (b :: ·))) := by
              rw [← map_flatMap_eq, ← map_flatMap_eq]
    have key_rhs_c (L : List (Word A)) :
        (L.flatMap (fun s => shuffle (a :: u') (c :: s))).Perm
          (((L.flatMap (fun s => shuffle u' (c :: s))).map (a :: ·)) ++
            ((L.flatMap (shuffle (a :: u') ·)).map (c :: ·))) := by
      have h := (List.flatMap_append_perm L
        (fun s => (shuffle u' (c :: s)).map (a :: ·))
        (fun s => (shuffle (a :: u') s).map (c :: ·))).symm
      calc
        L.flatMap (fun s => shuffle (a :: u') (c :: s))
            = L.flatMap (fun s =>
                (shuffle u' (c :: s)).map (a :: ·) ++ (shuffle (a :: u') s).map (c :: ·)) := by
                  simp [shuffle]
        _ ~ (L.flatMap (fun s => (shuffle u' (c :: s)).map (a :: ·))) ++
              (L.flatMap (fun s => (shuffle (a :: u') s).map (c :: ·))) := h
        _ = (((L.flatMap (fun s => shuffle u' (c :: s))).map (a :: ·)) ++
              ((L.flatMap (shuffle (a :: u') ·)).map (c :: ·))) := by
              rw [← map_flatMap_eq, ← map_flatMap_eq]
    have lhs_split := List.Perm.append
      (key_lhs (shuffle u' (b :: v')))
      (key_lhs_b (shuffle (a :: u') v'))
    have rhs_split := List.Perm.append
      (key_rhs_b (shuffle v' (c :: w')))
      (key_rhs_c (shuffle (b :: v') w'))
    have lhs_regroup := perm_append_swap_middle
      ((shuffle u' (b :: v')).flatMap (shuffle · (c :: w')) |>.map (a :: ·))
      ((shuffle u' (b :: v')).flatMap (fun s => shuffle (a :: s) w') |>.map (c :: ·))
      ((shuffle (a :: u') v').flatMap (shuffle · (c :: w')) |>.map (b :: ·))
      ((shuffle (a :: u') v').flatMap (fun s => shuffle (b :: s) w') |>.map (c :: ·))
    have rhs_regroup := perm_append_swap_middle
      ((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s)) |>.map (a :: ·))
      ((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·) |>.map (b :: ·))
      ((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s)) |>.map (a :: ·))
      ((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·) |>.map (c :: ·))
    have c_combine :
        ((shuffle u' (b :: v')).flatMap (fun s => shuffle (a :: s) w') ++
         (shuffle (a :: u') v').flatMap (fun s => shuffle (b :: s) w')).map (c :: ·) =
        ((shuffle (a :: u') (b :: v')).flatMap (shuffle · w')).map (c :: ·) := by
      rw [show shuffle (a :: u') (b :: v') =
          (shuffle u' (b :: v')).map (a :: ·) ++ (shuffle (a :: u') v').map (b :: ·) by
            simp [shuffle]]
      rw [List.flatMap_append, flatMap_map_eq, flatMap_map_eq, List.map_append]
    have a_combine :
        ((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s)) ++
         (shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·) =
        ((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·) := by
      rw [show shuffle (b :: v') (c :: w') =
          (shuffle v' (c :: w')).map (b :: ·) ++ (shuffle (b :: v') w').map (c :: ·) by
            simp [shuffle]]
      rw [List.flatMap_append, flatMap_map_eq, flatMap_map_eq, List.map_append]
    have ih_groups :
        ((((shuffle u' (b :: v')).flatMap (shuffle · (c :: w'))).map (a :: ·) ++
            ((shuffle (a :: u') v').flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
          (((shuffle (a :: u') (b :: v')).flatMap (shuffle · w')).map (c :: ·))).Perm
          ((((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·) ++
              ((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·)) ++
            (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))) := by
      exact List.Perm.append
        (List.Perm.append (List.Perm.map _ ih1) (List.Perm.map _ ih2))
        (List.Perm.map _ ih3)
    have lhs_collapse :
        ((((shuffle u' (b :: v')).flatMap (shuffle · (c :: w'))).map (a :: ·) ++
            ((shuffle (a :: u') v').flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
          ((((shuffle u' (b :: v')).flatMap (fun s => shuffle (a :: s) w')).map (c :: ·)) ++
            (((shuffle (a :: u') v').flatMap (fun s => shuffle (b :: s) w')).map (c :: ·)))).Perm
          ((((shuffle u' (b :: v')).flatMap (shuffle · (c :: w'))).map (a :: ·) ++
            ((shuffle (a :: u') v').flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
          (((shuffle (a :: u') (b :: v')).flatMap (shuffle · w')).map (c :: ·))) := by
      have hc :
          ((((shuffle u' (b :: v')).flatMap (fun s => shuffle (a :: s) w')).map (c :: ·)) ++
              (((shuffle (a :: u') v').flatMap (fun s => shuffle (b :: s) w')).map (c :: ·))).Perm
            (((shuffle (a :: u') (b :: v')).flatMap (shuffle · w')).map (c :: ·)) := by
        exact List.Perm.of_eq (by simpa [List.map_append] using c_combine)
      exact List.Perm.append_left _ hc
    have rhs_expand :
        (((((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·)) ++
            (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))) ++
          (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))).Perm
          (((((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
              (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))) ++
            ((((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·)) ++
              (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·)))) := by
      have ha :
          (((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·)) =
            ((((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
              (((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·))) := by
        simpa [List.map_append] using a_combine.symm
      calc
        ((((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·)) ++
            (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))) ++
          (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))
            ~ (((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·)) ++
              ((((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·)) ++
                (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))) := by
                exact List.Perm.of_eq (List.append_assoc _ _ _)
        _ = ((((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·) ++
              (((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·))) ++
            ((((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·)) ++
              (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·)))) := by
                rw [ha]
        _ ~ (((((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
              (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))) ++
            ((((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·)) ++
              (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·)))) := by
                exact perm_append_swap_middle
                  (((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·))
                  (((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·))
                  (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))
                  (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))
    calc
      _ ~ ((((shuffle u' (b :: v')).flatMap (shuffle · (c :: w'))).map (a :: ·) ++
            ((shuffle (a :: u') v').flatMap (shuffle · (c :: w'))).map (b :: ·)) ++
          (((shuffle (a :: u') (b :: v')).flatMap (shuffle · w')).map (c :: ·))) := by
            exact lhs_split.trans <| lhs_regroup.trans lhs_collapse
      _ ~ ((((shuffle (b :: v') (c :: w')).flatMap (shuffle u' ·)).map (a :: ·) ++
            ((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·)) ++
          (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·))) := ih_groups
      _ ~ (((((shuffle v' (c :: w')).flatMap (fun s => shuffle u' (b :: s))).map (a :: ·)) ++
              (((shuffle v' (c :: w')).flatMap (shuffle (a :: u') ·)).map (b :: ·))) ++
            ((((shuffle (b :: v') w').flatMap (fun s => shuffle u' (c :: s))).map (a :: ·)) ++
              (((shuffle (b :: v') w').flatMap (shuffle (a :: u') ·)).map (c :: ·)))) := rhs_expand
      _ ~ _ := rhs_split.symm

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
