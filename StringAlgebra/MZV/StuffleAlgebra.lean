/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.Basic
import StringAlgebra.MZV.ShuffleAlgebra

/-!
# Stuffle (Quasi-Shuffle) Algebra

This file defines the stuffle product on compositions, the second fundamental
algebraic structure on multiple zeta values.

## Main definitions

* `stuffle` - The stuffle product on compositions

## Mathematical Background

### The Stuffle Product

The stuffle (or quasi-shuffle, or harmonic) product arises from multiplying
MZV series directly:

  ζ(s) · ζ(t) = Σ terms

For compositions s = (s₁) and t = (t₁):
  (s₁) * (t₁) = (s₁, t₁) + (t₁, s₁) + (s₁ + t₁)

The general recursive formula is:
  ε * s = s * ε = s
  (s₁, s') * (t₁, t') = (s₁, s' * (t₁, t')) + (t₁, (s₁, s') * t') + (s₁+t₁, s' * t')

### Key Difference from Shuffle

- **Shuffle**: comes from iterated integral representation
- **Stuffle**: comes from series representation

Both products respect the MZV evaluation map, giving the "double shuffle" relations.

### Quasi-Shuffle Axioms

The stuffle product is a quasi-shuffle algebra with:
- Underlying commutative semigroup: (ℕ⁺, +)
- This determines the "diagonal" term (s₁ + t₁)

## References

* Hoffman - "The algebra of multiple harmonic series"
* Hoffman - "Quasi-shuffle products"
* Brown - "Mixed Tate motives over ℤ"
-/

namespace StringAlgebra.MZV

/-! ## The Stuffle Product on Compositions -/

/-- The stuffle product of two compositions.

    Defined recursively:
    - ε * s = [s]
    - s * ε = [s]
    - (s₁::s') * (t₁::t') = (s₁::(s' * (t₁::t'))) + (t₁::((s₁::s') * t')) + ((s₁+t₁)::(s' * t'))

    Returns a list of compositions (the multiset of stuffle products). -/
def stuffle : Composition → Composition → List Composition
  | [], t => [t]
  | s, [] => [s]
  | s₁ :: s', t₁ :: t' =>
      -- First term: s₁ goes first
      (stuffle s' (t₁ :: t')).map (s₁ :: ·) ++
      -- Second term: t₁ goes first
      (stuffle (s₁ :: s') t').map (t₁ :: ·) ++
      -- Third term: diagonal (s₁ + t₁)
      (stuffle s' t').map ((s₁ + t₁) :: ·)

/-- Notation for stuffle product -/
scoped infixl:70 " ∗ " => stuffle

/-- Stuffle with empty composition on the left gives singleton -/
theorem stuffle_nil_left (s : Composition) : stuffle ([] : Composition) s = [s] := by
  simp only [stuffle]

/-- Stuffle with empty composition on the right gives singleton -/
theorem stuffle_nil_right (s : Composition) : stuffle s ([] : Composition) = [s] := by
  cases s <;> simp only [stuffle]

/-! ## Properties of Stuffle -/

/-- Helper lemma: weight of cons -/
theorem weight_cons (x : ℕ+) (xs : Composition) :
    Composition.weight (x :: xs) = x.val + Composition.weight xs := by
  simp only [Composition.weight, List.map_cons, List.sum_cons]

/-- Stuffle preserves total weight.
    This follows from the structure of the stuffle recursion:
    - Base cases preserve weight trivially
    - Inductive case: each of the three terms preserves weight -/
theorem stuffle_weight_eq (s t : Composition) :
    ∀ r ∈ stuffle s t, Composition.weight r = Composition.weight s + Composition.weight t := by
  match s, t with
  | [], t =>
    simp [stuffle, Composition.weight]
  | s, [] =>
    cases s with
    | nil =>
      simp [stuffle, Composition.weight]
    | cons s₁ s' =>
      simp [stuffle, Composition.weight]
  | s₁ :: s', t₁ :: t' =>
    intro r hr
    simp only [stuffle, List.mem_append, List.mem_map] at hr
    rcases hr with hr | hr
    · rcases hr with hr | hr
      · rcases hr with ⟨r', hr', rfl⟩
        have ih := stuffle_weight_eq s' (t₁ :: t') r' hr'
        simp only [weight_cons] at ih ⊢
        omega
      · rcases hr with ⟨r', hr', rfl⟩
        have ih := stuffle_weight_eq (s₁ :: s') t' r' hr'
        simp only [weight_cons] at ih ⊢
        omega
    · rcases hr with ⟨r', hr', rfl⟩
      have ih := stuffle_weight_eq s' t' r' hr'
      calc
        Composition.weight ((s₁ + t₁) :: r') = ((s₁ + t₁ : ℕ+) : ℕ) + Composition.weight r' := by
          simp [weight_cons]
        _ = ((s₁ : ℕ) + (t₁ : ℕ)) + Composition.weight r' := by rfl
        _ = ((s₁ : ℕ) + (t₁ : ℕ)) + (Composition.weight s' + Composition.weight t') := by
          rw [ih]
        _ = ((s₁ : ℕ) + Composition.weight s') + ((t₁ : ℕ) + Composition.weight t') := by
          omega
        _ = Composition.weight (s₁ :: s') + Composition.weight (t₁ :: t') := by
          simp [weight_cons]

/-- Stuffle is commutative (as multisets) -/
theorem stuffle_comm (s t : Composition) : (stuffle s t).Perm (stuffle t s) := by
  match s, t with
  | [], t =>
    simp [stuffle, stuffle_nil_right]
  | s, [] =>
    simp [stuffle_nil_left, stuffle_nil_right]
  | s₁ :: s', t₁ :: t' =>
    have h₁ : (stuffle s' (t₁ :: t')).Perm (stuffle (t₁ :: t') s') :=
      stuffle_comm s' (t₁ :: t')
    have h₂ : (stuffle (s₁ :: s') t').Perm (stuffle t' (s₁ :: s')) :=
      stuffle_comm (s₁ :: s') t'
    have h₃ : (stuffle s' t').Perm (stuffle t' s') :=
      stuffle_comm s' t'
    have hA :
        ((stuffle s' (t₁ :: t')).map (s₁ :: ·)).Perm
          ((stuffle (t₁ :: t') s').map (s₁ :: ·)) :=
      List.Perm.map (s₁ :: ·) h₁
    have hB :
        ((stuffle (s₁ :: s') t').map (t₁ :: ·)).Perm
          ((stuffle t' (s₁ :: s')).map (t₁ :: ·)) :=
      List.Perm.map (t₁ :: ·) h₂
    have hC :
        ((stuffle s' t').map ((s₁ + t₁) :: ·)).Perm
          ((stuffle t' s').map ((s₁ + t₁) :: ·)) :=
      List.Perm.map ((s₁ + t₁) :: ·) h₃
    have hAB :
        (((stuffle s' (t₁ :: t')).map (s₁ :: ·)) ++ ((stuffle (s₁ :: s') t').map (t₁ :: ·))).Perm
          (((stuffle (t₁ :: t') s').map (s₁ :: ·)) ++ ((stuffle t' (s₁ :: s')).map (t₁ :: ·))) :=
      List.Perm.append hA hB
    have hABC :
        ((((stuffle s' (t₁ :: t')).map (s₁ :: ·)) ++ ((stuffle (s₁ :: s') t').map (t₁ :: ·))) ++
          ((stuffle s' t').map ((s₁ + t₁) :: ·))).Perm
          ((((stuffle (t₁ :: t') s').map (s₁ :: ·)) ++ ((stuffle t' (s₁ :: s')).map (t₁ :: ·))) ++
            ((stuffle t' s').map ((s₁ + t₁) :: ·))) :=
      List.Perm.append hAB hC
    have hSwapCore :
        (((stuffle (t₁ :: t') s').map (s₁ :: ·)) ++ ((stuffle t' (s₁ :: s')).map (t₁ :: ·))).Perm
          (((stuffle t' (s₁ :: s')).map (t₁ :: ·)) ++ ((stuffle (t₁ :: t') s').map (s₁ :: ·))) :=
      List.perm_append_comm
    have hSwap :
        ((((stuffle (t₁ :: t') s').map (s₁ :: ·)) ++ ((stuffle t' (s₁ :: s')).map (t₁ :: ·))) ++
          ((stuffle t' s').map ((s₁ + t₁) :: ·))).Perm
          ((((stuffle t' (s₁ :: s')).map (t₁ :: ·)) ++ ((stuffle (t₁ :: t') s').map (s₁ :: ·))) ++
            ((stuffle t' s').map ((s₁ + t₁) :: ·))) :=
      List.Perm.append_right _ hSwapCore
    have hFinal :
        ((((stuffle s' (t₁ :: t')).map (s₁ :: ·)) ++ ((stuffle (s₁ :: s') t').map (t₁ :: ·))) ++
          ((stuffle s' t').map ((s₁ + t₁) :: ·))).Perm
          ((((stuffle t' (s₁ :: s')).map (t₁ :: ·)) ++ ((stuffle (t₁ :: t') s').map (s₁ :: ·))) ++
            ((stuffle t' s').map ((s₁ + t₁) :: ·))) :=
      hABC.trans hSwap
    have hTail :
        ((stuffle t' s').map ((s₁ + t₁) :: ·)) =
          ((stuffle t' s').map ((t₁ + s₁) :: ·)) := by
      simp [add_comm]
    rw [hTail] at hFinal
    simpa [stuffle, List.append_assoc] using hFinal

/-- Helper: 3-way flatMap distribution over append. -/
private theorem flatMap_append3_perm (L : List α) (f g h : α → List β) :
    (L.flatMap (fun x => f x ++ g x ++ h x)).Perm
      (L.flatMap f ++ L.flatMap g ++ L.flatMap h) := by
  have h1 := (List.flatMap_append_perm L (fun x => f x ++ g x) h).symm
  have h2 := (List.flatMap_append_perm L f g).symm
  exact h1.trans (List.Perm.append_right _ h2)

/-- Swap two adjacent blocks in a right-associated append chain. -/
private theorem perm_swap_blocks (A B X : List α) :
    (B ++ (A ++ X)).Perm (A ++ (B ++ X)) := by
  have := List.Perm.append_right X (List.perm_append_comm (l₁ := B) (l₂ := A))
  simp only [List.append_assoc] at this
  exact this

/-- 3×3 block transpose: rearranges
    (A₁ B₁ C₁)(A₂ B₂ C₂)(A₃ B₃ C₃) → (A₁ A₂ A₃)(B₁ B₂ B₃)(C₁ C₂ C₃). -/
private theorem perm_transpose_3x3 (A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : List α) :
    ((A₁ ++ B₁ ++ C₁) ++ (A₂ ++ B₂ ++ C₂) ++ (A₃ ++ B₃ ++ C₃)).Perm
    ((A₁ ++ A₂ ++ A₃) ++ (B₁ ++ B₂ ++ B₃) ++ (C₁ ++ C₂ ++ C₃)) := by
  simp only [List.append_assoc]
  apply List.Perm.append_left A₁
  -- 9 block swaps (bubble sort)
  exact
    -- Move A₂ past C₁, B₁
    (List.Perm.append_left B₁ (perm_swap_blocks A₂ C₁ _))
    |>.trans (perm_swap_blocks A₂ B₁ _)
    -- Move A₃ past C₂, B₂, C₁, B₁
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left B₁ (List.Perm.append_left C₁
        (List.Perm.append_left B₂ (perm_swap_blocks A₃ C₂ _)))))
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left B₁ (List.Perm.append_left C₁
        (perm_swap_blocks A₃ B₂ _))))
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left B₁
        (perm_swap_blocks A₃ C₁ _)))
    |>.trans (List.Perm.append_left A₂ (perm_swap_blocks A₃ B₁ _))
    -- Move B₂ past C₁
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left A₃ (List.Perm.append_left B₁
        (perm_swap_blocks B₂ C₁ _))))
    -- Move B₃ past C₂, C₁
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left A₃ (List.Perm.append_left B₁
        (List.Perm.append_left B₂ (List.Perm.append_left C₁
          (perm_swap_blocks B₃ C₂ _))))))
    |>.trans (List.Perm.append_left A₂ (List.Perm.append_left A₃ (List.Perm.append_left B₁
        (List.Perm.append_left B₂ (perm_swap_blocks B₃ C₁ _)))))

/-- De-interleave: (B₁C₁)(B₂C₂)(B₃C₃) → (B₁B₂B₃)(C₁C₂C₃). -/
private theorem perm_deinterleave (B₁ C₁ B₂ C₂ B₃ C₃ : List α) :
    (B₁ ++ C₁ ++ B₂ ++ C₂ ++ B₃ ++ C₃).Perm
    (B₁ ++ B₂ ++ B₃ ++ C₁ ++ C₂ ++ C₃) := by
  simp only [List.append_assoc]
  apply List.Perm.append_left B₁
  -- C₁(B₂(C₂(B₃ C₃))) → B₂(B₃(C₁(C₂ C₃)))
  exact (perm_swap_blocks B₂ C₁ _).trans
    (List.Perm.append_left B₂
      ((List.Perm.append_left C₁ (perm_swap_blocks B₃ C₂ _)).trans
       (perm_swap_blocks B₃ C₁ _)))

/-- Key split lemma for stuffle LHS: expanding stuffle (x :: y) (z :: w) in a flatMap. -/
private theorem stuffle_key_lhs (L : List Composition) (x z : ℕ+) (w : Composition) :
    (L.flatMap (fun y => stuffle (x :: y) (z :: w))).Perm
      ((L.flatMap (stuffle · (z :: w))).map (x :: ·) ++
       (L.flatMap (fun y => stuffle (x :: y) w)).map (z :: ·) ++
       (L.flatMap (stuffle · w)).map ((x + z) :: ·)) := by
  simp_rw [show ∀ y, stuffle (x :: y) (z :: w) =
    (stuffle y (z :: w)).map (x :: ·) ++ (stuffle (x :: y) w).map (z :: ·) ++
    (stuffle y w).map ((x + z) :: ·) from fun y => by simp [stuffle]]
  have h := flatMap_append3_perm L
    (fun y => (stuffle y (z :: w)).map (x :: ·))
    (fun y => (stuffle (x :: y) w).map (z :: ·))
    (fun y => (stuffle y w).map ((x + z) :: ·))
  rwa [← map_flatMap_eq, ← map_flatMap_eq, ← map_flatMap_eq] at h

/-- Key split lemma for stuffle RHS: expanding stuffle (x :: s) (z :: y) in a flatMap. -/
private theorem stuffle_key_rhs (L : List Composition) (x : ℕ+) (s : Composition) (z : ℕ+) :
    (L.flatMap (fun y => stuffle (x :: s) (z :: y))).Perm
      ((L.flatMap (fun y => stuffle s (z :: y))).map (x :: ·) ++
       (L.flatMap (stuffle (x :: s) ·)).map (z :: ·) ++
       (L.flatMap (stuffle s ·)).map ((x + z) :: ·)) := by
  simp_rw [show ∀ y, stuffle (x :: s) (z :: y) =
    (stuffle s (z :: y)).map (x :: ·) ++ (stuffle (x :: s) y).map (z :: ·) ++
    (stuffle s y).map ((x + z) :: ·) from fun y => by simp [stuffle]]
  have h := flatMap_append3_perm L
    (fun y => (stuffle s (z :: y)).map (x :: ·))
    (fun y => (stuffle (x :: s) y).map (z :: ·))
    (fun y => (stuffle s y).map ((x + z) :: ·))
  rwa [← map_flatMap_eq, ← map_flatMap_eq, ← map_flatMap_eq] at h

/-- The stuffle product is associative (as multisets).
    `(s ∗ t) ∗ u ≅ s ∗ (t ∗ u)` -/
theorem stuffle_assoc (s t u : Composition) :
    ((stuffle s t).flatMap (stuffle · u)).Perm
      ((stuffle t u).flatMap (stuffle s ·)) := by
  match s, t, u with
  | [], t, u =>
    simp [stuffle_nil_left, List.flatMap_cons, List.flatMap_nil]
  | s, [], u =>
    simp [stuffle_nil_right, stuffle_nil_left, List.flatMap_cons, List.flatMap_nil]
  | s, t, [] =>
    simp [stuffle_nil_right]
  | s₁ :: s', t₁ :: t', u₁ :: u' =>
    have ih_s := stuffle_assoc s' (t₁ :: t') (u₁ :: u')
    have ih_t := stuffle_assoc (s₁ :: s') t' (u₁ :: u')
    have ih_st := stuffle_assoc s' t' (u₁ :: u')
    have ih_u := stuffle_assoc (s₁ :: s') (t₁ :: t') u'
    have ih_su := stuffle_assoc s' (t₁ :: t') u'
    have ih_tu := stuffle_assoc (s₁ :: s') t' u'
    have ih_stu := stuffle_assoc s' t' u'
    -- Unfold outer stuffle, distribute flatMap, simplify flatMap-over-map
    simp only [stuffle]
    rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_append]
    simp only [flatMap_map_eq]
    -- Goal: 3 LHS terms ~ 3 RHS terms
    -- Step 1: Split each side into 9 sub-terms using key lemmas
    have lhs_split := List.Perm.append (List.Perm.append
        (stuffle_key_lhs (stuffle s' (t₁ :: t')) s₁ u₁ u')
        (stuffle_key_lhs (stuffle (s₁ :: s') t') t₁ u₁ u'))
        (stuffle_key_lhs (stuffle s' t') (s₁ + t₁) u₁ u')
    have rhs_split := List.Perm.append (List.Perm.append
        (stuffle_key_rhs (stuffle t' (u₁ :: u')) s₁ s' t₁)
        (stuffle_key_rhs (stuffle (t₁ :: t') u') s₁ s' u₁))
        (stuffle_key_rhs (stuffle t' u') s₁ s' (t₁ + u₁))
    -- Step 2: 3×3 transpose on LHS
    have lhs_trans := perm_transpose_3x3
      ((stuffle s' (t₁ :: t')).flatMap (stuffle · (u₁ :: u')) |>.map (s₁ :: ·))
      ((stuffle s' (t₁ :: t')).flatMap (fun y => stuffle (s₁ :: y) u') |>.map (u₁ :: ·))
      ((stuffle s' (t₁ :: t')).flatMap (stuffle · u') |>.map ((s₁ + u₁) :: ·))
      ((stuffle (s₁ :: s') t').flatMap (stuffle · (u₁ :: u')) |>.map (t₁ :: ·))
      ((stuffle (s₁ :: s') t').flatMap (fun y => stuffle (t₁ :: y) u') |>.map (u₁ :: ·))
      ((stuffle (s₁ :: s') t').flatMap (stuffle · u') |>.map ((t₁ + u₁) :: ·))
      ((stuffle s' t').flatMap (stuffle · (u₁ :: u')) |>.map ((s₁ + t₁) :: ·))
      ((stuffle s' t').flatMap (fun y => stuffle ((s₁ + t₁) :: y) u') |>.map (u₁ :: ·))
      ((stuffle s' t').flatMap (stuffle · u') |>.map (((s₁ + t₁) + u₁) :: ·))
    -- Step 3: 3×3 transpose on RHS
    have rhs_trans := perm_transpose_3x3
      ((stuffle t' (u₁ :: u')).flatMap (fun y => stuffle s' (t₁ :: y)) |>.map (s₁ :: ·))
      ((stuffle t' (u₁ :: u')).flatMap (stuffle (s₁ :: s') ·) |>.map (t₁ :: ·))
      ((stuffle t' (u₁ :: u')).flatMap (stuffle s' ·) |>.map ((s₁ + t₁) :: ·))
      ((stuffle (t₁ :: t') u').flatMap (fun y => stuffle s' (u₁ :: y)) |>.map (s₁ :: ·))
      ((stuffle (t₁ :: t') u').flatMap (stuffle (s₁ :: s') ·) |>.map (u₁ :: ·))
      ((stuffle (t₁ :: t') u').flatMap (stuffle s' ·) |>.map ((s₁ + u₁) :: ·))
      ((stuffle t' u').flatMap (fun y => stuffle s' ((t₁ + u₁) :: y)) |>.map (s₁ :: ·))
      ((stuffle t' u').flatMap (stuffle (s₁ :: s') ·) |>.map ((t₁ + u₁) :: ·))
      ((stuffle t' u').flatMap (stuffle s' ·) |>.map ((s₁ + (t₁ + u₁)) :: ·))
    -- Step 4: u₁-combine on LHS (column b → single term)
    -- The 3 u₁-prefixed terms combine back to the full stuffle product
    have u₁_combine :
        ((stuffle s' (t₁ :: t')).flatMap (fun y => stuffle (s₁ :: y) u')).map (u₁ :: ·) ++
        ((stuffle (s₁ :: s') t').flatMap (fun y => stuffle (t₁ :: y) u')).map (u₁ :: ·) ++
        ((stuffle s' t').flatMap (fun y => stuffle ((s₁ + t₁) :: y) u')).map (u₁ :: ·) =
        ((stuffle (s₁ :: s') (t₁ :: t')).flatMap (stuffle · u')).map (u₁ :: ·) := by
      rw [← List.map_append, ← List.map_append]
      congr 1
      rw [show stuffle (s₁ :: s') (t₁ :: t') =
        (stuffle s' (t₁ :: t')).map (s₁ :: ·) ++
        (stuffle (s₁ :: s') t').map (t₁ :: ·) ++
        (stuffle s' t').map ((s₁ + t₁) :: ·) from by simp [stuffle]]
      rw [List.flatMap_append, List.flatMap_append, flatMap_map_eq, flatMap_map_eq, flatMap_map_eq]
    -- Step 5: s₁-combine on RHS (column a → single term)
    have s₁_combine :
        ((stuffle t' (u₁ :: u')).flatMap (fun y => stuffle s' (t₁ :: y))).map (s₁ :: ·) ++
        ((stuffle (t₁ :: t') u').flatMap (fun y => stuffle s' (u₁ :: y))).map (s₁ :: ·) ++
        ((stuffle t' u').flatMap (fun y => stuffle s' ((t₁ + u₁) :: y))).map (s₁ :: ·) =
        ((stuffle (t₁ :: t') (u₁ :: u')).flatMap (stuffle s' ·)).map (s₁ :: ·) := by
      rw [← List.map_append, ← List.map_append]
      congr 1
      rw [show stuffle (t₁ :: t') (u₁ :: u') =
        (stuffle t' (u₁ :: u')).map (t₁ :: ·) ++
        (stuffle (t₁ :: t') u').map (u₁ :: ·) ++
        (stuffle t' u').map ((t₁ + u₁) :: ·) from by simp [stuffle]]
      rw [List.flatMap_append, List.flatMap_append, flatMap_map_eq, flatMap_map_eq, flatMap_map_eq]
    -- Step 6: Apply IH to each column group
    -- Column a: A₁++A₂++A₃ ~ combined_A'++B'₁++C'₁
    have ih_col_a := List.Perm.append (List.Perm.append
        (List.Perm.map (s₁ :: ·) ih_s)
        (List.Perm.map (t₁ :: ·) ih_t))
        (List.Perm.map ((s₁ + t₁) :: ·) ih_st)
    -- Column b: combined_B ~ B'₂
    have ih_col_b := List.Perm.map (u₁ :: ·) ih_u
    -- Column c: C₁++C₂++C₃ ~ C'₂++B'₃++C'₃
    have h_add : (s₁ + t₁) + u₁ = s₁ + (t₁ + u₁) := add_assoc s₁ t₁ u₁
    have ih_col_c := List.Perm.append (List.Perm.append
        (List.Perm.map ((s₁ + u₁) :: ·) ih_su)
        (List.Perm.map ((t₁ + u₁) :: ·) ih_tu))
        (h_add ▸ List.Perm.map ((s₁ + (t₁ + u₁)) :: ·) ih_stu)
    -- Step 7: Combine all IH results
    have ih_all := List.Perm.append (List.Perm.append ih_col_a ih_col_b) ih_col_c
    -- Step 8: Final proof chain
    refine (lhs_split.trans lhs_trans).trans ?_
    rw [u₁_combine]
    refine ih_all.trans ?_
    -- Fix s₁+t₁+u₁ vs s₁+(t₁+u₁) mismatch
    rw [h_add]
    -- Deinterleave + s₁_combine + rhs_split.symm
    -- The goal: deinterleave B'/C' columns, undo s₁_combine, reverse rhs split
    have rhs_chain := (rhs_split.trans rhs_trans).symm
    apply List.Perm.trans
    · -- Deinterleave: combined_A'++B'₁++C'₁++B'₂++C'₂++B'₃++C'₃
      --            → combined_A'++B'₁++B'₂++B'₃++C'₁++C'₂++C'₃
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (List.Perm.append_left _
        ((perm_swap_blocks _ _ _).trans
          (List.Perm.append_left _
            ((List.Perm.append_left _ (perm_swap_blocks _ _ _)).trans
             (perm_swap_blocks _ _ _)))))
    · -- s₁ expand + RHS chain
      rw [← s₁_combine]
      simp only [List.append_assoc] at rhs_chain ⊢
      exact rhs_chain

/-- The empty composition is a left unit -/
theorem stuffle_one_left (s : Composition) :
    stuffle ([] : Composition) s = [s] := stuffle_nil_left s

/-- The empty composition is a right unit -/
theorem stuffle_one_right (s : Composition) :
    stuffle s ([] : Composition) = [s] := stuffle_nil_right s

/-! ## Key Example: Depth 1 Stuffle -/

/-- For depth 1 compositions, stuffle gives:
    (m) * (n) = (m, n) + (n, m) + (m + n) -/
theorem stuffle_depth1 (m n : ℕ+) :
    stuffle [m] [n] = [[m, n], [n, m], [m + n]] := by
  simp only [stuffle, List.map_cons, List.map_nil, List.nil_append, List.cons_append]

/-- Depth-1 stuffle relation for admissible indices written as positive-integer compositions. -/
theorem mzv_stuffle_depth1 (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    ∃ (m' n' : ℕ+), (m' : ℕ) = m ∧ (n' : ℕ) = n ∧
      stuffle [m'] [n'] = [[m', n'], [n', m'], [m' + n']] := by
  have hm_pos : 0 < m := by omega
  have hn_pos : 0 < n := by omega
  let m' : ℕ+ := ⟨m, hm_pos⟩
  let n' : ℕ+ := ⟨n, hn_pos⟩
  refine ⟨m', n', rfl, rfl, ?_⟩
  simpa [m', n'] using stuffle_depth1 (m := m') (n := n')

/-! ## Double Shuffle Relations -/

/-- Specification of double-shuffle compatibility for given evaluation maps:
    evaluation through stuffle on compositions agrees with evaluation through
    shuffle on associated words.

    The evaluation maps `ζw` (on words) and `ζc` (on compositions) are
    supplied externally. This avoids the vacuity of existentially
    quantifying over arbitrary maps (which would be trivially satisfied
    by the zero map). -/
def double_shuffle_relation {β : Type*} [Semiring β]
    (ζw : MZVWord → β) (ζc : Composition → β) : Prop :=
  ∀ s t : Composition,
    ((stuffle s t).map ζc).sum =
      ((shuffle (compositionToWord s) (compositionToWord t)).map ζw).sum

/-! ## Regularization -/

/-- Regularization is needed when compositions are not admissible.

    For non-admissible compositions, the MZV series diverges,
    but can be regularized using shuffle or stuffle regularization. -/
def needsRegularization (s : Composition) : Bool :=
  match s with
  | [] => false
  | h :: _ => h.val < 2

end StringAlgebra.MZV
