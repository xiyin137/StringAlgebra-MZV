/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Polylogarithms and Multiple Polylogarithms

This file defines polylogarithms and their multi-index generalizations,
which are the analytic functions underlying multiple zeta values.

## Main definitions

* `Polylog` - The classical polylogarithm Li_n(z)
* `MultiplePolylog` - Multiple polylogarithm Li_{s₁,...,sₖ}(z₁,...,zₖ)
* `HarmonicPolylog` - Harmonic polylogarithm (special case with zᵢ ∈ {0, 1, -1})

## Mathematical Background

### Classical Polylogarithm

The polylogarithm of order n is defined by:

  Li_n(z) = Σ_{k=1}^∞ z^k / k^n    for |z| ≤ 1

Key properties:
- Li_1(z) = -log(1-z)
- Li_n(1) = ζ(n) for n ≥ 2
- Functional equations relating Li_n(z) and Li_n(1/z), Li_n(1-z), etc.

### Multiple Polylogarithms

The multiple polylogarithm is defined by:

  Li_{s₁,...,sₖ}(z₁,...,zₖ) = Σ_{n₁>n₂>...>nₖ≥1} z₁^{n₁}...zₖ^{nₖ} / (n₁^{s₁}...nₖ^{sₖ})

Special cases:
- Li_s(1,...,1) = ζ(s₁,...,sₖ) (MZV at zᵢ = 1)
- Li_s(z,1,...,1) = Li_{s₁,...,sₖ}(z) (Nielsen polylogarithm generalization)

### Connection to Iterated Integrals

  Li_{s₁,...,sₖ}(z₁,...,zₖ) = (-1)^k ∫_0^1 ω_{z₁}^{s₁-1} ω₁ ... ω_{zₖ}^{sₖ-1} ω₁

where ω_a = dt/(t-a).

### Harmonic Polylogarithms

When zᵢ ∈ {0, 1, -1}, we get harmonic polylogarithms (HPLs),
which appear frequently in physics calculations.

## References

* Goncharov - "Multiple polylogarithms and mixed Tate motives"
* Remiddi, Vermaseren - "Harmonic polylogarithms"
* Borwein, Bradley, Broadhurst, Lisoněk - "Special values of multiple polylogarithms"
-/

namespace StringAlgebra.MZV

/-! ## Classical Polylogarithm -/

/-- Convergence region for polylogarithms.

    The series Li_n(z) = Σ_{k=1}^∞ z^k / k^n converges:
    - For |z| < 1: always converges (for all n ≥ 1)
    - For |z| = 1: converges if n ≥ 2 (absolutely for n ≥ 2)
    - For |z| > 1: diverges

    This type abstracts the convergence condition without requiring ℂ. -/
inductive PolylogConvergence : Type
  | insideUnitDisk : PolylogConvergence   -- |z| < 1: always converges
  | onUnitCircle (n_ge_2 : Bool) : PolylogConvergence  -- |z| = 1: need n ≥ 2
  deriving DecidableEq, Repr

/-- The classical polylogarithm Li_n(z).

    Defined by the series:
    Li_n(z) = Σ_{k=1}^∞ z^k / k^n

    Converges for |z| ≤ 1 (with care at z = 1 for n = 1). -/
structure Polylog where
  /-- The order n of the polylogarithm -/
  order : ℕ
  /-- The argument z (coefficient-level model over `ℤ`). -/
  argument : ℤ
  /-- The convergence region -/
  convergenceRegion : PolylogConvergence
  /-- Convergence condition: for |z| = 1 we need order ≥ 2 -/
  converges : convergenceRegion = .insideUnitDisk ∨
    (convergenceRegion = .onUnitCircle true ∧ order ≥ 2)

namespace Polylog

/-- Li_1(z) for |z| < 1: Li_1(z) = -log(1-z) -/
def li1 : Polylog where
  order := 1
  argument := 0
  convergenceRegion := .insideUnitDisk
  converges := Or.inl rfl

/-- Li_2(z) - the dilogarithm, converges on unit circle too -/
def li2 : Polylog where
  order := 2
  argument := 1
  convergenceRegion := .onUnitCircle true
  converges := Or.inr ⟨rfl, le_refl 2⟩

/-- There is an admissible weight-`n` composition for every `n ≥ 2`.

    In the intended analytic picture this is the index appearing in `Li_n(1) = ζ(n)`,
    but this lemma only constructs the corresponding composition. -/
theorem polylog_one_has_admissible_index (n : ℕ) (hn : n ≥ 2) :
    ∃ s : Composition, s.weight = n ∧ s.isAdmissible := by
  refine ⟨[⟨n, by omega⟩], ?_, ?_⟩
  · simp [Composition.weight]
  · simp [Composition.isAdmissible, hn]

/-- Conjectural 5-term relation for Li_2 (Abel's identity).

    The relation is expressed against an abstract evaluator `Li2 : ℚ → ℚ`,
    so proof obligations are explicit and no tautological placeholder is used. -/
def dilog_five_term_conjecture (Li2 : ℚ → ℚ) : Prop :=
  ∀ x y : ℚ, x * y ≠ 1 →
    Li2 x + Li2 y + Li2 ((1 - x) / (1 - x * y)) + Li2 (1 - x * y) +
      Li2 ((1 - y) / (1 - x * y)) = 0

/-- Conjectural inversion formula:
    `Li_n(-1/z) = (-1)^(n-1) Li_n(-z)` up to lower-weight correction terms. -/
def polylog_inversion_conjecture (Li : ℕ → ℚ → ℚ) : Prop :=
  ∀ n : ℕ, ∀ z : ℚ, z ≠ 0 →
    Li n (-(1 / z)) = ((-1 : ℚ) ^ (n - 1)) * Li n (-z)

/-- Conjectural duplication formula:
    `Li_n(z) + Li_n(-z) = 2^(1-n) Li_n(z^2)`. -/
def polylog_duplication_conjecture (Li : ℕ → ℚ → ℚ) : Prop :=
  ∀ n : ℕ, ∀ z : ℚ,
    Li n z + Li n (-z) = ((1 : ℚ) / ((2 : ℚ) ^ (n - 1))) * Li n (z * z)

end Polylog

/-! ## Multiple Polylogarithms -/

/-- A multiple polylogarithm Li_{s₁,...,sₖ}(z₁,...,zₖ).

    Defined by:
    Li_s(z) = Σ_{n₁>...>nₖ≥1} z₁^{n₁}...zₖ^{nₖ} / (n₁^{s₁}...nₖ^{sₖ})

    The composition s = (s₁,...,sₖ) gives the "exponents" (depths).
    The arguments z = (z₁,...,zₖ) give the "twists".

    Convergence: When all |zᵢ| ≤ 1, convergence is equivalent to
    the composition being admissible (s₁ ≥ 2) when z₁ = 1. -/
structure MultiplePolylog where
  /-- The index composition -/
  indices : Composition
  /-- The arguments as integer parameters. -/
  arguments : List ℤ
  /-- Lengths must match -/
  lengths_eq : indices.length = arguments.length
  /-- Convergence is guaranteed by admissibility of the index composition
      when evaluating at unit arguments.
      We use isAdmissible as the key convergence criterion. -/
  converges : indices.isAdmissible

namespace MultiplePolylog

/-- Weight of the multiple polylogarithm = sum of indices -/
def weight (L : MultiplePolylog) : ℕ := L.indices.weight

/-- Depth of the multiple polylogarithm = number of indices -/
def depth (L : MultiplePolylog) : ℕ := L.indices.depth

/-- At unit arguments z = (1,...,1), get MZV:
    Li_s(1,...,1) = ζ(s₁,...,sₖ) -/
def at_unit_arguments (s : Composition) (_hs : s.isAdmissible) : Prop :=
  ∃ L : MultiplePolylog, L.indices = s ∧ L.arguments = List.replicate s.length (1 : ℤ)

/-- Conjectural shuffle product for multiple polylogarithms.

    `shuffleExpand` models the formal shuffle expansion on indices/arguments,
    and `eval` is the (analytic) value map to be formalized later. -/
def shuffle_product_conjecture
    (eval : MultiplePolylog → ℚ)
    (shuffleExpand : MultiplePolylog → MultiplePolylog → List MultiplePolylog) : Prop :=
  ∀ L₁ L₂ : MultiplePolylog,
    eval L₁ * eval L₂ = List.sum ((shuffleExpand L₁ L₂).map eval)

/-- Conjectural stuffle product for multiple polylogarithms. -/
def stuffle_product_conjecture
    (eval : MultiplePolylog → ℚ)
    (stuffleExpand : MultiplePolylog → MultiplePolylog → List MultiplePolylog) : Prop :=
  ∀ L₁ L₂ : MultiplePolylog,
    eval L₁ * eval L₂ = List.sum ((stuffleExpand L₁ L₂).map eval)

end MultiplePolylog

/-! ## Harmonic Polylogarithms (HPLs) -/

/-- The HPL alphabet: {0, 1, -1} -/
inductive HPLLetter : Type
  | zero : HPLLetter
  | one : HPLLetter
  | minusOne : HPLLetter
  deriving DecidableEq, Repr

/-- An HPL word -/
abbrev HPLWord := List HPLLetter

/-- A harmonic polylogarithm H(w; x).

    For a word w = (a₁,...,aₙ) with aᵢ ∈ {0, 1, -1}:
    H(w; x) = ∫₀ˣ f_{a₁}(t) H(a₂,...,aₙ; t) dt

    where f_0(t) = 1/t, f_1(t) = 1/(1-t), f_{-1}(t) = 1/(1+t) -/
structure HarmonicPolylog where
  /-- The word/weight vector -/
  word : HPLWord
  /-- The argument as an integer parameter. -/
  argument : ℤ

namespace HarmonicPolylog

/-- The weight of an HPL is the length of its word -/
def weight (H : HarmonicPolylog) : ℕ := H.word.length

/-- Count trailing zeros (for checking convergence) -/
def trailingZeros (H : HarmonicPolylog) : ℕ :=
  H.word.reverse.takeWhile (· == HPLLetter.zero) |>.length

/-- HPL is convergent at x = 1 if word doesn't start with 1 -/
def convergentAtOne (H : HarmonicPolylog) : Prop :=
  H.word.head? ≠ some HPLLetter.one

/-- Conjectural shuffle product for HPLs. -/
def hpl_shuffle_product_conjecture
    (eval : HarmonicPolylog → ℚ)
    (shuffleExpand : HarmonicPolylog → HarmonicPolylog → List HarmonicPolylog) : Prop :=
  ∀ H₁ H₂ : HarmonicPolylog,
    eval H₁ * eval H₂ = List.sum ((shuffleExpand H₁ H₂).map eval)

/-- Conjectural reduction of convergent HPLs at `x = 1` to colored MZVs. -/
def hpl_at_one_conjecture
    (toWeightAtOne : HarmonicPolylog → ℕ) : Prop :=
  ∀ H : HarmonicPolylog,
    convergentAtOne H → toWeightAtOne H = H.weight

/-- Conjectural transformation law under `x ↦ 1 - x`. -/
def hpl_complement_conjecture
    (eval : HarmonicPolylog → ℚ)
    (complement : HarmonicPolylog → HarmonicPolylog)
    (correction : HarmonicPolylog → ℚ) : Prop :=
  ∀ H : HarmonicPolylog, eval (complement H) = eval H + correction H

/-- Conjectural transformation law under `x ↦ -x`. -/
def hpl_negate_conjecture
    (eval : HarmonicPolylog → ℚ)
    (negate : HarmonicPolylog → HarmonicPolylog)
    (sign : HarmonicPolylog → ℚ) : Prop :=
  ∀ H : HarmonicPolylog, eval (negate H) = sign H * eval H

/-- Conjectural transformation law under `x ↦ 1/x`. -/
def hpl_invert_conjecture
    (eval : HarmonicPolylog → ℚ)
    (invert : HarmonicPolylog → HarmonicPolylog)
    (correction : HarmonicPolylog → ℚ) : Prop :=
  ∀ H : HarmonicPolylog, H.argument ≠ 0 → eval (invert H) = eval H + correction H

end HarmonicPolylog

/-! ## Nielsen Polylogarithms -/

/-- Nielsen generalized polylogarithm S_{n,p}(z).

    S_{n,p}(z) = ((-1)^{n+p-1} / ((n-1)!p!)) ∫₀¹ log^{n-1}(t) log^p(1-zt) dt/t

    Special cases:
    - S_{n,1}(z) = Li_{n+1}(z)
    - S_{1,p}(z) = (-1)^p ∫₀¹ log^p(1-zt) dt/t -/
structure NielsenPolylog where
  /-- Index n -/
  n : ℕ
  /-- Index p -/
  p : ℕ
  /-- Argument z -/
  argument : ℤ

namespace NielsenPolylog

/-- Conjectural identity `S_{n,1}(z) = Li_{n+1}(z)`. -/
def nielsen_n1_conjecture
    (Sval : ℕ → ℕ → ℚ → ℚ)
    (Li : ℕ → ℚ → ℚ) : Prop :=
  ∀ n : ℕ, ∀ z : ℚ, Sval n 1 z = Li (n + 1) z

/-- Weight of Nielsen polylog is n + p -/
def weight (S : NielsenPolylog) : ℕ := S.n + S.p

end NielsenPolylog

/-! ## Colored MZVs -/

/-- A root of unity (N-th root). -/
structure RootOfUnity where
  /-- Order N -/
  order : ℕ+
  /-- Index k (represents ζ_N^k) -/
  index : Fin order

/-- Colored MZV ζ(s₁,...,sₖ; ε₁,...,εₖ) where εᵢ are roots of unity.

    ζ(s; ε) = Σ_{n₁>...>nₖ≥1} ε₁^{n₁}...εₖ^{nₖ} / (n₁^{s₁}...nₖ^{sₖ})

    For N-th roots of unity, these are called "colored MZVs" or
    "multiple polylogarithms at roots of unity".

    Convergence requires the index composition to be admissible (s₁ ≥ 2)
    when the first root of unity is 1. -/
structure ColoredMZV where
  /-- The indices -/
  indices : Composition
  /-- The colors (roots of unity) -/
  colors : List RootOfUnity
  /-- Lengths match -/
  lengths_eq : indices.length = colors.length
  /-- Convergence condition: use the admissibility of the index composition.
      This ensures convergence when evaluating the series. -/
  isAdmissible : indices.isAdmissible

namespace ColoredMZV

/-- Weight = sum of indices -/
def weight (ζ : ColoredMZV) : ℕ := ζ.indices.weight

/-- Depth = number of indices -/
def depth (ζ : ColoredMZV) : ℕ := ζ.indices.depth

/-- Conjectural reduction at trivial colors (all colors `= 1`) to standard MZVs. -/
def at_trivial_colors_conjecture
    (evalColored : ColoredMZV → ℚ)
    (evalMZV : Composition → ℚ) : Prop :=
  ∀ ζ : ColoredMZV,
    (∀ c ∈ ζ.colors, c.order = ⟨1, by omega⟩) →
      evalColored ζ = evalMZV ζ.indices

/-- Euler sums: colors from {1, -1} -/
def isEulerSum (ζ : ColoredMZV) : Prop :=
  ∀ c ∈ ζ.colors, c.order = ⟨2, by omega⟩

/-- Conjectural distribution relation for colored MZVs. -/
def distribution_relation_conjecture
    (evalColored : ColoredMZV → ℚ)
    (distribute : ℕ → ColoredMZV → List ColoredMZV) : Prop :=
  ∀ N : ℕ, ∀ ζ : ColoredMZV,
    evalColored ζ = List.sum ((distribute N ζ).map evalColored)

end ColoredMZV

/-! ## Functional Equations -/

/-- Conjectural monodromy constraint for polylogarithms around `0,1,∞`. -/
def polylog_monodromy_conjecture
    (monodromy0 monodromy1 monodromyInf : Polylog → Polylog) : Prop :=
  ∀ P : Polylog, monodromyInf (monodromy1 (monodromy0 P)) = P

/-- Conjectural Bloch-Wigner five-term relation. -/
def bloch_wigner_five_term_conjecture (D : ℚ → ℚ) : Prop :=
  ∀ z : ℚ, z ≠ 0 → z ≠ 1 →
    D z + D (1 - z) + D ((z - 1) / z) + D (1 / (1 - z)) + D (z / (z - 1)) = 0

/-! ## Connection to K-theory -/

/-- Formal generator [z] of the pre-Bloch group for z ∈ ℚ \ {0,1}.

    The Bloch group B(F) is the kernel of δ : ℤ[F \ {0,1}] → Λ²(F×)
    where δ([z]) = z ∧ (1-z), quotiented by the five-term relation.

    Proper formalization would require:
    - The free abelian group on F \ {0,1}
    - The boundary map δ
    - The five-term relation as a quotient
    - Connection to K₃(F) via Bloch-Suslin

    This structure records formal generators with the exclusion constraint. -/
structure PreBlochGenerator where
  /-- The element z -/
  value : ℚ
  /-- z ≠ 0 -/
  ne_zero : value ≠ 0
  /-- z ≠ 1 -/
  ne_one : value ≠ 1

/-- Formal element of the pre-Bloch group: a ℤ-linear combination of generators. -/
abbrev PreBlochGroup := List (ℤ × PreBlochGenerator)

/-- The five-term relation in the pre-Bloch group.

    For x, y with x ≠ y and appropriate non-degeneracy:
    [x] - [y] + [y/x] - [(1-x⁻¹)/(1-y⁻¹)] + [(1-x)/(1-y)] = 0

    This records both the existence of the auxiliary generators
    (with the correct values) AND that the signed formal sum
    evaluates to zero under any additive evaluation map `ev`. -/
def BlochFiveTermRelation (x y : PreBlochGenerator) (_hxy : x.value ≠ y.value)
    (ev : PreBlochGenerator → ℚ) : Prop :=
  ∃ g₃ g₄ g₅ : PreBlochGenerator,
    g₃.value = y.value / x.value ∧
    g₄.value = (1 - x.value⁻¹) / (1 - y.value⁻¹) ∧
    g₅.value = (1 - x.value) / (1 - y.value) ∧
    -- The actual five-term relation: [x] - [y] + [y/x] - [g₄] + [g₅] = 0
    ev x - ev y + ev g₃ - ev g₄ + ev g₅ = 0

/-- Conjectural rank form of Borel's theorem:
    `rank K_{2n-1}(ℤ) = 1` for `n ≥ 2`. -/
def borel_theorem_conjecture (rankK : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 2 → rankK (2 * n - 1) = 1

end StringAlgebra.MZV
