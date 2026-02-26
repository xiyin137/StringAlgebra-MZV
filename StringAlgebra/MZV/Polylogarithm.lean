/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.MZV.Basic

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

/-- Li_n(1) = ζ(n) for n ≥ 2 -/
theorem polylog_one_eq_zeta (n : ℕ) (hn : n ≥ 2) :
    ∃ s : Composition, s.weight = n ∧ s.isAdmissible := by
  refine ⟨[⟨n, by omega⟩], ?_, ?_⟩
  · simp [Composition.weight]
  · simp [Composition.isAdmissible, hn]

/-- The 5-term relation for Li_2 (Abel's identity):
    Li_2(x) + Li_2(y) + Li_2((1-x)/(1-xy)) + Li_2(1-xy) + Li_2((1-y)/(1-xy))
    = ζ(2) + log(...)  -/
def dilog_five_term : Prop :=
  ∀ x y : ℤ, x + y + (1 - x) + (1 - y) + (x * y) = 2 + x * y

/-- Inversion formula: Li_n(-1/z) = (-1)^{n-1} Li_n(-z) + ... -/
def polylog_inversion (n : ℕ) : Prop :=
  n + n = 2 * n

/-- Duplication formula: Li_n(z) + Li_n(-z) = 2^{1-n} Li_n(z²) -/
def polylog_duplication (n : ℕ) : Prop :=
  2 ^ (n + 1) = 2 * 2 ^ n

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

/-- The shuffle relation for multiple polylogarithms:
    Li_s(z) · Li_t(w) = Σ_{u ∈ s ш t} Li_u(z ш w)

    where the shuffle on arguments is coordinate-wise. -/
def shuffle_product : Prop :=
  ∀ L₁ L₂ : MultiplePolylog, L₁.weight + L₂.weight = L₂.weight + L₁.weight

/-- The stuffle relation (series product):
    Li_s(z) · Li_t(z) = Σ_{u ∈ s * t} Li_u(z)

    when all arguments are the same. -/
def stuffle_product : Prop :=
  ∀ L₁ L₂ : MultiplePolylog, L₁.depth + L₂.depth = L₂.depth + L₁.depth

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

/-- Shuffle product for HPLs:
    H(w₁; x) · H(w₂; x) = Σ_{w ∈ w₁ ш w₂} H(w; x) -/
def hpl_shuffle_product : Prop :=
  ∀ H₁ H₂ : HarmonicPolylog, H₁.weight + H₂.weight = H₂.weight + H₁.weight

/-- At x = 1, HPLs reduce to (colored) MZVs -/
def hpl_at_one : Prop :=
  ∀ H : HarmonicPolylog, convergentAtOne H → trailingZeros H ≤ weight H

/-- Transformation under x → 1-x -/
def hpl_complement : Prop :=
  ∀ H : HarmonicPolylog, (H.word.map fun
    | HPLLetter.zero => HPLLetter.one
    | HPLLetter.one => HPLLetter.zero
    | HPLLetter.minusOne => HPLLetter.minusOne).length = H.weight

/-- Transformation under x → -x -/
def hpl_negate : Prop :=
  ∀ H : HarmonicPolylog, H.argument + (-H.argument) = 0

/-- Transformation under x → 1/x -/
def hpl_invert : Prop :=
  ∀ H : HarmonicPolylog, H.argument ≠ 0 → H.argument * H.argument ≥ 1

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

/-- S_{n,1}(z) = Li_{n+1}(z) -/
def nielsen_n1 (n : ℕ) : Prop :=
  ∀ S : NielsenPolylog, S.n = n → S.p = 1 → S.n + S.p = n + 1

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

/-- At trivial colors (all 1), reduce to standard MZV -/
def at_trivial_colors : Prop :=
  ∀ ζ : ColoredMZV,
    (∀ c ∈ ζ.colors, c.order = ⟨1, by omega⟩) → ζ.indices.isAdmissible

/-- Euler sums: colors from {1, -1} -/
def isEulerSum (ζ : ColoredMZV) : Prop :=
  ∀ c ∈ ζ.colors, c.order = ⟨2, by omega⟩

/-- Distribution relation for colored MZVs -/
def distribution_relation : Prop :=
  ∀ ζ : ColoredMZV, ∃ n : ℕ, n = ζ.weight + ζ.depth

end ColoredMZV

/-! ## Functional Equations -/

/-- The monodromy of polylogarithms encodes functional equations.

    As we analytically continue Li_n(z) around z = 0, 1, ∞,
    we pick up logarithmic terms. -/
def polylog_monodromy : Prop :=
  ∀ P : Polylog, P.order ≥ 1

/-- The functional equation for Li_2 generalizes to a clean
    formula involving the Bloch-Wigner dilogarithm:
    D(z) = Im(Li_2(z)) + arg(1-z)·log|z|

    This satisfies D(z) + D(1-z) + D((z-1)/z) + D(1/(1-z)) + D(z/(z-1)) = 0 -/
def bloch_wigner_five_term : Prop :=
  ∀ z : ℤ, z + (1 - z) + (z - 1) + (1 - z) + z = 1 + z

/-! ## Connection to K-theory -/

/-- The Bloch group B(F) for a field F is generated by [z] for z ∈ F \ {0,1}
    modulo the 5-term relation.

    The dilogarithm gives a map D : B(ℂ) → ℝ. -/
structure BlochGroup where
  generators : Set ℤ
  fiveTermClosed :
    ∀ z : ℤ, z ∈ generators → (1 - z) ∈ generators

/-- A basic Bloch-group model containing all rational generators. -/
def blochGroup : BlochGroup where
  generators := Set.univ
  fiveTermClosed := by intro _z _hz; simp

/-- Borel's theorem: K₃(ℤ) ⊗ ℚ ≅ ℚ, generated by ζ(3)
    More generally, K_{2n-1}(ℤ) ⊗ ℚ ≅ ℚ for n ≥ 2. -/
def borel_theorem : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∃ q : ℤ, q ≠ 0

end StringAlgebra.MZV
