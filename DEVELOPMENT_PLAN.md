# StringAlgebra-MZV Comprehensive Development Plan

Date: 2026-02-26

## 1. Objective and Quality Bar

The target is to turn `StringAlgebra-MZV` from an interface-heavy scaffold into a theorem-heavy Lean development where mathematically significant claims are represented as theorems with explicit proof obligations.

Quality bar:

1. No semantic placeholder shells for major mathematical results (`def ... : Prop := ...` used as theorem stand-ins).
2. Open mathematics is tracked as explicit theorem obligations with `sorry` (temporarily), never hidden in structures/definitions.
3. Every merged proof should be backed by reproducible module-scoped build checks.
4. Conjectures remain clearly marked as conjectures and separated from proved theorems.

## 2. Current State (Gap Summary)

1. Core combinatorial infrastructure exists (`Basic`, `ShuffleAlgebra`, `StuffleAlgebra`) with real recursive proofs.
2. Most high-level MZV, motivic, polylog, and associator claims are specification-level shells.
3. Documentation currently over-emphasizes "0 sorry" while under-emphasizing unresolved theorem obligations.

## 3. Workstreams

## WS-A. Placeholder Elimination and Truthful Statusing

Goal: remove theorem-shell pattern and make proof debt explicit.

Tasks:

1. Convert theorem-like `def ... : Prop` declarations into `theorem` statements.
2. Use `by sorry` at theorem sites where infrastructure is still missing.
3. Keep definitional predicates (`isAdmissible`, `isLyndon`, etc.) as `def`.
4. Update `README.md` and `TODO.md` to report both:
   - theorem-level `sorry` count
   - theorem-shell (`def ... : Prop`) count for theorem-like names

Acceptance criteria:

1. `rg -n '^\s*def\s+.*(theorem|conjecture|formula|relation)\b.*:\s*Prop\s*:=' StringAlgebra/MZV --glob '*.lean'` returns only intentionally definitional exceptions.
2. Remaining open obligations appear only as theorem/lemma `sorry` sites.

## WS-B. Algebraic Core Closure

Goal: finish core algebra on shuffle/stuffle structures.

Tasks:

1. Prove full associativity theorems for shuffle and stuffle expansions.
2. Prove distributivity/bilinearity for formal sums after normalization.
3. Add canonical normal-form lemmas for `FormalSum.normalize`.

Acceptance criteria:

1. `shuffle_assoc` and `stuffle_assoc` are theorem-level and proved.
2. Formal-sum product lemmas are usable without rewriting by hand.

## WS-C. Double-Shuffle Derivation Pipeline

Goal: derive nontrivial low-weight relations from implemented products.

Tasks:

1. Formalize admissible/non-admissible split and regularization compatibility lemmas.
2. Prove weight-3 and weight-4 finite double-shuffle consequences in theorem form.
3. Tie Ihara derivation actions to explicit relation generation lemmas.

Acceptance criteria:

1. At least 3 concrete nontrivial double-shuffle relation theorems proved from core definitions.
2. No relation theorem is only a type alias to a `Prop` shell.

## WS-D. Iterated Integral and Polylog Bridge

Goal: establish a real bridge between form words and polylog/MZV statements.

Tasks:

1. Strengthen conversion theorems and partial inverse properties.
2. Formalize convergent-word conditions and duality transfer lemmas.
3. Replace arithmetic tautology placeholders in `Polylogarithm.lean` with properly scoped theorem goals.

Acceptance criteria:

1. Polylog functional-equation entries are either proved theorems or explicit theorem obligations with non-tautological statements.
2. Bridge lemmas are used by at least one downstream relation proof.

## WS-E. Motivic Hopf Layer

Goal: upgrade motivic layer from shape checks to structural proofs.

Tasks:

1. Replace length-based coaction theorems with algebraic compatibility statements.
2. Prove depth filtration monotonicity and basic period-map interaction lemmas.
3. Keep period conjecture clearly marked as conjectural, separated from proved results.

Acceptance criteria:

1. Coaction theorems express algebraic behavior, not list-length invariants.
2. Motivic section has explicit proved-vs-open partition.

## WS-F. Associator/GT Layer

Goal: retain formal interfaces while preventing false completion signals.

Tasks:

1. Move high-level claims (pentagon/hexagon consequences, GT bridges) into theorem obligations.
2. Add a minimal proved kernel (normalization, low-degree coefficient identities that are genuinely derivable).
3. Mark external-depth statements as open obligations or conjectures.

Acceptance criteria:

1. No fake “completed” impression from tautological equalities.
2. Associator file starts with proved kernel and ends with open theorem obligations.

## 4. Implementation Sequence (Dependency-Aware)

1. WS-A first: make debt explicit.
2. WS-B second: stabilize algebraic base.
3. WS-C third: derive concrete relations.
4. WS-D in parallel with WS-C when bridge lemmas are needed.
5. WS-E after WS-B/WS-C.
6. WS-F last, once motivic and double-shuffle infrastructure is usable.

## 5. Validation Protocol

For each PR-sized step:

1. Run module-scoped builds only (no bare `lake build`):
   - `lake build StringAlgebra.MZV.Basic`
   - `lake build StringAlgebra.MZV.ShuffleAlgebra`
   - etc.
2. Run debt audits:
   - `rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean'`
   - `rg -n '^\s*def\s+.*(theorem|conjecture|formula|relation)\b.*:\s*Prop\s*:=' StringAlgebra/MZV --glob '*.lean'`
3. Update debt counts in `TODO.md` whenever counts change.

## 6. Two-Week Tactical Plan

Week 1:

1. Complete WS-A conversion for `Relations`, `DoubleShuffle`, `Motivic`, `Associator`, `Polylogarithm`.
2. Land truthful status updates in `README.md` and `TODO.md`.
3. Prove any low-hanging theorem obligations already implied by current definitions.

Week 2:

1. Prove `shuffle_assoc`/`stuffle_assoc` (or decompose into helper lemmas with partial closure).
2. Prove first two finite double-shuffle low-weight relations.
3. Replace one full section of polylog tautology placeholders with meaningful theorem statements.

## 7. Non-Negotiable Rules

1. No axiom introduction for MZV theorem debt.
2. No burying proof obligations inside structure fields.
3. No claims of completion based solely on absence of `sorry`.
4. Open obligations must be explicit theorem statements.
