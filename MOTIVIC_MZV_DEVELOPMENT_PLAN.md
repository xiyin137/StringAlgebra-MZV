# Comprehensive Development Plan: Motivic MZV Formalization

Date: 2026-02-26
Last updated: 2026-02-27 (absorbed `claude_to_codex.md` directives)
Target module: `StringAlgebra/MZV/Motivic.lean`
Dependencies: `Basic`, `ShuffleAlgebra`, `StuffleAlgebra`, `DoubleShuffle`, `Relations`, `IteratedIntegral`, `Polylogarithm`.

## 1. Mission

Deliver a mathematically credible Lean development of motivic multiple zeta values that:

1. Reflects the proof architecture in Brown’s work.
2. Exposes unresolved mathematics as explicit theorem obligations.
3. Avoids semantic placeholders for major theorems.
4. Supports downstream associator and double-shuffle development.

## 2. Design Principles

1. Proof debt must appear in theorem statements (`theorem ... := by sorry` while open), not hidden in `def ... : Prop` shells.
2. Conjectures remain first-class and explicitly marked conjectural.
3. Foundational structures (graded/filtered/coaction) are formalized before high-level theorem statements.
4. Every phase has objective acceptance tests.

## 2.1 Incorporated Directives from `claude_to_codex.md` (2026-02-27)

This plan now explicitly adopts the review conclusions as hard constraints:

1. Repository-wide semantic placeholder cleanup is mandatory before claiming progress on deep theorems.
2. Low-weight matrix expansions based on the current add-at-position `iharaDerivComp` model are frozen.
3. The derivation layer must be rebuilt from coaction-extraction maps that lower weight, matching Brown’s program.
4. Existing reusable infrastructure is preserved and reused: `LevelMatrixBlock`, `BrownLevelDerivationStep`, `CertifiedStep`, indexed-family/finitary development APIs.
5. `native_decide` usage is gradually replaced by kernel-checked proofs (`decide`, `simp`, explicit lemmas) unless computation scale justifies an exception.
6. `MotivicMZV` grading metadata (`weight`, `depth`) must become invariant-backed or computed, not unchecked annotations.
7. Typeclass integration (`AddCommMonoid`, `Module`, eventual `Ring`/`Algebra`) is treated as core infrastructure, not optional polish.
8. Basis blocks must gain completeness guarantees (generation algorithm + correctness theorem), not only manually curated lists.
9. Build/test discipline follows module-targeted builds plus debt audits at each merge step.

## 3. Work Breakdown Structure

## Phase 0: Baseline and Debt Transparency

Goal:

1. Produce an honest baseline for formalization status across the full MZV stack.

Tasks:

1. Inventory theorem-like proposition shells across `StringAlgebra/MZV/*.lean`.
2. Delete semantically vacuous shells that encode tautologies while claiming deep content.
3. Convert mathematically intended claims into `theorem ... := by sorry` obligations until proved.
4. Tag conjectural statements consistently (`*_conjecture`) with mathematically faithful bodies.
5. Add module header sections: `Proved`, `Open obligations`, `Conjectures`.

Deliverables:

1. Refactored signatures across the MZV modules.
2. Updated debt counts in project notes.

Acceptance criteria:

1. No theorem-like claim remains as silent `def ... : Prop := ...` placeholder.
2. Open claims are searchable by theorem names and `sorry` locations.

## Phase 0.5: Derivation Correctness Reset (Critical Path Gate)

Goal:

1. Replace the current wrong-direction derivation scaffold with Brown-compatible coaction-derived maps.

Tasks:

1. Freeze further expansion of low-weight derivation matrix families based on add-at-position derivations.
2. Specify coaction-cut extraction operators defining candidate `∂_{2n+1}` maps that lower weight.
3. Prove direction/weight behavior and compatibility lemmas for the new derivation definition.
4. Build compatibility shims so existing matrix/certification infrastructure can be reused with corrected maps.
5. Mark legacy derivation pipeline as provisional/testing-only until replaced.

Deliverables:

1. Corrected derivation API with explicit weight-lowering semantics.
2. Migration notes from legacy derivation interfaces.

Acceptance criteria:

1. No new Brown-step theorem depends on the legacy add-at-position derivation semantics.
2. At least one nontrivial low-weight step is rebuilt using the corrected derivation API.

## Phase 1: Algebraic Kernel for Motivic Objects

Goal:

1. Replace ad hoc representations with reusable algebraic primitives.

Tasks:

1. Define proper structures for graded objects and weight/depth compatibility.
2. Define tensor-side operations needed for coaction algebra.
3. Prove basic ring/module laws for `MotivicMZV` operations.
4. Separate syntactic representations (lists) from semantic equivalence (`normalize`/quotients).

Deliverables:

1. `Motivic/Core`-style reusable definitions.
2. Lemma set for additive/multiplicative behavior.

Acceptance criteria:

1. No critical theorem depends on raw list shape artifacts.
2. Coaction codomain supports algebraic operations needed by coassociativity proofs.

## Phase 2: Coaction Infrastructure

Goal:

1. Implement mathematically meaningful coaction API.

Tasks:

1. Define coaction map and its algebraic target with explicit multiplication/composition.
2. State coassociativity as `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` in formal terms.
3. State multiplicativity as `Δ(x*y) = Δ(x) ⋅ Δ(y)` in formal terms.
4. Prove depth-1 cases rigorously, then general extension lemmas.

Deliverables:

1. Coaction theorem set replacing current `length = 2` surrogates.

Acceptance criteria:

1. Coaction theorems no longer reduce to list-length checks.
2. Theorems can be consumed by double-shuffle compatibility lemmas.

## Phase 3: Derivations and Infinitesimal Coaction Layer

Goal:

1. Build the `∂_{2n+1}` machinery central to Brown’s proof strategy.

Tasks:

1. Define indecomposable projection / graded extraction operators.
2. Define derivations induced by coaction pieces.
3. Prove derivation laws (Leibniz-type) and depth/level lowering behavior.
4. Replace legacy `iharaDerivComp`-driven interfaces with mathematically correct coaction-derived maps.
5. Preserve a thin compatibility layer only where needed for transition.

Deliverables:

1. Derivation API and compatibility theorems.

Acceptance criteria:

1. Derivations are formally linked to coaction, not standalone syntactic maps.
2. Level/depth reduction lemmas are available for induction arguments.

## Phase 4: Filtrations and Associated Graded Objects

Goal:

1. Implement level/depth filtrations needed for Brown-style inductive proofs.

Tasks:

1. Define level filtration for `{2,3}` words/compositions.
2. Define depth filtration for motivic algebra and quotient by `ζ(2)` where required.
3. Define associated graded spaces and canonical projection maps.
4. Prove monotonicity and compatibility with coaction/derivations.

Deliverables:

1. `Filtration` and `Graded` theorem layer.

Acceptance criteria:

1. Induction on level is executable in Lean with explicit helper lemmas.
2. Depth-graded statements can be expressed without ad hoc rewriting.

## Phase 5: Brown 2012 Theorem Track (Hoffman Basis)

Goal:

1. Formal theorem path to motivic Hoffman basis in repository scope.

Tasks:

1. Formalize matrix representation of level-graded derivation maps.
2. Introduce coefficient system and valuation lemmas needed for invertibility criterion.
3. Prove injectivity of level-lowering maps.
4. Prove linear independence by induction on level.
5. Connect to dimension bounds to obtain basis statement.

Deliverables:

1. Theorem family corresponding to Brown’s Theorem 1.1 architecture.

Acceptance criteria:

1. `brown_structure_theorem` no longer shell-like; it is either proved or explicitly reduced to clearly scoped open lemmas.
2. All intermediary steps are formal theorems, not documentation claims.

## Phase 6: Decomposition Algorithm Track

Goal:

1. Formal exact-numerical decomposition workflow for motivic MZVs.

Tasks:

1. Define finite-weight basis records and truncations.
2. Implement recursive decomposition map from derivation data.
3. Prove soundness and basis-validation conditions.
4. Add low-weight worked examples as executable tests.

Deliverables:

1. `Decomposition` module with correctness theorems.

Acceptance criteria:

1. Given a validated basis up to weight `N`, decomposition of test elements is provably correct.
2. Failure modes are explicit (basis not isomorphism).

## Phase 7: Depth-Graded / Linearized Double Shuffle Track

Goal:

1. Build bridge to Brown 2013 depth-graded structure.

Tasks:

1. Formalize linearized double-shuffle equation space and bracket closure.
2. Add depth-2/3 exact-sequence style lemmas where currently known.
3. Define period-polynomial-to-depth4 map and prove linearized-shuffle satisfaction.
4. Keep motivicity of exceptional depth-4 elements as conjectural if not proved.

Deliverables:

1. Depth-graded module with proven low-depth content and explicit conjectural frontier.

Acceptance criteria:

1. Theorem-level distinction between proved linearized statements and conjectural motivicity.
2. No conflation of conjecture with theorem in code interfaces.

## Phase 8: Single-Valued Motivic Extension

Goal:

1. Add `sv` map and single-valued motivic MZV layer.

Tasks:

1. Formalize single-valued map from de Rham/unipotent period data.
2. Define `ζ_sv^m` and relation-preservation theorems.
3. Prove algebra closure and basic generation statements in low weights.

Deliverables:

1. `MotivicSingleValued.lean` or integrated section with clear dependencies.

Acceptance criteria:

1. `sv` map is theorem-backed and not just postulated.
2. Single-valued relation preservation is theorem-level.

## 4. Dependency Graph for Execution

Execution order:

1. Phase 0
2. Phase 0.5
3. Phase 1
4. Phase 2
5. Phase 3
6. Phase 4
7. Phase 5
8. Phase 6
9. Phase 7
10. Phase 8

Parallelization opportunities:

1. Phase 6 can start once Phase 3 APIs stabilize.
2. Phase 7 can start after Phase 4 with reduced scope (linearized side first).
3. Phase 8 can begin after Phase 2 if it uses only period/coaction interfaces.

## 5. Concrete Module Refactor Plan

Proposed structure:

1. `StringAlgebra/MZV/Motivic/Core.lean`
2. `StringAlgebra/MZV/Motivic/Coaction.lean`
3. `StringAlgebra/MZV/Motivic/Derivations.lean`
4. `StringAlgebra/MZV/Motivic/Filtration.lean`
5. `StringAlgebra/MZV/Motivic/HoffmanBasis.lean`
6. `StringAlgebra/MZV/Motivic/Decomposition.lean`
7. `StringAlgebra/MZV/Motivic/DepthGraded.lean`
8. `StringAlgebra/MZV/Motivic/SingleValued.lean`
9. `StringAlgebra/MZV/Motivic.lean` as façade import file

## 6. Acceptance Tests and Audit Commands

For each merge step:

1. Build only touched modules.
2. Run placeholder/debt audits.
3. Update theorem/proof-debt inventory.

Suggested commands:

1. `lake build StringAlgebra.MZV`
2. `rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean'`
3. `rg -n '^\s*def\s+.*(theorem|basis|coaction|filtration|conjecture|relation)\b.*:\s*Prop\s*:=' StringAlgebra/MZV --glob '*.lean'`
4. `rg -n '^theorem\s' StringAlgebra/MZV/Motivic*.lean`
5. `rg -n 'native_decide' StringAlgebra/MZV --glob '*.lean'`

## 7. Risk Register and Mitigations

Risk 1:

1. Coaction formalization complexity blocks all downstream phases.

Mitigation:

1. First prove depth-1 and truncated-weight versions; generalize incrementally.

Risk 2:

1. Quotient/normalization semantics for formal sums become brittle.

Mitigation:

1. Introduce canonical normalization lemmas and avoid theorem statements on raw list equality.

Risk 3:

1. Depth-graded exceptional-element motivicity remains out of current reach.

Mitigation:

1. Mark explicitly conjectural and isolate into separate theorem namespace.

Risk 4:

1. Scope creep from associator/physics layer obscures motivic core completion.

Mitigation:

1. Freeze cross-module dependencies until Phases 0-5 are stable.

Risk 5:

1. Continuing to extend proofs on the legacy derivation model creates large volumes of mathematically misaligned code.

Mitigation:

1. Enforce Phase 0.5 gate before any additional Brown-step expansion work.

## 8. 12-Week Execution Schedule

Weeks 1-2:

1. Phase 0 and Phase 0.5.
2. Refactor `Motivic.lean` into modular skeleton.

Weeks 3-4:

1. Phase 1 completion (grading invariants, algebraic instances).
2. Phase 2 completion for depth-1 and algebraic coaction APIs.

Weeks 5-6:

1. Phase 3 derivation machinery on corrected coaction-derived definitions.
2. Initial integration with `DoubleShuffle` derivation APIs.

Weeks 7-8:

1. Phase 4 filtrations and associated graded framework.
2. Low-weight examples for sanity.

Weeks 9-10:

1. Phase 5 Hoffman-basis theorem track (partial then full, depending on valuation lemmas).

Weeks 11-12:

1. Phase 6 decomposition algorithm.
2. Start Phase 7 depth-graded interfaces and identify explicit conjectural boundary.

## 9. Definition of Done (Motivic Core)

Motivic core is considered complete when:

1. Coaction, derivation, and filtration infrastructure are theorem-backed.
2. Brown-style Hoffman-basis theorem path is formalized to either completion or a small, explicit set of remaining theorem obligations.
3. No major motivic theorem claim is hidden as proposition shell.
4. Conjectures are separated and clearly marked.
