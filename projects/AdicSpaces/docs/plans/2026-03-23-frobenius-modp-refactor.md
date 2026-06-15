# Frobenius on A°/(p) — Class Refactor Plan

> **For agentic workers:** REQUIRED: Use superpowers:executing-plans to implement this plan.

**Goal:** Fill `frobenius_modP_surjective` sorry by refactoring `IsPerfectoidRing` to use Scholze's Definition 3.5 (Frobenius surjective on `A°/(p)`) instead of Wedhorn's formulation (Frobenius on `A°/(ϖ)`).

**Architecture:** Separate the pseudo-uniformizer data from the Frobenius condition. Add the p-Frobenius as a class field, derive the ϖ-Frobenius as a consequence. This gives clean API matching the standard mathematical reference.

**Rationale:** The conversion from ϖ-Frobenius to p-Frobenius requires a non-trivial p-adic convergence argument. By putting the stronger condition in the class (as Scholze does), downstream consumers get what they need directly, and the ϖ-Frobenius becomes a simple corollary.

---

## Design

### Current class (Wedhorn-style):
```
exists_pseudoUniformizer : ∃ ϖ,
  IsPowerBounded ϖ ∧
  (∃ c, IsPowerBounded c ∧ p = c * ϖ^p) ∧
  (∀ x, IsPowerBounded x → ∃ y z, IsPowerBounded y ∧ IsPowerBounded z ∧ x = y^p + ϖ*z)
```

### New class (Scholze-style):
```
exists_pseudoUniformizer : ∃ ϖ,
  IsPowerBounded ϖ ∧
  (∃ c, IsPowerBounded c ∧ p = c * ϖ^p)
frobenius_surj : ∀ x, IsPowerBounded x →
  ∃ y, IsPowerBounded y ∧ ∃ z, IsPowerBounded z ∧ x = y^p + p * z
```

The Frobenius condition now says `x ≡ y^p (mod p)`, not `x ≡ y^p (mod ϖ)`. This matches Scholze's Definition 3.5 and is what `surjective_fontaineTheta` needs.

### Derived lemma (new, easy):
```
perfectoidPseudoUniformizer_frobenius_surj_varpi : ... x = y^p + ϖ*z
```
This follows because `p*z = c*ϖ^p*z = ϖ*(c*ϖ^{p-1}*z)`, so `x = y^p + ϖ*(c*ϖ^{p-1}*z)`.

---

## Tasks

### Task 1: Refactor `IsPerfectoidRing` class

**File:** `Adic spaces/PerfectoidRing.lean`

- [ ] **Step 1:** Change `exists_pseudoUniformizer` to remove the Frobenius condition from the existential.

- [ ] **Step 2:** Add `frobenius_surj` as a new separate field:
```lean
frobenius_surj : ∀ x : A, IsPowerBounded x →
  ∃ y : A, IsPowerBounded y ∧ ∃ z : A, IsPowerBounded z ∧ x = y ^ p + (p : A) * z
```

- [ ] **Step 3:** Update `perfectoidPseudoUniformizer_frobenius_surj` to derive the old ϖ-formulation from the new p-formulation:
```
x = y^p + p*z = y^p + c*ϖ^p*z = y^p + ϖ*(c*ϖ^{p-1}*z)
```
Set `z' = c*ϖ^{p-1}*z` (power-bounded since c, ϖ, z are).

- [ ] **Step 4:** Verify PerfectoidRing.lean compiles.

### Task 2: Fix downstream — Tilting.lean `p_not_isUnit_in_powerBounded`

**File:** `Adic spaces/Tilting.lean`

The proof at line 139 uses `obtain ⟨ϖ, _, ⟨c, hc, hpc⟩, _⟩` — the `_` at the end discards the Frobenius. Since we moved Frobenius out of the existential, the pattern match changes.

- [ ] **Step 1:** Update the pattern match to `obtain ⟨ϖ, _, ⟨c, hc, hpc⟩⟩`.

- [ ] **Step 2:** Verify Tilting.lean compiles.

### Task 3: Fix downstream — PerfectoidRing.lean `isHausdorff_pIdeal` and `isPrecomplete_pIdeal`

**File:** `Adic spaces/PerfectoidRing.lean`

These proofs also destructure `exists_pseudoUniformizer`. Update the pattern matches.

- [ ] **Step 1:** Update all `obtain ⟨ϖ, hϖ_pb, ⟨c, hc_pb, hpc⟩, _⟩` patterns.

- [ ] **Step 2:** Verify PerfectoidRing.lean compiles.

### Task 4: Fill `frobenius_modP_surjective`

**File:** `Adic spaces/Tilting.lean`

With the new class field, the proof becomes straightforward:

- [ ] **Step 1:** Replace the sorry with a proof using `IsPerfectoidRing.frobenius_surj`.

The key: for any `x̄ ∈ A°/(p)`, lift to `x ∈ A°`, apply `frobenius_surj` to get `y ∈ A°` with `x - y^p ∈ (p)·A°`, so `x̄ = ȳ^p` in `A°/(p)`.

- [ ] **Step 2:** Verify Tilting.lean compiles with 0 errors.

- [ ] **Step 3:** Commit.

### Task 5: Verify full build

- [ ] **Step 1:** Run `lake env lean` on PerfectoidRing.lean and Tilting.lean.
- [ ] **Step 2:** Spot-check that ScottishBook problems using PerfectoidRing still compile.
- [ ] **Step 3:** Final commit with descriptive message.

---

## Impact

- `frobenius_modP_surjective`: **sorry → proved**
- `theta_surjective`: now depends on proved `frobenius_modP_surjective` → **effectively proved** (modulo `IsAdicComplete` which is nearly proved)
- API matches Scholze's standard formulation
- Old ϖ-Frobenius available as derived lemma
