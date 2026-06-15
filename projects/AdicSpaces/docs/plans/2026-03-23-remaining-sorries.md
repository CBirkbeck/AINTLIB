# Remaining Theory Sorry's — Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill as many theory-file sorry's as possible, reducing from 20 sorry's across 4 files to a minimal set of genuine "deep theorem" sorry's.

**Architecture:** Prioritize sorry's that have mathlib API support, then those needing moderate proof work, then document the rest as intentional placeholders for research-level results.

**Tech Stack:** Lean 4, Mathlib v4.29.0-rc3. Key APIs: `WittVector.fontaineTheta`, `surjective_fontaineTheta`, `frobenius`, `ModP`, `SModEq`, `IsAdicComplete`.

---

## Current Sorry Inventory (20 total)

| File | Sorry | Type | Fillable? |
|------|-------|------|-----------|
| **PerfectoidRing.lean** | `isPrecomplete_pIdeal` SModEq step | Proof | HARD — needs closedness of p^n·A° |
| **PerfectoidRing.lean** | `toIsStablyUniform` | Deep theorem | NO — research level |
| **PerfectoidRing.lean** | `toIsSheafy` | Deep theorem | NO — follows from stably uniform |
| **Tilting.lean** | `theta_surjective` Frobenius | Proof | YES — from perfectoid condition |
| **Tilting.lean** | `ker_theta_principal` | Deep theorem | MAYBE — needs Witt vector work |
| **Tilting.lean** | `tilt_admits_perfectoid_structure` | Construction | NO — needs PreTilt topology |
| **Tilting.lean** | `tilt_isField` | Proof | MAYBE — from valuation ring structure |
| **Tilting.lean** | `tiltingEquiv` | Deep theorem | NO — depends on tilt topology |
| **PerfectoidSpace.lean** | `toAffinoidAdicSpace` | Proof | NO — needs toIsSheafy |
| **PerfectoidSpace.lean** | `toAdicSpace` | Proof | NO — needs above |
| **PerfectoidSpace.lean** | `PerfectoidSpace.tilt` | Construction | NO — needs tilt topology |
| **CompletedAlgClosure.lean** | 9 sorry's | Axiomatized | NO — by design (PUnit placeholder) |

---

## Execution Plan

### Task 1: Fill `theta_surjective` — Frobenius on A°/(p) [FILLABLE]

**File:** `Adic spaces/Tilting.lean:237-242`

The sorry needs: `Function.Surjective (frobenius (ModP A° p) p)`.

**Mathematical proof:**
- `ModP A° p = A° ⧸ Ideal.span {p}` and `frobenius` is `x ↦ x^p`.
- Need: for every `x̄ ∈ A°/(p)`, exists `ȳ` with `ȳ^p = x̄`, i.e., `x - y^p ∈ (p)`.
- The perfectoid condition gives: `x = y^p + ϖ·z` (Frobenius surj on `A°/(ϖ)`).
- So `x - y^p = ϖ·z`. Need `ϖ·z ∈ (p)·A°`.
- Iterate the perfectoid condition p times on the remainder:
  `x = y₀^p + ϖ·y₁^p + ϖ²·y₂^p + ... + ϖ^{p-1}·y_{p-1}^p + ϖ^p·z_{p-1}`.
- In `A°/(p)`: since `p = c·ϖ^p`, we have `c·ϖ^p = 0 mod (p)`.
- Key: `(y₀ + ϖ·y₁ + ... + ϖ^{p-1}·y_{p-1})^p ≡ y₀^p + ϖ^p·y₁^p + ... mod p`
  (by Freshman's dream in char p... but A°/(p) might not have char p if p is not prime in A°).

**Simpler approach:** Work in `A°/(p)` where `CharP (A°/(p)) p` holds. Use Frobenius = x^p. The perfectoid condition on `A°/(ϖ)` implies it on `A°/(p)` because:
- Lift `x̄ ∈ A°/(p)` to `x ∈ A°`
- Apply perfectoid: `x = y^p + ϖ·z` in A°
- In A°/(p): `x̄ = ȳ^p + ϖ̄·z̄`
- Since `p = c·ϖ^p`, in A°/(p): `c̄·ϖ̄^p = 0`.
- If we can show `ϖ̄ ∈ nilradical(A°/(p))`, then iterating gives `ϖ̄^N = 0` for some N.
- Actually `ϖ^p·c = p`, so `ϖ^p ∈ (p)·c^{-1}·A°`... but c^{-1} might not exist.
- Better: `ϖ^p = p · c^{-1}` in A (since c is a unit candidate). Actually c is just power-bounded.

**Most pragmatic approach:** Prove `Ideal.span {(ϖ : A°)} ≤ Ideal.span {(p : A°)}` or vice versa, then use the quotient map. If `(p) ⊆ (ϖ^p) ⊆ (ϖ)`, then A°/(ϖ) is a quotient of A°/(p), and Frobenius surjectivity lifts.

Wait — that gives surjectivity on A°/(ϖ) FROM A°/(p), not the reverse. We need the reverse.

**Correct approach:** Use `Ideal.Quotient.lift` to show the Frobenius on A°/(p) is surjective by explicitly constructing the lift. For each `x ∈ A°`:
1. Apply perfectoid condition: `x = y^p + ϖ·z`
2. `ϖ^p | p` means `ϖ^p · c' = p` for some... no, `p = c · ϖ^p`.
3. In A°/(p): `x̄ = ȳ^p + ϖ̄·z̄`. And `c̄·ϖ̄^p = 0`.

This gives `x̄ = ȳ^p` only if `ϖ̄·z̄ = 0` in A°/(p). But `ϖ·z` is not necessarily in (p).

**Conclusion:** The sorry `theta_surjective` requires a non-trivial argument converting ϖ-Frobenius to p-Frobenius. This involves iterating the perfectoid condition. This is ~50-80 lines but doable.

- [ ] **Step 1:** Add helper `frobenius_modP_surjective` proving `Function.Surjective (frobenius (ModP A° p) p)` from the perfectoid condition. The proof iterates the condition p times and uses `p = c·ϖ^p` to show `ϖ^p ≡ 0 mod (p)`.

- [ ] **Step 2:** Use it to fill the sorry in `theta_surjective`.

- [ ] **Step 3:** Verify Tilting.lean compiles.

- [ ] **Step 4:** Commit.

### Task 2: Fill `isPrecomplete_pIdeal` SModEq step [HARD]

**File:** `Adic spaces/PerfectoidRing.lean:441`

The sorry needs: given limit `L ∈ A°` of the Cauchy sequence `f`, show `f n ≡ L [SMOD (Ideal.span {p})^n • ⊤]`, i.e., `p^n | (f n - L)` in A°.

**Proof strategy:** For `m ≥ n`, the Cauchy condition gives `p^n | (f m - f n)`. Taking `m → ∞`, `f m → L` in A, so `f n - L = lim_{m→∞} (f n - f m)`. Each `f n - f m ∈ p^n · A°`. If `p^n · A°` is closed in the topology of A°, then `f n - L ∈ p^n · A°`.

**Key sub-lemma:** `p^n · A°` is closed in A° (or equivalently, in A).

Why? `p^n · A° = {p^n · a | a ∈ A°}`. Since multiplication by `p^n` is continuous and `A°` is closed (we already showed limits of power-bounded sequences are power-bounded), `p^n · A°` is the continuous image of a closed set. But continuous images of closed sets are NOT necessarily closed...

**Alternative:** Show `p^n · A°` is closed by showing it's the intersection of zero-sets of continuous valuations (each valuation v gives `v(x) ≤ v(p^n) · sup_{a ∈ A°} v(a)`).

**Simplest approach:** The elements `g_m := (f m - f n) / p^n` (defined in A°) form a sequence. We need to show this sequence converges in A° to `(L - f n) / p^n`. But `p^n` is not invertible in A°...

**Pragmatic decision:** This sorry may need to remain. The mathematical content is correct but the formal proof requires showing `p^n · A°` is closed, which needs the nonarchimedean topology structure in a way not yet formalized. Mark as a TODO with clear documentation.

- [ ] **Step 1:** Add detailed comment explaining the proof strategy and the specific obstacle.
- [ ] **Step 2:** If time permits, attempt the closure argument.

### Task 3: Document remaining sorry's [HOUSEKEEPING]

The following sorry's are intentionally kept as placeholders for deep results:

**PerfectoidRing.lean:**
- `toIsStablyUniform` — Scholze Thm 5.2, research-level (almost mathematics + tilting)
- `toIsSheafy` — follows from stably uniform, Buzzard-Verberkmoes

**Tilting.lean:**
- `ker_theta_principal` — Scholze Lemma 3.10, needs explicit Witt vector computation
- `tilt_admits_perfectoid_structure` — needs topology on PreTilt (not in mathlib)
- `tilt_isField` — needs PreTilt field structure (not in mathlib)
- `tiltingEquiv` — Scholze Thm 3.7, depends on above

**PerfectoidSpace.lean:**
- All 3 sorry's depend on `toIsSheafy` or tilt topology

**CompletedAlgClosure.lean:**
- All 9 sorry's are axiomatized by design (PUnit placeholder)

- [ ] **Step 1:** Ensure all sorry's have clear docstrings explaining what's needed.
- [ ] **Step 2:** Commit with updated documentation.

---

## Estimated Outcome

| File | Before | After | Change |
|------|--------|-------|--------|
| PerfectoidRing.lean | 3 | 2-3 | -0 to -1 (IsPrecomplete hard) |
| Tilting.lean | 5 | 4 | -1 (theta_surjective) |
| PerfectoidSpace.lean | 3 | 3 | 0 (blocked by deep theorems) |
| CompletedAlgClosure.lean | 9 | 9 | 0 (axiomatized) |
| **Total** | **20** | **18-19** | **-1 to -2** |

The main win is making `theta_surjective` concrete, which validates the entire theta pipeline: theta definition → surjectivity → (ker principality stays sorry). This gives confidence that the construction is mathematically correct.
