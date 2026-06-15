# IsAdicComplete for Power-Bounded Subrings of Perfectoid Rings

> **For agentic workers:** REQUIRED: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `IsAdicComplete (Ideal.span {p}) A°` for a perfectoid ring `A`, filling the sorry in `PerfectoidRing.lean:147`.

**Architecture:** Split into two independent parts: `IsHausdorff` (intersection of `p^n A°` is zero) and `IsPrecomplete` (p-adic Cauchy sequences converge). Both arguments use the same key ingredient: the cofinality of the `p`-adic filtration with the topological neighborhood filtration, via `p = c · ϖ^p`.

**Tech Stack:** Lean 4, Mathlib `IsAdicComplete`/`IsHausdorff`/`IsPrecomplete` from `RingTheory.AdicCompletion.Basic`, `SModEq` from `LinearAlgebra.SModEq.Basic`, project APIs from `Bounded.lean` and `PerfectoidRing.lean`.

---

## Mathematical Proof

### IsHausdorff: `⋂_n p^n · A° = {0}`

Given `x ∈ A°` with `x ∈ p^n · A°` for all `n`:
1. Since `p = c · ϖ^p` in `A` (perfectoid condition), `p^n = c^n · ϖ^{np}`.
2. So `x ∈ p^n · A°` means `x = p^n · y_n` for some `y_n ∈ A°`, hence `(x : A) = c^n · ϖ^{np} · y_n`.
3. The set `{c^n · y_n · z | z ∈ A°}` is contained in `A° · A° · A° = A°` (bounded).
4. Since `ϖ^{np} → 0` and `A°` is bounded, for any `U ∋ 0` there exists `V` with `A° · V ⊆ U`, and for large `n`, `ϖ^{np} ∈ V`, so `x ∈ U`.
5. Hence `(x : A)` is in every neighborhood of 0, so `(x : A) = 0` by T₀, hence `x = 0` in `A°`.

**Key lemma needed:** For a bounded set `S` and topologically nilpotent `a`, `⋂_n (a^n · S) ⊆ {0}` in a T₀ topological ring. We don't need this in full generality; we prove the specific statement for `p^n` and `A°`.

### IsPrecomplete: p-adic Cauchy sequences converge

Given `f : ℕ → A°` with `f m - f n ∈ p^m · A°` for `m ≤ n`:
1. By the same cofinality, `f m - f n ∈ ϖ^{mp} · A°` (viewing in `A`).
2. This means `(f n : A)` is Cauchy in the topology of `A` (since `ϖ^{mp} · A°` shrinks to `{0}`).
3. Since `A` is complete, `(f n : A) → L` for some `L ∈ A`.
4. `L ∈ A°`: since each `f n ∈ A°` and `A°` is closed in `A` (it's `⋂_v {x : |v(x)| ≤ 1}`).
5. `f n ≡ L [SMOD p^n · A°]`: follows from the Cauchy condition and convergence.

**Key issue:** Step 4 (closedness of `A°`) is non-trivial. For a nonarchimedean ring, `A°` is the set of power-bounded elements, and this is closed iff `A` is "well-behaved". For perfectoid rings (which are uniform), `A°` is the unique maximal bounded subring, and it IS closed.

**Simplification:** Rather than proving `A°` is closed in full generality, we can use a weaker approach: show that for the specific Cauchy sequence, the limit `L` is power-bounded by using the boundedness of the sequence elements.

---

## File Structure

All changes go in one file:

- **Modify:** `Adic spaces/PerfectoidRing.lean` — replace the sorry at line 147 with the proof, adding helper lemmas in the same `namespace IsPerfectoidRing` section.

No new files needed. The proof adds ~80-120 lines.

---

## Task Breakdown

### Task 1: Helper — `p^n` membership in `A°` implies `ϖ^{np}` membership

**Files:**
- Modify: `Adic spaces/PerfectoidRing.lean:124-147`

This is the cofinality lemma: membership in `p^n · A°` (as an ideal of `A°`) implies a relationship with `ϖ^{np}` in the ambient ring `A`.

- [ ] **Step 1:** Add helper lemma `mem_span_pow_p_of_perfectoid`

The key algebraic fact: if `x ∈ Ideal.span {(p : A°)}^n · ⊤` (as a submodule of `A°`), then `(x : A) ∈ Set.range (fun y => (p : A)^n * y)` where `y ∈ A°`. In particular, `(x : A) = (c · ϖ^p)^n · y` for power-bounded `y`.

```
-- For all x in A°, x ≡ 0 [SMOD (Ideal.span {p})^n • ⊤] implies
-- (x : A) can be written as p^n * y for some y ∈ A°
```

- [ ] **Step 2:** Verify step 1 compiles (LSP check)

- [ ] **Step 3:** Commit

### Task 2: IsHausdorff — prove `⋂ p^n A° = {0}`

**Files:**
- Modify: `Adic spaces/PerfectoidRing.lean`

- [ ] **Step 1:** Add `instIsHausdorff` instance

Prove `IsHausdorff (Ideal.span {p}) A°` using `IsHausdorff.mk`. The proof:
1. Take `x : A°` with `∀ n, x ≡ 0 [SMOD (Ideal.span {p})^n • ⊤]`.
2. Use `SModEq.sub_mem` to get `x ∈ (Ideal.span {p})^n • ⊤` for all `n`.
3. Embed into `A`: `(x : A) ∈ p^n · (image of A°)` for all `n`.
4. Use `p = c · ϖ^p` to show `(x : A)` is in every neighborhood of 0:
   - Extract `y_n ∈ A°` with `(x : A) = (p : A)^n * (y_n : A)`
   - Rewrite `(p : A)^n = ((c : A) * (ϖ : A)^p)^n`
   - Use `IsPowerBounded.isTopologicallyNilpotent_mul` and `T0Space` to conclude `x = 0`.

- [ ] **Step 2:** Verify step 1 compiles (LSP check)

- [ ] **Step 3:** Commit

### Task 3: IsPrecomplete — prove p-adic Cauchy sequences converge

**Files:**
- Modify: `Adic spaces/PerfectoidRing.lean`

This is the harder part. We need to show every p-adic Cauchy sequence in `A°` has a limit.

- [ ] **Step 1:** Add `instIsPrecomplete` instance

Prove `IsPrecomplete (Ideal.span {p}) A°` using `IsPrecomplete.mk`. The proof:
1. Take `f : ℕ → A°` Cauchy: `∀ m ≤ n, f m ≡ f n [SMOD (Ideal.span {p})^m • ⊤]`.
2. The sequence `(f n : A)` is topologically Cauchy in `A` (by cofinality: differences lie in shrinking neighborhoods).
3. Since `A` is complete, `(f n : A)` converges to some `L : A`.
4. Show `L ∈ A°` (L is power-bounded).
5. Show `f n ≡ ⟨L, hL⟩ [SMOD (Ideal.span {p})^n • ⊤]`.

**Alternative approach (simpler):** If the Cauchy sequence argument is too hard topologically, we can use the telescoping sum approach:
- `f n = f 0 + Σ_{k=0}^{n-1} (f(k+1) - f(k))`
- Each difference `f(k+1) - f(k) ∈ p^k · A°`, so `f(k+1) - f(k) = p^k · g_k` for `g_k ∈ A°`.
- Define `L = f 0 + Σ_{k=0}^∞ p^k · g_k` — this converges since `p^k → 0`.
- Then `f n - L = Σ_{k=n}^∞ p^k · g_k ∈ p^n · A°`.

This avoids topology entirely and works purely algebraically, but requires showing the infinite sum converges.

- [ ] **Step 2:** Verify step 1 compiles (LSP check)

- [ ] **Step 3:** Commit

### Task 4: Assemble — combine into `instIsAdicComplete`

**Files:**
- Modify: `Adic spaces/PerfectoidRing.lean:142-147`

- [ ] **Step 1:** Replace the `sorry` in `instIsAdicComplete` with `IsAdicComplete.mk`

With the `IsHausdorff` and `IsPrecomplete` instances from Tasks 2-3, the proof is just:
```lean
instance instIsAdicComplete ... :=
  { toIsHausdorff := instIsHausdorff p A
    toIsPrecomplete := instIsPrecomplete p A }
```

- [ ] **Step 2:** Verify full file compiles with `lake env lean`

- [ ] **Step 3:** Verify Tilting.lean still compiles (theta now uses this instance)

- [ ] **Step 4:** Commit with message referencing the mathematical content

---

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| `SModEq` unfolding issues | Medium | Use `SModEq.sub_mem` early to convert to membership |
| Embedding `A° → A` coercion issues | Medium | Use `Subtype.val` explicitly, `Subring.coe_*` lemmas |
| Closedness of `A°` in `A` | High | Use weaker argument: limits of power-bounded sequences are power-bounded |
| Infinite sum convergence | High | May need `tsum` or `HasSum` API; alternatively use the topological Cauchy argument |
| `Ideal.span {p}^n • ⊤` ↔ `p^n * A°` | Medium | Need `Ideal.span_singleton_pow` + `Ideal.smul_top_eq_map` |

## Estimated Effort

~80-120 lines of proof code, split across Tasks 1-4. Task 2 (IsHausdorff) is the most tractable. Task 3 (IsPrecomplete) is the hardest and may need the most iteration.
