# Plan: Fill W5 + W6/W7 — Completing Wedhorn 7.18

**Date:** 2026-04-10
**Target:** The two sub-sorries in `Adic spaces/Presheaf.lean:1251` (W5: `g_max < 1`) and `:1256` (W6/W7: cofinality).
**Reference:** Wedhorn Prop 7.18 (pp. 60–61), proof by [Hu2] Lemma 3.3.

---

## 1. Diagnosis: Why the Current Proof Is Stuck

The current proof uses `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` (Stacks 090P part 1) to get `V₀ ⊇ integralClosure(B)` with `ι x ∉ V₀`. This gives:
- `V₀.valuation ≤ 1` on B (since B ⊆ integralClosure(B) ⊆ V₀)  
- `V₀.valuation(ι x) > 1` (since ι x ∉ V₀)

**BUT** it does NOT give:
- **W5:** `V₀.valuation < 1` on P.I generators (they could be V₀-units → value = 1)
- **W6/W7:** Cofinal powers of `g_max` in `V₀.ValueGroup` (value group might have higher rank)

---

## 2. Root Cause and Fix

### Root cause for W5
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` (Stacks 090P **part 1**) doesn't control the maximal ideal of V₀.

**Fix:** Use `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn` (Stacks 090P **part 2**, Mathlib `LocalSubring.lean:171–191`). This produces V **dominating** a local subring L, meaning `maxIdeal(L) ⊆ maxIdeal(V)`. If we choose L so that P.I images are in `maxIdeal(L)`, then P.I images land in `maxIdeal(V) = V.nonunits`, giving strict `< 1`.

### Root cause for W6/W7
`V₀.ValueGroup` might not be MulArchimedean (could have rank > 1), so `g^n` might not be cofinal.

**Fix:** Coarsen V₀'s valuation via `Valuation.restrictToConvex` (ValuationContinuity.lean:485) with a `convexGenerated` subgroup. The restricted value group `WithZero(H_gen.toSubgroup)` is automatically MulArchimedean, and `withZero_inv_pow_cofinal_of_convexGenerated` (Lemma745.lean:194) gives cofinality.

---

## 3. Key Architectural Decision: Restructure the Existential

**Change the existential statement** from "∃ V : ValuationSubring with properties" to "∃ continuous valuation on R with properties":

```lean
-- OLD (current):
have hV_exists : ∃ V : ValuationSubring (FractionRing R),
    integralClosure(B) ≤ V.toSubring ∧ ι x ∉ V ∧
    ∃ (g : V.ValueGroup) (_ : g < 1), ... := by

-- NEW (proposed):
have hV_exists : ∃ (Γ₀ : Type) (_ : LinearOrderedCommGroupWithZero Γ₀)
    (wVal : Valuation R Γ₀),
    (∀ b ∈ B, wVal b ≤ 1) ∧ 1 < wVal x ∧ wVal.IsContinuous := by
```

**Why:** The coarsened valuation has value group `WithZero(H_gen.toSubgroup)`, not `V.ValueGroup`. Producing a `Valuation R Γ₀` directly avoids the type mismatch. The downstream proof simplifies dramatically.

---

## 4. Proof Architecture (Following Lemma 7.45's Pattern)

The proof reuses ~70% of `exists_spa_point_via_restrictToConvex` (Lemma745.lean:344–599).

### Step A: Refined Stacks 090P (replaces W4 + W5)

**Goal:** Produce `V : ValuationSubring (FractionRing R)` with:
- `integralClosure(B) ⊆ V.toSubring`
- `ι x ∉ V`
- `image(P.I) ⊆ V.nonunits` (strict bound)

**Construction:**
1. Let `R₀ := (integralClosure B (FractionRing R)).toSubring`.
2. Define the **conductor ideal**: `S(x) := { s ∈ R₀ : s · (ι x) ∈ R₀ }`.
   - This is an `Ideal R₀` (Mathlib has `Submodule.colon R₀ {ι x}` for this).
   - `S(x) ≠ ⊤` since `1 · (ι x) = ι x ∉ R₀`.
3. Map P.I generators into R₀ via `ι ∘ P.A₀.subtype` (works since `P.A₀ ⊆ B ⊆ R₀`).
   Let `I_img` be the ideal of R₀ they generate.
4. **Show `S(x) + I_img ≠ ⊤`** (the KEY properness lemma — see §5 below).
5. Find maximal ideal `𝔪 ⊇ S(x) + I_img` via `Ideal.exists_le_maximal`.
6. Set `L := LocalSubring.ofPrime R₀ 𝔪`.
7. **Verify `ι x ∉ L.toSubring`:** If `ι x ∈ L`, then `ι x = a/s` with `a ∈ R₀`, `s ∉ 𝔪`. So `s · ι x = a ∈ R₀`, meaning `s ∈ S(x) ⊆ 𝔪`, contradiction.
8. **Verify IsIntegrallyClosedIn:** Localization of integrally closed at a prime preserves integrally closed.
9. Apply `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn` → V dominating L with `ι x ∉ V`.
10. **Extract strict bound:** Domination gives `𝔪 ⊆ maxIdeal(V)`, so `I_img ⊆ maxIdeal(V) = V.nonunits`. Hence `V.valuation < 1` strictly on all P.I generators.

### Step B: Coarsen for MulArchimedean (replaces W6/W7)

**Goal:** Produce `wVal : Valuation R (WithZero H_gen.toSubgroup)` that is continuous with `wVal ≤ 1` on B and `wVal x > 1`.

**Construction (following Lemma745.lean:407–506):**

1. Compute `g_max := S.sup'` of `V.valuation(ι(P.A₀.subtype s))` over generators `s ∈ S`.
   Now `g_max < 1` (from Step A).
2. Let `u_max := Units.mk0 g_max hg_ne0` and `u_x := Units.mk0 (V.valuation(ι x)) hx_ne0`.
3. Form the convex subgroup: `H_gen := ConvexSubgroup.convexGenerated (max(u_max⁻¹, u_x))`.
   - Ensures `u_max ∈ H_gen` (so P.I values are preserved)
   - Ensures `u_x ∈ H_gen` (so x's value is preserved)
4. Apply `restrictToConvex` to `V.valuation.comap ι |_{P.A₀}` → `v_r : Valuation P.A₀ (WithZero H_gen)`.
   This works because `V.valuation.comap ι ≤ 1` on P.A₀.
5. Extend `v_r` from P.A₀ to R via `vExtFun` (using topologically nilpotent `s ∈ P.I`):
   `v_ext(a) := v_r(s^n · a) · v_r(s)^{-n}` where n is minimal with `s^n · a ∈ P.A₀`.
6. The extended `v_ext : Valuation R (WithZero H_gen)` has:
   - **Continuity:** via `isContinuous_of_le_one_and_pow_cofinal` with cofinal from `withZero_inv_pow_cofinal_of_convexGenerated`.
   - **v_ext ≤ 1 on B:** For `b ∈ B`, either `v_r(s^n · b)` is zero (giving v_ext = 0 ≤ 1) or preserved with the original value `V.valuation(ι b) ≤ 1`.
   - **v_ext(x) > 1:** Since `u_x ∈ H_gen`, `v_r` preserves x's value, and the extension gives `v_ext(x) = V.valuation(ι x) > 1`.

### Step C: Package the result

Return `⟨WithZero H_gen, _, v_ext, hB, hx, hcont⟩` as the existential witness.

---

## 5. The KEY Properness Lemma: `S(x) + I_img ≠ ⊤`

**Statement:** For `R₀ = integralClosure(B)`, `S(x) = conductor(x)`, `I_img = image of P.I in R₀`:

> If `ι x ∉ R₀` and every generator of P.I is in the Jacobson radical of R₀, then `S(x) + I_img ≠ ⊤`.

**Proof:** By contradiction. If `1 = c + i` with `c ∈ S(x)`, `i ∈ I_img`, then `c = 1 - i`.

Since `i` is in the Jacobson radical of R₀, `1 - i` is a unit in R₀. Call its inverse `u := (1-i)⁻¹ ∈ R₀`.

Now `c = 1 - i`, so `c · (ι x) ∈ R₀` (by definition of conductor). Then `ι x = u · (c · ι x) ∈ R₀`, contradicting `ι x ∉ R₀`. ∎

**Sub-lemma needed:** P.I generators are in Jacobson radical of `R₀ = integralClosure(B)`.

For `s ∈ P.I` and any `t ∈ R₀`, we need `1 - (ι s) · t` to be a unit in R₀.

**Proof approaches:**

**(A) Via adic completeness (requires `[IsAdicComplete P.I P.A₀]`):**
- The geometric series `1 + st + (st)² + ...` converges in P.A₀ (I-adic completeness).
- The limit is `(1 - st)⁻¹ ∈ P.A₀ ⊆ B ⊆ R₀`.
- So `1 - st` is a unit in R₀ with inverse in R₀.
- **⚠ Obstacle:** We may NOT have `IsAdicComplete` for our specific P (the locPairOfDefinition). The locSubring is NOT necessarily complete.

**(B) Via power-boundedness (no completeness needed):**
- `s ∈ P.I` is topologically nilpotent in R.
- For any `t ∈ R₀`: since R₀ is bounded (integral closure of bounded subring is bounded), `t` is power-bounded.
- `st` is topologically nilpotent (product of top-nilp and power-bounded is top-nilp).
- In Tate rings: `1 - (top nilp unit) · u = 1 - (nilp)` is a unit (Wedhorn Lemma 6.6 / open mapping).
- The inverse `(1 - st)⁻¹ = Σ (st)^n` might not converge in R₀ directly, but it EXISTS in R (the full ring) and is integral over B (since its powers are bounded by the geometric series convergence).
- So `(1-st)⁻¹ ∈ integralClosure(B) = R₀`.
- **⚠ Subtlety:** Need to verify `(1-st)⁻¹` is power-bounded (hence integral over B). If `st` is topologically nilpotent, the formal series `1 + st + (st)² + ...` has partial sums that are bounded (in the nbhd `{a : |a| ≤ 1}` of bounded elements). So the limit (if it converges) is power-bounded.

**(C) Via the ambient ring A (for our specific Tate application):**
- Our R = Localization.Away D'.s. Our P = locPairOfDefinition.
- The ORIGINAL ring A has pair of definition D'.P with [IsAdicComplete D'.P.I D'.P.A₀] (or at least, A is a Tate ring with well-behaved completion).
- The elements of P.I = locIdeal are images of D'.P.I via algebraMapD.
- In A, D'.P.I elements are topologically nilpotent. Geometric series converges in D'.P.A₀ ⊆ A.
- Transfer to R via algebraMap.

**Recommendation:** Use approach **(C)** for our specific application, adding `[IsAdicComplete D'.P.I D'.P.A₀]` as a hypothesis (which is available in Tate rings with noetherian ring of definition). This is the most concrete path and avoids abstract power-boundedness machinery.

---

## 6. Implementation Tickets

| Ticket | Description | Est. lines | Depends on | Risk |
|--------|-------------|------------|------------|------|
| **F1** | Restructure existential to produce `Valuation R Γ₀` directly | ~20 | None | Low |
| **F2** | Simplify downstream proof (contradict hvle directly) | ~-10 (net) | F1 | Low |
| **F3** | Conductor ideal `S(x)` as Mathlib `Submodule.colon` | ~30 | None | Low |
| **F4** | Jacobson radical membership for P.I in integralClosure(B) | ~60 | F3 | **HIGH** |
| **F5** | Properness of `S(x) + I_img` using F4 | ~40 | F3, F4 | Medium |
| **F6** | Refined Stacks 090P: LocalSubring.ofPrime + domination | ~50 | F5 | Medium |
| **F7** | Coarsen via restrictToConvex with enlarged H_gen | ~80 | F6 | Medium |
| **F8** | Extension vExtFun from P.A₀ to R | ~40 | F7 | Medium |
| **F9** | Verify v_ext ≤ 1 on B and v_ext(x) > 1 | ~40 | F7, F8 | Medium |
| **F10** | Continuity via isContinuous_of_le_one_and_pow_cofinal | ~20 | F7, F8 | Low |
| **F11** | Final assembly: package into existential + build verification | ~20 | F1-F10 | Low |
| **Total** | | **~380 lines** | | |

### Critical path: F3 → F4 → F5 → F6 → F7 → F8/F9/F10 → F11
### Highest-risk item: F4 (Jacobson radical)
### Parallelizable: F1/F2 (restructure) can run in parallel with F3-F4

---

## 7. Reusable Infrastructure from Lemma 7.45

| Infrastructure | Source | Reuse |
|---------------|--------|-------|
| `convexGenerated` construction | OrderedGroupConvex.lean:387–462 | Direct |
| `withZero_inv_pow_cofinal_of_convexGenerated` | Lemma745.lean:194–204 | Direct |
| `restrictToConvex` + full API | ValuationContinuity.lean:485–661 | Direct |
| `vExtFun_*` extension lemmas | Lemma745.lean:243–339 | Adapt (different `s`, same pattern) |
| `isContinuous_of_le_one_and_pow_cofinal` | ValuationContinuity.lean:70–96 | Direct |
| `valuation_le_on_ideal_of_le_on_generators` | ValuationContinuity.lean:298–318 | Direct |
| `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn` | Mathlib LocalSubring.lean:171–191 | Direct |
| `Ideal.exists_le_maximal` | Mathlib Ideal/Maximal.lean:73 | Direct |

---

## 8. Prerequisites and Hypotheses

The theorem `isIntegral_of_forall_continuous_valuation_le_one` may need **additional hypotheses**:

1. **`[IsAdicComplete P.I P.A₀]`** — for the Jacobson radical argument (F4). Alternative: use power-boundedness argument (approach B) which might avoid this.

2. **The existence of a topologically nilpotent element in P.I** — for the vExtFun extension (F8). This follows from `P.fg` + `P.isAdic` (elements of I are topologically nilpotent by `PairOfDefinition.isTopologicallyNilpotent_of_mem`).

For our specific Tate instance application:
- `P = locPairOfDefinition D'.P D'.T D'.s D'.hopen`
- `P.A₀ = locSubring` (NOT I-adically complete in general)
- If we add `[IsAdicComplete P.I P.A₀]`, we need to provide this instance for locPairOfDefinition, which requires locSubring to be J-adically complete. This is FALSE in general but might hold with additional hypotheses.

**Fallback:** If adic completeness is too strong, refactor to work in the COMPLETION `presheafValue D'` (where completeness holds) and transfer integrality back to R. This adds complexity but avoids the completeness obstacle.

---

## 9. Acceptance Criteria

After implementing F1–F11:
1. `isIntegral_of_forall_continuous_valuation_le_one` compiles with 0 sorries.
2. The Tate instance `HasLocLiftPowerBounded.tate` compiles with 0 sorries.
3. `PresheafIdentification.lean` has 0 sorries.
4. Full `lake build` passes (3080+ jobs).
5. R4 is COMPLETE.
