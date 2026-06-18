# Stream A — Updated brief for the Hasse bound (v2, 2026-04-22) — CORRECTED

**Supersedes:** `hasse-bound-stream-A-brief-v2.md` earlier tonight.

**Correction to earlier v2 draft:** I wrote that stream A was "supporting, not critical-path". **That was wrong.** On a careful re-read of the consumer chain, **both streams A and D are critical-path** — neither alone closes the bound. Specifically, V.1.3 (`#E(F_q) = deg(1−π)`) requires stream A's **T-II-2-009** unconditional form to break a circularity in the fiber-witness otherwise.

**See `HasseWeil/Hasse/Unconditional.lean`** for the validation harness — it makes the hole you need to fill explicit as `HOLE D`.

**Subject:** Close T-II-2-009 (unconditional) applied to `β_pc = oneSubFrobeniusIsog W`. This is the missing piece on the V.1.3 side.

---

## Why you're critical-path — the circularity you resolve

The validation harness `hasse_bound_target` in `HasseWeil/Hasse/Unconditional.lean` needs, for the V.1.3 side, `h_pc_fiber_witness`:

```lean
∃ P₀ : W.toAffine.Point,
  Nat.card {P // β_pc.toAddMonoidHom P = β_pc.toAddMonoidHom P₀} =
    β_pc.sepDegree
```

where `β_pc = oneSubFrobeniusIsog W`. Taking `P₀ = 0` reduces this to `|ker β_pc| = sepDeg β_pc`. For separable `β_pc`, `sepDeg = deg`. So the witness becomes `|ker β_pc| = β_pc.degree`, i.e., `|E(F_q)| = β_pc.degree` — which is **precisely V.1.3 itself**. Circular.

**T-II-2-009** (Silverman II.2.6(b), generic-fiber cardinality) produces a *non-trivial* `P₀` where fiber-size equals `sepDeg`. Via the worker's existing bridge `Isogeny.fiber_witness_of_ker_card_eq_sepDegree` (`HasseWeil/EC/IsogenyKernel.lean:368`), this is not tautological: the generic point has fiber size equal to `sepDeg` by the structure of the curve extension, *independent* of the Hasse statement.

That's the loop-breaker. No other stream has this output.

---

## Deliverables — re-prioritised

### 🎯 Priority 0 (CRITICAL-PATH FOR HASSE) — T-II-2-009 unconditional applied to β_pc

**File:** target — close `HOLE D` in `HasseWeil/Hasse/Unconditional.lean` (line ~125).

**Target:**

```lean
example (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (oneSubFrobeniusIsog W).toAddMonoidHom P =
            (oneSubFrobeniusIsog W).toAddMonoidHom P₀} =
        (oneSubFrobeniusIsog W).sepDegree
```

**How:** T-II-2-009 for general `CurveMap` (your stream's ticket), then specialise to `β_pc = oneSubFrobeniusIsog W`. Under the `isogOneSub` placeholder, `β_pc.sepDegree = 1` (trivial self-extension), so the witness becomes "∃ P₀ with fiber-size 1" — which holds at **any non-kernel** point: pick `P₀` with `β_pc.toAddMonoidHom P₀ ≠ 0`, then the fiber is `{P₀}` (a single coset of the trivial kernel portion). Actually under the placeholder this simplifies dramatically, possibly to `P₀ = 0` trivially if the placeholder gives `sepDeg = 1 = 1`. The exact placeholder reduction is worth checking first — it may be a near-one-liner under the current placeholder setup.

For the unconditional β_pc (post-AdditionPullback), T-II-2-009 in full generality is the real content.

### Priority 1 — T-II-2-008 full form (unblocks many tickets beyond Hasse)

**Rationale:** worker-K's `sum_ramificationIdx_eq_finrank` in `NormValuation.lean` gives the specific case for the coordinate function `x : C → A¹`. Extending to arbitrary `CurveMap C₁ C₂` + arbitrary test function `t` closes T-II-2-008 unconditionally.

**File:** `HasseWeil/Curves/CurveMap.lean` (extend).

**Target signature:**

```lean
theorem CurveMap.sum_ramificationIndexℤ_eq_degree
    (φ : CurveMap C₁ C₂) (t : C₂.FunctionField) (ht : t ≠ 0)
    (fiber : Finset C₁.SmoothPoint)
    (h_fiber : /- fiber characterisation -/) :
    ∑ P ∈ fiber, φ.ramificationIndexℤ P t = (φ.degree : ℤ)
```

**Pick-up theorems already axiom-clean:**
- `HasseWeil.Curves.CurveMap.fiber_card_eq_degree_iff_all_ramificationIndexℤ_one` — consumes this as `hsum`.
- `HasseWeil.Isogeny.ramificationIndex_mul_sepDegree_eq_degree_of_witnesses` — same via the isogeny-side witness form.

**Estimated work:** ~90 lines: wrap worker-K's `sum_ramificationIdx_eq_finrank` + `Ideal.sum_ramification_inertia` + handle the arbitrary `t` case.

---

### Priority 2 — T-II-2-001 full form (opens Route A for the dual keystone)

**Rationale:** `rational map on smooth curve ⇒ morphism`. Without this, my `factor_through_isogeny_existsUnique_witness` (T-III-4-016 witness) can't convert its Galois-fixed-field output into a concrete `Isogeny E₂ E₃` — the uniqueness side `h_surj` input needs T-II-2-002 too.

**File:** `HasseWeil/Curves/RationalMap.lean` (extend) or new file.

**Target:** a morphism-extension theorem for rational maps on smooth curves (Silverman II.2.1).

**Estimated work:** ~200 lines. Substantial, but standard algebraic-geometry material.

---

### Priority 3 — Pic⁰ backup route (Route B to `exists_dual`)

**Rationale:** If stream D's BRIDGE-001/003 stalls, Route B via Pic⁰ is the second-best path. It needs:

1. **T-II-3-009 completion** (worker-K active): `deg(div f) = 0`. ~200 remaining lines per worker-K's progress logs.
2. **T-II-3-011** (`φ*, φ_*` on divisors). Depends on T-II-3-001 (divisor def, DONE) and T-II-2-007 (ramification index, PARTIAL). ~80 lines.
3. **T-III-3-004** (Pic⁰(E) ≅ E): depends on T-II-3-010 (exact sequence) + T-III-3-002/005/006. ~100 lines in main-line but the prerequisite stack is taller.

Coordinating with worker-K on T-II-3-009 or picking up T-II-3-011 would help.

---

### Priority 4 — `ordAtInfty_algebraMap_F_nonzero` (small lemma I deferred)

**Rationale:** I attempted this in `HasseWeil/OrdAtInftyBridge.lean` (session 2) but hit a heartbeat timeout on instance resolution for the `Algebra (FractionRing F[X]) KE` tower. Your stream has the `FractionRing (Polynomial F)`-algebra instances in `Curves/FiniteOverKx.lean`; delivering this as a named lemma in stream A's idiom would both close the gap I noted AND make downstream work cleaner.

**File:** `HasseWeil/Curves/Infinity.lean` (extend).

**Target signature:**

```lean
theorem ordAtInfty_algebraMap_F_of_ne_zero
    (C : SmoothPlaneCurve F) (c : F) (hc : c ≠ 0) :
    C.ordAtInfty (algebraMap F C.FunctionField c) = (0 : WithTop ℤ)
```

**Estimated work:** ~30 lines of `RatFunc` manipulation (see my `OrdAtInftyBridge.lean` for the attempted proof sketch).

---

## What's NOT critical-path for Hasse anymore

- **T-II-2-002** (nonconst surjective) — stream-A deliverable but redundant for finite-field Hasse. Still valuable for generalisation of kernel finiteness.
- **T-II-2-009** (fiber = sepDeg generic) — reduced to `|ker| = sepDeg` via the worker's earlier bridge `Isogeny.fiber_witness_of_ker_card_eq_sepDegree` (`IsogenyKernel.lean:368`); which in turn shifts the obligation but doesn't close Hasse alone.

---

## How the chain looks once everything lands

If stream D lands Route D and you land Priority 1 (T-II-2-008 full):

```lean
-- Axiom-clean, sorry-free
theorem hasse_bound_unconditional
    (W : WeierstrassCurve 𝔽_q) [W.toAffine.IsElliptic]
    [Fintype W.toAffine.Point] :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card 𝔽_q) - 1 : ℝ)|
      ≤ 2 * Real.sqrt (Fintype.card 𝔽_q : ℝ) := by
  -- Via hasse_bound_of_all_witnesses + stream D's deg QF + worker-J's
  -- witness forms already in place.
  sorry  -- one-line discharge via plug-ins
```

Your T-II-2-008 output also unblocks T-II-3-012, T-III-4-013 unconditional form, and T-II-2-010, generalising the ramification theory.

---

## Files you'll touch

- `HasseWeil/Curves/CurveMap.lean` — Priority 1
- `HasseWeil/Curves/RationalMap.lean` — Priority 2
- `HasseWeil/Curves/Divisors.lean` + `ProjectiveDivisor.lean` — Priority 3 (coordinate with worker-K)
- `HasseWeil/Curves/Infinity.lean` — Priority 4

---

## Existing consumer API (your drop-in targets)

All axiom-clean:

- `HasseWeil.Isogeny.kernel_finite_of_fiber_finite` (`EC/IsogenyKernel.lean`)
- `HasseWeil.Isogeny.fiber_card_eq_sepDegree_of_witness` (`EC/IsogenyKernel.lean`)
- `HasseWeil.Isogeny.card_kernel_eq_degree_of_separable_witness` (`EC/IsogenyKernel.lean`)
- `HasseWeil.Isogeny.fiber_witness_of_ker_card_eq_sepDegree` (**new, your own**, `EC/IsogenyKernel.lean:368`)
- `HasseWeil.Isogeny.factor_through_isogeny_existsUnique_witness` (`EC/IsogenyFactor.lean`) — for Priority 2
- `HasseWeil.Curves.CurveMap.fiber_card_eq_degree_iff_all_ramificationIndexℤ_one` (`Curves/CurveMap.lean`)

---

## References

- Silverman, *The Arithmetic of Elliptic Curves*, II.2.1 / II.2.6 / II.3 / III.3.
- Status report: my answer of 2026-04-22 "full project status update".
- Worker-K's progress log: `tickets/curves/T-II-3-009-deg-div-zero.md`.
