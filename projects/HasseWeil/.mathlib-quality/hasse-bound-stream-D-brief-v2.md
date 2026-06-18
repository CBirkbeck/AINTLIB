# Stream D — Updated brief for closing the Hasse bound (v2, 2026-04-22)

**Supersedes:** `hasse-bound-stream-D-brief.md` (first draft).

**Subject:** Close T-IV-BRIDGE-001 + T-IV-BRIDGE-003 — the last two stream-D tickets gating the axiom-clean `hasse_bound`.

**Correction to earlier v2 draft:** I originally implied "Route D alone closes the bound." **That was wrong.** Stream D's chain closes **V.1.4/V.1.5** (the QF side) but **V.1.3** (`#E(F_q) = deg(1−π)`) still needs stream A's T-II-2-009 to break a fiber-witness circularity. See `HasseWeil/Hasse/Unconditional.lean` for the validation harness — the `HOLE E` you close is one of five; `HOLE D` is stream A's. **Both streams are critical-path, in parallel.** You're not alone, but the QF side is entirely yours.

**Why you're on the critical path:** Every other route to the unconditional Hasse bound on the QF side has a deeper obstruction.
- **Route A** (close `AdditionPullback.lean`'s three transcendence sorries) is ~500 lines of polynomial manipulation, and an attempted `ordAtInfty` shortcut this week hit ramification-theory walls at infinity.
- **Route B** (Pic⁰(E) ≅ E) depends on worker-K's T-II-3-003/009 plus T-II-3-011 — active but further out.
- **Route D** (yours): the formal-group machinery is **almost entirely in place** (T-IV-2-* / T-IV-4-* / T-IV-5-* mostly DONE by workers E/F/G). Only BRIDGE-001/003 remain.

Close your two tickets and the QF side (V.1.4/V.1.5/V.1.6) cascades to sorry-free via consumer theorems that are already axiom-clean.

---

## Your two deliverables

### 1. T-IV-BRIDGE-001 — `omegaPullbackCoeff α = leading formal coefficient`

**File:** extend `HasseWeil/OmegaPullbackCoeff.lean` (or new `HasseWeil/FormalGroupBridge.lean`).

**Target signature:**

```lean
theorem omegaPullbackCoeff_eq_formalIsogenyLeading
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine) :
    omegaPullbackCoeff W α =
      PowerSeries.coeff F 1 (formalIsogenySeries W α)
```

**Closes:** the Wronskian-based sorry in `OmegaPullbackCoeff.lean:477` (by redirection — the `omegaPullbackCoeff` characterisation bypasses the Wronskian path).

**Key infra available** (all DONE):
- `omegaPullbackCoeff` + `_spec` (in `OmegaPullbackCoeff.lean`) — the defining equation at the pullback level
- T-IV-4-001..006 invariant-differential API
- T-IV-4-005 chain rule for formal groups
- T-IV-BRIDGE-005 `kaehler_rank_one` (already DONE, check the ticket)

---

### 2. T-IV-BRIDGE-003 — `formalIsogenySeries_add`

**File:** same as above.

**Target signature:**

```lean
theorem formalIsogenySeries_add
    (α β γ : Isogeny W.toAffine W.toAffine)
    (h_add : γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom) :
    formalIsogenySeries W γ =
      PowerSeries.subst₂ (W.formalGroup.fAdd)
        (formalIsogenySeries W α) (formalIsogenySeries W β)
```

This is the isogeny-to-formal-group additivity bridge. Your T-IV-2-006/007 (done) machinery for `[m]` on formal groups gives the template; generalising to arbitrary isogenies is the substantive work.

---

## What auto-completes after you land both

The consumer chain below is **already axiom-clean in the repo**. Once BRIDGE-001/003 land, each step is a one-liner:

**Step A — T-III-5-002** (pullback additivity `(φ+ψ)*ω = φ*ω + ψ*ω`):

Differentiate BRIDGE-003 at the origin using the formal chain rule (T-IV-4-005). Target: the worker-J unconditional form of
`mulByInt_pullbackKaehler_invariantDifferential` in `HasseWeil/Hasse/Separability.lean`, replacing its `omegaPullbackCoeff_mulByInt` witness.

**Step B — T-III-5-006** (ring hom `α ↦ a_α : End E → F`):

Combine BRIDGE-001 (which gives `a_α = coeff 1 (formalIsogenySeries α)`) with:
- Additivity from step A
- Multiplicativity from the formal chain rule (T-III-5-010, already DONE)

Deliverable: `noncomputable def pullbackCoeffRingHom : Isogeny W.toAffine W.toAffine →+* F`.

Closes the 2 sorries in `HasseWeil/PullbackCoeff.lean`.

**Step C — T-III-6-005** (dual additivity):

**Already in place as witness-parametric:** `HasseWeil.dual_add_of_trace_witnesses` in `DualIsogeny.lean` (commit `48f9778` from today). Given step B's ring-hom output + III.5.7 (kernel of a_ = inseparables), discharge `dual_add_of_trace_witnesses`'s hypotheses and the unconditional form is yours.

**Step D — T-III-6-009** (deg QF = pos-def quadratic form):

**Already in place as consumer:** `HasseWeil.degree_quadratic_closed` + the specialised `isogSmulSub_degree_quadratic_closed` in `DegreeQuadraticForm.lean` (commits `5d89e3c`, `a48843b` from today). Supply the four inputs:

```lean
-- α = frobeniusIsog W (or any Isogeny W.toAffine W.toAffine you like)
-- α_dual = your dualOf α (from exists_dual_of_constructor + BRIDGE outputs)
-- h_dual_comp : from isogDual_comp_self for α_dual
-- h_sum_trace : from isogTrace_eq_dual + ring hom (step B)
-- h_deg_bridge : ← the toAddMonoidHom → degree coherence (see below, NOT yours)
```

Closes `DegreeQuadraticForm.lean:145` (the `degree_quadratic` sorry).

**Step E — unconditional `hasse_bound`:**

Already in place as `hasse_bound_of_all_witnesses` in `Hasse/BoundOfWitnesses.lean`. With `degree_quadratic` closed, the `β_qf r s = isogSmulSub (frobeniusIsog W) r s` family has the required degree identity, and the top-level bound is a one-liner.

---

## What's NOT yours (someone else closes these)

- **`Frobenius.lean:128`** — the `pointCount_eq` sorry. Once `degree_quadratic` closes, the `pointCount` identity follows from `hasse_bound_of_all_witnesses` directly (bypassing the `isogOneSub` placeholder). The sorry becomes redundant rather than requiring closure.
- **`AdditionPullback.lean:193/225/268`** — the transcendence sorries. Not needed for Hasse if Route D completes.
- **`DualIsogeny.lean:134` (`exists_dual`)** — dispatched by your ring-hom output + `exists_dual_of_constructor` (commit `dff85e9`).
- **`h_deg_bridge`** — the `toAddMonoidHom → degree` coherence used by `degree_quadratic_closed`. This is the bridge: "if two isogenies agree on `toAddMonoidHom`, their degrees agree". Genuine stream-C-internal / generic-point work that I (Claude) plan to attempt separately; it's independent of your BRIDGE work.

---

## Files you'll touch

- `HasseWeil/FormalGroupBridge.lean` (new) — or extend `OmegaPullbackCoeff.lean`.
- `HasseWeil/PullbackCoeff.lean` — close the 2 sorries via step B.
- `HasseWeil/Hasse/Separability.lean` — promote worker-J's witness forms to unconditional.
- `HasseWeil/DualIsogeny.lean` — call `exists_dual_of_constructor` with your `dualOf` (from the III.5.6 + III.5.7 chain).
- `HasseWeil/DegreeQuadraticForm.lean` — call `degree_quadratic_closed` with step-D inputs.

---

## Existing axiom-clean consumer API (your drop-in targets)

All verified axiom-clean (`propext`, `Classical.choice`, `Quot.sound`):

**`DualIsogeny.lean`** (commits `dff85e9`, `48f9778`):
- `exists_dual_of_construction` — single-α dual builder
- `exists_dual_of_constructor` — universal dual builder
- `dual_add_of_trace_witnesses` — **T-III-6-005 witness form** (just landed)
- `dual_add_of_sum_witnesses` — simpler alternative form
- `isogDual_comp_self_of_witness`, `self_comp_isogDual_of_witness`, `degree_dual_of_witness`

**`DegreeQuadraticForm.lean`** (commits `9b0bcd7`, `0ed9511`, `8b87978`, `5d89e3c`, `a48843b`):
- `degree_quadratic_of_dualChain_witnesses` — core step-4 consumer
- `sq_degree_eq_sq_of_dual_comp_witness` + `degree_eq_abs_of_dual_comp_witness`
- `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` — AddMonoidHom-level algebra
- `degree_quadratic_closed` — **full consumer** with explicit witness bundle
- `isogSmulSub_degree_quadratic_closed` — **specialised call site** for the `β_qf r s = isogSmulSub α r s` family

**`Hasse/BoundOfWitnesses.lean`** (commit `4066811`):
- `hasse_bound_of_all_witnesses` — consolidated V.1 capstone

---

## References

- Silverman, *The Arithmetic of Elliptic Curves*, III.5.2–7, III.6.1–3.
- Project plan: `.mathlib-quality/formal_group_plan.md`.
- Ticket files:
  - `.mathlib-quality/tickets/formal/T-IV-BRIDGE-001-omega-coeff-is-formal-leading.md`
  - `.mathlib-quality/tickets/formal/T-IV-BRIDGE-003-formal-additivity.md`
  - `.mathlib-quality/tickets/ec/T-III-5-002-pullback-additivity.md`
  - `.mathlib-quality/tickets/ec/T-III-5-006-ring-hom-end.md`
  - `.mathlib-quality/tickets/ec/T-III-6-005-dual-additivity.md`
  - `.mathlib-quality/tickets/ec/T-III-6-009-deg-quadratic-form.md`
