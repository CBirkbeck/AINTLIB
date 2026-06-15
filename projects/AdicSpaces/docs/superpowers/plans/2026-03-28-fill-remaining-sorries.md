# Fill Remaining Refactoring Sorries — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the 4 remaining sorries introduced by the Wedhorn definition audit, building the necessary localization/topology/category infrastructure.

**Architecture:** Four independent workstreams with one dependency (Ticket B depends on A). Each ticket produces a self-contained compilable result. The key Wedhorn references are: Proposition 8.2 (restriction maps), Lemma 7.45 (analytic points), Remark 8.20 (sheaf condition), and standard localization gluing (Čech H⁰).

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3, `lake build` for verification.

**IMPORTANT:** Do NOT modify `Adic spaces/PresheafTateStructure.lean` — another agent is working on it.

---

## Tickets

```
TICKET-A: Čech H⁰ exactness (discrete gluing)
    ↓
TICKET-B: structureSheaf in CompleteTopCommRingCat

TICKET-C: Non-open prime case (Prop 8.2 + Lemma 7.45) [independent]

TICKET-D: Localization topology continuity (Prop 8.2(b)) [independent]
```

---

### TICKET-A: Čech H⁰ Exactness for Discrete Localization Coverings

**Sorry:** `Adic spaces/TateAcyclicity.lean:399`
**Goal state:**
```
⊢ ∃ x', ∀ (D : ↥C.covers), (restrictionMapAlg C.base ↑D ⋯) x' = f D
```
where `f D : presheafValue D.1` are compatible sections, `C` is a `RationalCovering A`, and `[DiscreteTopology A]`.

**Wedhorn reference:** This is the sheaf condition for the structure presheaf on rational covers. For discrete rings, it reduces to standard localization patching.

**Mathematical content:** Given compatible elements in localizations `Localization.Away D.s` (one per cover piece), construct a global element in `Localization.Away C.base.s` mapping to each. This uses:
1. The covering condition implies the images of `{D.s}` generate the unit ideal in `Localization.Away C.base.s`
2. Partition of unity: `∑ cᵢ · sᵢᴺ = 1` in the localization
3. Global element: `x' = ∑ cᵢ · sᵢᴺ · fᵢ` (where fᵢ are lifts of the compatible sections)

**Mathlib API:** `Localization.existsUnique_algebraMap_eq_of_span_eq_top` — gluing for localizations when elements span the unit ideal. This works for the base ring R; we need the version for `Localization.Away s`.

**Files:**
- Modify: `Adic spaces/TateAcyclicity.lean:399`
- May add helper lemmas in same file (before the sorry)

- [ ] **Step 1: Show covering implies unit ideal generation**

State and prove (or sorry) a lemma: for a `RationalCovering C` with `[DiscreteTopology A]`, the images of `{D.s : D ∈ C.covers}` in `Localization.Away C.base.s` generate the unit ideal.

```lean
private theorem covers_span_top_of_discrete [DiscreteTopology A]
    (C : RationalCovering A) :
    Ideal.span (C.covers.image (fun D => algebraMap A (Localization.Away C.base.s) D.s) : Set _) = ⊤ := by
  sorry -- Use C.hcover + exists_mem_spa_supp_eq_of_prime
```

The proof: by contradiction. If the span is not ⊤, it's contained in a maximal ideal 𝔪. Pull back to get a prime 𝔭 in A containing C.base.s (since 𝔪 lives in the localization at C.base.s). Then 𝔭 ∋ all D.s. But the covering condition says every point in R(T/s) is in some R(Tᵢ/sᵢ), and the point corresponding to 𝔭 should be in some R(Tᵢ/sᵢ), meaning sᵢ ∉ 𝔭. Contradiction.

- [ ] **Step 2: Transport compatible sections to localizations**

Use `coeRingHom_bijective_of_discrete` to define `f' D : Localization.Away D.s` from `f D : presheafValue D.1` via the bijection inverse.

- [ ] **Step 3: Apply Mathlib's localization gluing**

Use `Localization.existsUnique_algebraMap_eq_of_span_eq_top` (or its generalization) to get the global element. May need to adapt the Mathlib API to work with `Localization.Away` instead of the base ring.

- [ ] **Step 4: Transport back and verify**

Show the global element in `Localization.Away C.base.s`, when mapped via `restrictionMapAlg`, equals each `f D`.

- [ ] **Step 5: Verify with `lean_diagnostic_messages` and commit**

---

### TICKET-B: structureSheaf in CompleteTopCommRingCat

**Sorry:** `Adic spaces/StructureSheaf.lean:222`
**Goal:** `Sheaf CompleteTopCommRingCat (SpaTop A)` — the structure sheaf as a sheaf of complete topological rings.

**Wedhorn reference:** Remark 8.20 — 𝒪_X is a sheaf of topological rings iff it's a sheaf of rings AND product restriction maps are topological embeddings.

**Strategy:** The `structurePresheaf` (already built) is valued in `CompleteTopCommRingCat` using `sectionsSubring` with discrete uniformity. The sheaf condition reduces to the Type-level sheaf condition via forgetful functors.

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean:222`
- Modify: `Adic spaces/CompleteTopCommRingCat.lean` (add categorical instances)

- [ ] **Step 1: Add HasLimits/PreservesLimits for CompleteTopCommRingCat**

Add instances showing the forgetful functor `CompleteTopCommRingCat → Type` preserves limits and reflects isomorphisms. This may require `sorry` for some instances.

- [ ] **Step 2: Use isSheaf_iff_isSheaf_comp**

Reduce the sheaf condition to the Type level:
```lean
(TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CompleteTopCommRingCat) _).mpr ...
```

- [ ] **Step 3: Show Type-level sheaf condition via isLocallyFraction**

The presheaf values at the Type level ARE `sectionsSubring U`, which is a sheaf by `subpresheafToTypes.isSheaf isLocallyFraction`.

- [ ] **Step 4: Verify and commit**

---

### TICKET-C: Non-Open Prime Case of Proposition 8.2

**Sorry:** `Adic spaces/Presheaf.lean:366`
**Goal state:**
```
p : Ideal A, hp : p.IsPrime, hp_notOpen : ¬IsOpen ↑p, hDs : D.s ∈ p
⊢ D'.s ∈ p
```
given `rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s`.

**Wedhorn reference:** Proposition 7.52, using Lemma 7.45.

**Mathematical content:** For non-open prime 𝔭, use Lemma 7.45 to get `v ∈ Spa A A⁺` with `𝔭 ≤ v.supp`. The key subtlety: we need `D'.s ∉ v.supp` (not just `D'.s ∉ 𝔭`) to get the contradiction. This works when `v.supp = 𝔭` (Lemma 7.45's noetherian case), but only gives `𝔭 ≤ v.supp` in general.

**Available API:** `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma745.lean:617)
- Requires: `[IsAdicComplete P.I P.A₀]`, `[PlusSubring A]`, `(A⁺ : Set A) ⊆ P.A₀`
- Gives: `∃ v ∈ Spa A A⁺, 𝔭 ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp`

**The proof argument:** By contradiction, assume `D'.s ∉ 𝔭`. Need `v ∈ Spa A A⁺` with:
- `D.s ∈ v.supp` (from `D.s ∈ 𝔭 ≤ v.supp`)
- `D'.s ∉ v.supp` (need this for `v ∈ rationalOpen D'.T D'.s`)
Since `D'.s ∉ 𝔭` but `𝔭 ≤ v.supp`, we don't automatically get `D'.s ∉ v.supp`.

**Resolution options:**
1. Add `[IsAdicComplete P.I P.A₀]` + `[IsNoetherianRing P.A₀]` hypotheses to get `v.supp = 𝔭`
2. Use the `¬P.idealOfDefinition ≤ v.supp` condition from Lemma 7.45 to argue that `v.supp` is "small enough"
3. Restructure: instead of by-contradiction on a single prime, use the radical characterization with a different construction for non-open primes

**Files:**
- Modify: `Adic spaces/Presheaf.lean:366`
- May add import for `Lemma745` if not already imported

- [ ] **Step 1: Check if Lemma 7.45's output suffices**

Read the proof of `exists_mem_spa_supp_ge_of_nonOpen_prime` and check if `¬P.idealOfDefinition ≤ v.supp` (the extra condition) helps. If `idealOfDefinition` is small, this constrains `v.supp`.

- [ ] **Step 2: Add completeness hypotheses if needed**

The theorem `mem_prime_of_rational_subset_nonOpen` currently assumes only `[IsHuberRing A]`. If we need `[IsAdicComplete P.I P.A₀]`, add it. This is mathematically correct — Wedhorn Prop 8.2 is for complete affinoid rings.

- [ ] **Step 3: Prove using Lemma 7.45**

Apply `exists_mem_spa_supp_ge_of_nonOpen_prime` to get `v`, then show the rational subset inclusion gives the contradiction.

- [ ] **Step 4: Verify and commit**

---

### TICKET-D: Localization Topology Continuity (Prop 8.2(b))

**Sorry:** `Adic spaces/Presheaf.lean:439`
**Goal:** The algebraic lift `IsLocalization.Away.lift D.s ...` is continuous from `D.topology` to the completion topology on `presheafValue D'`.

**Wedhorn reference:** Proposition 8.2(1) — the unique continuous ring homomorphism σ: A⟨T/s⟩ → A⟨T'/s'⟩.

**Mathematical content:** The localization topology on `Localization.Away D.s` is generated by `locNhd D.P D.T D.s n` (neighborhoods from the ring of definition). The restriction map preserves these neighborhoods: the image of `locNhd D ... n` under the lift lands in `locNhd D' ... n` (roughly). Composing with the continuous completion embedding gives continuity to the completion.

**Key API:**
- `locNhd P T s n : AddSubgroup (Localization.Away s)` — neighborhoods
- `locBasis P T s : RingSubgroupsBasis (Localization.Away s)` — basis structure
- `D.topology : TopologicalSpace (Localization.Away D.s)` — the localization topology
- `UniformSpace.Completion.uniformContinuous_coe` — completion embedding is uniformly continuous

**Files:**
- Modify: `Adic spaces/Presheaf.lean:439`
- May add: `Adic spaces/LocalizationTopology.lean` (new helper lemma about lift preserving locNhd)

- [ ] **Step 1: State the key lemma — lift preserves locNhd**

```lean
theorem lift_locNhd_subset (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) (n : ℕ) :
    (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s ...)) '' (locNhd D.P D.T D.s n)
    ⊆ locNhd D'.P D'.T D'.s n := by
  sorry
```

This is the content of Wedhorn's proof: the lift sends `Iⁿ·D/(s^k)` to `Iⁿ·D'/(s'^k)`.

- [ ] **Step 2: Derive continuity from neighborhood preservation**

A ring homomorphism preserving neighborhoods is continuous for the ring-subgroup-basis topologies.

- [ ] **Step 3: Compose with completion embedding**

The completion embedding `Localization.Away D'.s → presheafValue D'` is continuous. Compose to get continuity of the full map.

- [ ] **Step 4: Verify and commit**

---

## Priority Order

1. **TICKET-A** (discrete gluing) — most self-contained, enables TICKET-B
2. **TICKET-B** (structureSheaf) — depends on A, completes the sheaf construction
3. **TICKET-C** (non-open primes) — independent, uses existing Lemma 7.45
4. **TICKET-D** (continuity) — independent, deepest localization topology work

## Files Summary

| File | Tickets | Changes |
|------|---------|---------|
| `TateAcyclicity.lean` | A | Fill sorry:399 + helper lemmas |
| `StructureSheaf.lean` | B | Fill sorry:222 |
| `CompleteTopCommRingCat.lean` | B | Add categorical instances |
| `Presheaf.lean` | C, D | Fill sorry:366 and sorry:439 |
| `LocalizationTopology.lean` | D | Add `lift_locNhd_subset` helper |
| `Lemma745.lean` | C | (read-only, API consumer) |
