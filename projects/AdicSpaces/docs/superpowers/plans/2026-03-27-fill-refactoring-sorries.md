# Fill Refactoring Sorries — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fill the 5 sorries introduced by the Wedhorn definition audit (removing HasRestrictionMaps class, upgrading IsSheafy, switching to CompleteTopCommRingCat sheaf).

**Architecture:** Three independent workstreams: (A) Prop 8.2 for Huber rings via Lemma 7.45, (B) discrete gluing via Čech exactness, (C) presheaf/sheaf in CompleteTopCommRingCat via existing restriction map infrastructure.

**Tech Stack:** Lean 4, Mathlib (RingTheory.Localization, Topology.UniformSpace.Completion, Topology.Sheaves)

---

## Dependency Graph

```
Task 1: mem_prime_of_rational_subset (generalize discrete→Huber)
   ↓
Task 2: isUnit_canonicalMap_s_of_huber (Prop 8.2(a))
   ↓
Task 3: restrictionMapAlg_continuous_of_huber (Prop 8.2(b))
   ↓
Task 5: structurePresheaf in CompleteTopCommRingCat
   ↓
Task 6: structureSheaf in CompleteTopCommRingCat

Task 4: discrete gluing (independent)
```

## Sorries to Fill

| # | File:Line | Sorry | Task |
|---|-----------|-------|------|
| 1 | Presheaf.lean:268 | `isUnit_canonicalMap_s_of_huber` | Task 2 |
| 2 | Presheaf.lean:278 | `restrictionMapAlg_continuous_of_huber` | Task 3 |
| 3 | TateAcyclicity.lean:391 | `gluing` discrete | Task 4 |
| 4 | StructureSheaf.lean:127 | `structurePresheaf` | Task 5 |
| 5 | StructureSheaf.lean:132 | `structureSheaf` | Task 6 |

---

### Task 1: Generalize `mem_prime_of_rational_subset` to Huber rings

**Files:**
- Modify: `Adic spaces/Presheaf.lean` (after line 533)

**Context:** The discrete proof (`mem_prime_of_rational_subset_discrete`, line 489) shows: if `R(T'/s') ⊆ R(T/s)` and prime `p ∋ D.s` but `D'.s ∉ p`, then contradiction. It constructs a Spa point with `supp = p` using `exists_mem_spa_supp_eq_of_prime` (discrete-only). For general Huber rings, use Lemma 7.45 (`exists_mem_spa_supp_ge_of_nonOpen_prime` in Lemma745.lean:617) which gives `supp ⊇ p`.

- [ ] **Step 1: State the generalized lemma**

```lean
/-- For a Huber ring, if `R(T'/s') ⊆ R(T/s)` and prime `p ∋ D.s`,
then `D'.s ∈ p` (Wedhorn Proposition 7.52). -/
theorem mem_prime_of_rational_subset {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    {p : Ideal A} (hp : p.IsPrime) (hDs : D.s ∈ p) : D'.s ∈ p := by
  sorry
```

- [ ] **Step 2: Prove using case split on open/non-open primes**

Split on whether `p` is open:
- **Open prime:** Use `exists_mem_spa_supp_eq_of_prime` (works for open primes in any ring, see StructureSheaf.lean:590+)
- **Non-open prime:** Use `exists_mem_spa_supp_ge_of_nonOpen_prime` from Lemma745.lean:617

Both cases: get `v ∈ Spa A A⁺` with `p ≤ v.supp`, then `D.s ∈ v.supp`, so `v ∉ rationalOpen D.T D.s`. But the inclusion forces `v ∉ rationalOpen D'.T D'.s`, so `D'.s ∈ v.supp ⊇ p`... wait, we need `D'.s ∈ p`, not `D'.s ∈ v.supp`. Since `p ≤ v.supp` and `D'.s ∉ p`, we'd need `D'.s ∉ v.supp`, meaning `v ∈ rationalOpen D'.T D'.s`... then `v ∈ rationalOpen D.T D.s` (by inclusion), contradicting `D.s ∈ v.supp`. So `D'.s ∈ p` by contradiction. ✓

- [ ] **Step 3: Verify with `lean_diagnostic_messages`**

- [ ] **Step 4: Commit**

---

### Task 2: Fill `isUnit_canonicalMap_s_of_huber` (Prop 8.2(a))

**Files:**
- Modify: `Adic spaces/Presheaf.lean:268`

- [ ] **Step 1: Replace sorry with proof using Task 1**

Follow the discrete proof template (line 537-560):
1. Show `D'.s ∈ Ideal.radical (Ideal.span {D.s})` using `Ideal.radical_eq_sInf` + `mem_prime_of_rational_subset`
2. Extract `n` and `a` with `D'.s^n = a * D.s`
3. Show `D.s` is a unit in `Localization.Away D'.s`

- [ ] **Step 2: Verify with `lean_diagnostic_messages`**

- [ ] **Step 3: Commit**

---

### Task 3: Fill `restrictionMapAlg_continuous_of_huber` (Prop 8.2(b))

**Files:**
- Modify: `Adic spaces/Presheaf.lean:278`
- May need: `Adic spaces/LocalizationTopology.lean` (new helper lemma)

**Context:** Must show the algebraic lift `IsLocalization.Away.lift D.s ...` is continuous from `D.topology` (localization topology on `Localization.Away D.s`) to the completion topology on `presheafValue D'`. This is the content of Wedhorn Proposition 8.2(1) — the localization topology is defined precisely to make restriction maps continuous.

- [ ] **Step 1: Understand the localization topology basis**

Read `LocalizationTopology.lean` — the basis `locNhd D.P D.T D.s n` consists of elements whose product with `I^n` lands in the localization subring. The restriction map sends basis elements to basis elements.

- [ ] **Step 2: Prove continuity via basis**

Show that for each `n`, the preimage of a basis neighborhood in `D'` contains a basis neighborhood in `D`. This uses the algebraic structure of the lift.

- [ ] **Step 3: Verify and commit**

---

### Task 4: Fill discrete `gluing` (independent)

**Files:**
- Modify: `Adic spaces/TateAcyclicity.lean:391`

**Context:** For discrete A, `presheafValue D ≅ Localization.Away D.s` (bijective completion embedding). The gluing says: given compatible sections `f D ∈ presheafValue D` for each cover piece D, there exists a global section `x ∈ presheafValue C.base` restricting to each `f D`.

- [ ] **Step 1: Use bijection to work in localizations**

Via `coeRingHom_bijective_of_discrete`, transport everything to `Localization.Away`. Then the problem is purely algebraic: given compatible elements in localizations that agree on overlaps, find a global element.

- [ ] **Step 2: Construct global section**

For a rational covering `{R(Tᵢ/sᵢ)}` of `R(T/s)`, the global section is constructed by:
- Each `f D` is `aD / sD^nD` in the localization
- Compatibility on overlaps means they agree in common localizations
- Since the `sᵢ` generate the unit ideal in `Localization.Away s`, we can patch

This is the exactness of the Čech complex for localization.

- [ ] **Step 3: Verify and commit**

---

### Task 5: Build `structurePresheaf` in `CompleteTopCommRingCat`

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean:127`

**Context:** All the pieces exist:
- `presheafValueObj D : CompleteTopCommRingCat` (Presheaf.lean:221)
- `restrictionMapCont D D' h : presheafValueObj D ⟶ presheafValueObj D'` (Presheaf.lean:427)
- Functoriality: `restrictionMap_comp` (line 353) and `restrictionMap_id` (line 396)

The challenge: the presheaf must be defined on ALL opens, not just rational ones. Rational opens form a basis for the topology on Spa.

- [ ] **Step 1: Define presheaf on rational opens as a basis presheaf**

Use Mathlib's `TopCat.Presheaf` API. For each open `U`, if `U = rationalOpen D.T D.s`, assign `presheafValueObj D`. For general opens, sorry (or use stalks/colimits).

Actually, the simplest correct approach: define it on the basis of rational opens and extend. Mathlib has `TopologicalSpace.Opens.IsBasis` and sheaf extension from basis machinery.

- [ ] **Step 2: Verify functoriality**

Use `restrictionMap_comp` and `restrictionMap_id` to verify the presheaf axioms.

- [ ] **Step 3: Verify and commit**

---

### Task 6: Build `structureSheaf` in `CompleteTopCommRingCat`

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean:132`

- [ ] **Step 1: Combine presheaf with sheaf condition**

The sheaf condition follows from `IsSheafy` — which asserts embedding + gluing for rational coverings. For the categorical sheaf condition, need to show this implies the sheaf axiom for all covers (not just rational ones).

- [ ] **Step 2: Verify and commit**

---

## Feasibility Assessment

| Task | Difficulty | Likely Outcome |
|------|-----------|----------------|
| 1 | Medium | **Fillable** — Lemma 7.45 is proved, just need to combine with prime argument |
| 2 | Easy | **Fillable** — follows directly from Task 1, same proof as discrete |
| 3 | Hard | **May need sorry** — localization topology continuity is deep |
| 4 | Hard | **May need sorry** — Čech exactness for rational coverings |
| 5 | Medium | **Fillable** — all components exist, just assembly |
| 6 | Hard | **May need sorry** — sheaf condition from basis to all opens |
