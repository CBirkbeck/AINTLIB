# Tate Acyclicity Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `ValuationSpectrum.tateAcyclicity` in `Adic spaces/LaurentRefinement.lean:642` sorry-free under `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]` (the strongly noetherian Tate setting), closing Wedhorn Theorem 8.28(b).

**Architecture:** Two parallel tracks. Track S ("separation") uses Wedhorn Corollary 8.32 (faithful flatness of product restriction) to prove `restrictionMapHom_injective` and `tateAcyclicity` Part 1. Track G ("gluing") uses Wedhorn Lemma 8.33 (Laurent-cover exactness, already scaffolded as compositions in `f1020be`) plus Lemma 8.34 (refinement transfer) to prove `tateAcyclicity` Part 2. Both tracks ultimately require `exists_spa_point_in_rationalOpen` for the non-open prime case.

**Tech Stack:** Lean 4 v4.29.0-rc3 + Mathlib v4.29.0-rc3. Project modules: `Presheaf`, `StructureSheaf`, `PresheafTateStructure`, `LaurentRefinement`, `TopologyComparison`, `LaurentCoverExact`, `Lemma745`, `CechCohomology`.

---

## File Structure

**Files modified:**
- `Adic spaces/StructureSheaf.lean` — add `exists_spa_point_in_rationalOpen_of_nonOpen_prime`, `productRestriction_faithfullyFlat`, update `base_s_in_annihilator_radical_of_covering` callsites.
- `Adic spaces/PresheafTateStructure.lean` — rewrite `restrictionMapHom_injective` via Cor 8.32.
- `Adic spaces/LaurentRefinement.lean` — fill 11 bridge-chain sorries; fill `tateAcyclicity` Part 2.
- `Adic spaces/TopologyComparison.lean` — if needed, add `presheafValueTateQuotientEquiv_strong` that discharges the 5 hypotheses under `[IsTateRing A] [IsNoetherianRing P.A₀]`.

**Files created:**
- `Adic spaces/IteratedRational.lean` — housing the Q3-STEP2C/2D primitives (isolate to keep `LaurentRefinement.lean` readable).
- `Adic spaces/Lemma834.lean` — refinement transfer (Wedhorn Lemma 8.34).
- `Adic spaces/Cor832.lean` — faithful flatness of product restriction (Wedhorn Cor 8.32).

**Root import:**
- `Adic spaces.lean` — add the three new imports.

---

## Dependency graph

```
Layer A (separation)          Layer G (gluing)

spa_point_nonOpen  ────┐      Q3-STEP2C minus ───┐
  (Phase 1)            │         (Phase 2)        │
                       │                          │
                       ▼                          ▼
              Cor 8.32 faithful flat      Q3-STEP4 hypothesis discharges
                  (Phase 3a)                   (Phase 3b)
                       │                          │
                       ▼                          ▼
               restrictionMapHom_injective     laurentMinusBridge (proved)
                  (Phase 4a)                   (auto via composition)
                       │                          │
                       ▼                          │
                tateAcyclicity Part 1              │
                  (Phase 5a)                       │
                                                   ▼
Q3-STEP2C plus + Q3-STEP2D ──────────────► laurentPlusBridge (proved)
  (Phase 2b)                                (auto via composition)
                                                   │
                                                   ▼
                                         Q3-STEP5 compat theorems
                                              (Phase 4b)
                                                   │
                                                   ▼
                                   laurentCover_gluing_presheaf (proved)
                                              (auto)
                                                   │
                                                   ▼
                                        Lemma 8.34 refinement
                                              (Phase 5b)
                                                   │
                                                   ▼
                                         tateAcyclicity Part 2
                                              (Phase 6)
                                                   │
                                                   ▼
                                       tateAcyclicity sorry-free
                                              (Phase 7)
```

Phases 1, 2, and 3 can run in parallel.

---

## Success criteria

1. `lake build` succeeds with 0 errors.
2. `grep "declaration uses \`sorry\`" <(lake build 2>&1)` reports fewer Tate-core sorries (target: 103 → ≤ 80 at plan end, with all 11 bridge-chain sorries closed and the Layer A / Part 2 sorries also closed).
3. `lake env lean "Adic spaces/LaurentRefinement.lean"` reports no sorry on `tateAcyclicity`.
4. `#print axioms ValuationSpectrum.tateAcyclicity` shows no custom axioms (only Lean's standard ones).
5. All 3 downstream files (`StructureSheaf`, `PresheafTateStructure`, `LaurentRefinement`) still compile.

---

## Phase 1 — Spa-point at non-open prime (Layer A unblocker)

**⚠️ Blocked pending Bourbaki CA III §2.8 formalization.** Per memory
`project_T001_completion_route.md`: the completion route requires
`completedLocSubring_isAdicComplete` (Presheaf.lean:476), which itself
depends on `Submodule.isClosed_of_fg` for complete T2 linearly-topologized
rings (Bourbaki CA III §2.8) — not in Mathlib. 20+ supporting theorems
already proved on the way to this blocker.

**Consequence for this plan:** Phase 1 cannot land without upstream
Mathlib work or an alternative proof route (e.g., valuation-ring
domination over `Frac(A/p)` from the reviewer's Q1 guidance, which is
itself a ~120-line Zorn-based addition).

**Downstream consequence:** Phase 5a (Cor 8.32 faithful flatness) depends
on Phase 1's Spa-point construction. Without Phase 1, Phase 5a remains
blocked, which leaves `restrictionMapHom_injective` (PresheafTateStructure.lean:1162)
sorry'd, which leaves `tateAcyclicity` Part 1 blocked.

**Realistic scope for this plan, given the blocker:**
- Phases 2, 2b, 3, 4 are tractable → `laurentCover_gluing_presheaf` and all
  11 bridge-chain sorries close.
- Phase 5b (Lemma 8.34) is tractable and independent of Phase 1.
- Phase 6.2 (`tateAcyclicity` Part 2) is tractable via Phase 5b.
- **`tateAcyclicity` Part 1 remains blocked.**

Construct `exists_spa_point_in_rationalOpen_of_nonOpen_prime` via Wedhorn Lemma 7.45 on `presheafValue_pairOfDefinition`. Route: for a non-open prime `p` with `C.base.s ∉ p`, complete `A/p` and use the Tate unit there.

### Task 1.1: State `exists_spa_point_in_rationalOpen_of_nonOpen_prime`

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean` (after line 671, before the quarantined section)

- [ ] **Step 1: Add the statement (sorry'd)**

```lean
/-- For a non-open prime `p` with `s ∉ p`, construct a Spa point over `p`
inside `rationalOpen T s`. Uses Wedhorn Lemma 7.45 on `presheafValue_pairOfDefinition`.

**Mathematical content.** The map `A → presheafValue D₀` (at `D₀ = globalLocData P`)
is dense, and the completion `Â := presheafValue (globalLocData P)` is a complete
strongly noetherian Tate ring. Any non-open prime `p ⊂ A` lifts to a prime `p̂ ⊂ Â`
(via the flatness of `A → Â`). By Lemma 7.45 on `Â`, there is a continuous
valuation `v̂ ∈ Spa(Â, Â⁺)` with `p̂ ≤ v̂.supp`. Pulling back `v̂` along `A → Â`
gives `v ∈ Spa(A, A⁺)` with `p ≤ v.supp`, and `v ∈ rationalOpen T s` by the
control Lemma 7.45 provides on the ideal of definition. -/
theorem exists_spa_point_in_rationalOpen_of_nonOpen_prime
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (T : Finset A) (s : A)
    (p : Ideal A) [p.IsPrime]
    (hp_notOpen : ¬IsOpen (p : Set A))
    (hs_notin : s ∉ p) :
    ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  sorry
```

- [ ] **Step 2: Verify the file still compiles**

Run: `lake env lean "Adic spaces/StructureSheaf.lean" 2>&1 | grep error`
Expected: no output (no errors).

- [ ] **Step 3: Commit**

```bash
git add "Adic spaces/StructureSheaf.lean"
git commit -m "$(cat <<'EOF'
Layer-A: state exists_spa_point_in_rationalOpen_of_nonOpen_prime

Adds the non-open prime variant of exists_spa_point_in_rationalOpen as a
sorry'd theorem. Proof route: Wedhorn Lemma 7.45 on presheafValue_pairOfDefinition.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 1.2: Prove via Lemma 7.45 on the completion

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean`

- [ ] **Step 1: Look up `exists_mem_spa_supp_ge_of_nonOpen_prime` signature**

Run: `grep -n "exists_mem_spa_supp_ge_of_nonOpen_prime" "Adic spaces/Lemma745.lean"`
Expected: theorem returning `∃ v ∈ Spa A A⁺, p ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp`.

- [ ] **Step 2: Understand what the hypotheses convert to in our setting**

The Lemma 7.45 version in the project takes `A` complete (IsAdicComplete hypothesis). For our `A` strongly noetherian Tate (not necessarily complete), apply it to `Â := presheafValue (globalLocData P)`. The identification `Spa(A, A⁺) ≃ Spa(Â, Â⁺)` (Wedhorn Prop 7.23) pulls the result back.

- [ ] **Step 3: Write the proof**

```lean
theorem exists_spa_point_in_rationalOpen_of_nonOpen_prime
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (T : Finset A) (s : A)
    (p : Ideal A) [p.IsPrime]
    (hp_notOpen : ¬IsOpen (p : Set A))
    (hs_notin : s ∉ p) :
    ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  -- Step 1: Lift p to a prime of Â = presheafValue (globalLocData P)
  --   (via flatness of A → Â or via Ideal.comap of canonicalMap).
  -- Step 2: Apply Lemma 7.45 on Â to get v̂ ∈ Spa(Â, Â⁺) with p̂ ≤ v̂.supp.
  -- Step 3: Identify Spa(A, A⁺) ≃ Spa(Â, Â⁺) (Wedhorn Prop 7.23).
  -- Step 4: Pull v̂ back along A → Â to v ∈ Spa(A, A⁺).
  -- Step 5: Show v ∈ rationalOpen T s from the Lemma 7.45 bound on ideal of definition.
  -- Step 6: Show p ≤ v.supp.
  --
  -- Outline below; each subgoal is a lemma.
  sorry  -- full proof ~60 lines; see detailed subtasks in task 1.2a-1.2f
```

Given the complexity, split into subtasks:

**Task 1.2a: Lift the prime.** Define `p̂ : Ideal (presheafValue (globalLocData P))` as the image (via flat base change) or preimage (via comap of canonicalMap).

**Task 1.2b: Verify `p̂` is prime and not-open.** The flatness of `A → Â` ensures primeness; non-openness transfers because the canonicalMap is continuous.

**Task 1.2c: Apply Lemma 7.45.** Run `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime` at `Â` with `P̂ = presheafValue_pairOfDefinition P (globalLocData P)`. Requires `IsNoetherianRing (locSubring (globalLocData P).P (globalLocData P).T (globalLocData P).s)` — check this is provable from `[IsNoetherianRing P.A₀]`.

**Task 1.2d: Identify Spa(A) with Spa(Â).** Use/build the Wedhorn Prop 7.23 bridge. If not present, may need to be added as an auxiliary lemma.

**Task 1.2e: Pull valuation back.** For `v̂ : Spv Â`, define `v := v̂.comap canonicalMap : Spv A` and show `v ∈ Spa(A, A⁺)` + `p ≤ v.supp`.

**Task 1.2f: Show `v(t) ≤ v(s)` for `t ∈ T`.** Use the Lemma 7.45 bound on the ideal of definition; `s ∉ p` gives `v̂(s) > 0` via the reduction `Â → Â/p̂ → Frac(Â/p̂)`.

- [ ] **Step 4: Run `lake build` and verify no errors (sorries OK)**

Run: `lake build 2>&1 | tail -3`
Expected: build succeeds.

- [ ] **Step 5: Commit**

```bash
git add "Adic spaces/StructureSheaf.lean"
git commit -m "Layer-A: prove exists_spa_point_in_rationalOpen_of_nonOpen_prime via Â completion"
```

### Task 1.3: Update `base_s_in_annihilator_radical_of_covering` callers

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean` (hasSeparation hSpa hypothesis can now be discharged)
- Modify: `Adic spaces/StructureSheaf.lean` (combining open + non-open cases)

- [ ] **Step 1: Build the unified Spa-point existence**

```lean
theorem exists_spa_point_in_rationalOpen
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (T : Finset A) (s : A)
    (p : Ideal A) [p.IsPrime]
    (hs_notin : s ∉ p) :
    ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  by_cases hopen : IsOpen (p : Set A)
  · exact exists_spa_point_in_rationalOpen_of_isOpen_prime T s p hopen hs_notin
  · exact exists_spa_point_in_rationalOpen_of_nonOpen_prime P T s p hopen hs_notin
```

- [ ] **Step 2: Update `rationalCovering_hasSeparation` to use this internally**

The current `hSpa` hypothesis becomes derivable; could be removed OR kept for flexibility.
Keep the hypothesis but add a second lemma `rationalCovering_hasSeparation_of_strong`
that calls `exists_spa_point_in_rationalOpen` to discharge it.

```lean
theorem rationalCovering_hasSeparation_of_strong
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ x y : presheafValue C.base, _ := fun x y hxy =>
  rationalCovering_hasSeparation P C
    (fun p hp hs_notin => exists_spa_point_in_rationalOpen P C.base.T C.base.s p hs_notin)
    x y hxy
```

- [ ] **Step 3: Verify build, commit**

```bash
lake build
git add "Adic spaces/StructureSheaf.lean" "Adic spaces/LaurentRefinement.lean"
git commit -m "Layer-A: unify exists_spa_point_in_rationalOpen and thread through hasSeparation"
```

---

## Phase 2 — Iterated rational identification (Wedhorn Lemma 2.13)

### Task 2.1: Create `IteratedRational.lean` file

**Files:**
- Create: `Adic spaces/IteratedRational.lean`
- Modify: `Adic spaces.lean` (add import)

- [ ] **Step 1: Create file with namespace and imports**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13)

For a rational datum `D₀ : RationalLocData A` on a strongly noetherian Tate
ring `A`, and for iterated data (`laurent±Datum D₀ f` for `f : A`), the
iterated rational localization `presheafValue (laurent±Datum D₀ f)` is
isomorphic to a single rational localization of `B := presheafValue D₀`.

This module houses the proofs of:
- `presheafValue_iteratedMinus_equiv` (LHS of the minus-branch Q3-STEP2C).
- `presheafValue_iteratedPlus_equiv` (LHS of the plus-branch Q3-STEP2C).
- `presheafValue_trivialPlus_fSubX_equiv` (Q3-STEP2D, non-discrete f−X
  quotient over generic B).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

end ValuationSpectrum
```

- [ ] **Step 2: Import in root**

Edit `Adic spaces.lean` to add: `import «Adic spaces».IteratedRational`

- [ ] **Step 3: Build + commit**

```bash
lake build
git add "Adic spaces/IteratedRational.lean" "Adic spaces.lean"
git commit -m "IteratedRational: create module for Wedhorn Lemma 2.13 primitives"
```

### Task 2.2: Prove `presheafValue_iteratedMinus_equiv` forward ring hom

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`
- Modify: `Adic spaces/LaurentRefinement.lean` (move stub here or reference)

- [ ] **Step 1: Establish helper — `canonicalMap(D₀.s)` is a unit in B**

```lean
section IteratedMinusBuilders

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

theorem canonicalMap_D₀s_isUnit (D₀ : RationalLocData A) :
    IsUnit (D₀.canonicalMap D₀.s) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map D₀.coeRingHom
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

end IteratedMinusBuilders
```

- [ ] **Step 2: Build the forward RingHom (at the uncompleted localization level)**

```lean
variable (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
variable (D₀ : RationalLocData A)
  [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
variable (f : A)

/-- The composite A → B → Loc_B(canonicalMap f). -/
noncomputable def iteratedMinus_baseHom :
    A →+* Localization.Away (D₀.canonicalMap f) :=
  (algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f))).comp
    D₀.canonicalMap

/-- `D₀.s * f` becomes a unit in `Localization.Away (canonicalMap f)` via
the base hom. -/
theorem iteratedMinus_D₀s_mul_f_isUnit :
    IsUnit (iteratedMinus_baseHom P D₀ f (D₀.s * f)) := by
  rw [iteratedMinus_baseHom, RingHom.comp_apply, map_mul, map_mul]
  exact ((canonicalMap_D₀s_isUnit D₀).map (algebraMap _ _)).mul
    (IsLocalization.Away.algebraMap_isUnit (D₀.canonicalMap f))

/-- Forward ring hom `Localization.Away (D₀.s * f) → Localization.Away (canonicalMap f)`,
obtained by the universal property of localization using `D₀.s * f` being a unit. -/
noncomputable def iteratedMinus_forwardLocHom :
    Localization.Away (D₀.s * f) →+*
      Localization.Away (D₀.canonicalMap f) :=
  IsLocalization.Away.lift (D₀.s * f) (iteratedMinus_D₀s_mul_f_isUnit P D₀ f)
```

- [ ] **Step 3: Build the forward RingHom to the completion**

```lean
/-- Forward RingHom from `presheafValue (laurentMinusDatum D₀ f)` uncompleted
level to the RHS completion. -/
noncomputable def iteratedMinus_forwardToCompletion :
    Localization.Away (D₀.s * f) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  (iteratedMinusDatum_B P D₀ f).coeRingHom.comp
    (iteratedMinus_forwardLocHom P D₀ f)
```

- [ ] **Step 4: Show the forward hom is continuous**

This is the KEY technical step. Use the characterization of `laurentMinusDatum.uniformSpace`
and the localization topology on the RHS. The key fact: `D₀.canonicalMap` is continuous,
and the forward hom factors through it.

```lean
theorem iteratedMinus_forwardToCompletion_continuous :
    @Continuous _ _ (laurentMinusDatum D₀ f).topology _
      (iteratedMinus_forwardToCompletion P D₀ f) := by
  -- Outline:
  -- 1. Source topology: localization topology at D₀.s * f with laurentMinusDatum.T.
  --    Basic opens: ideals generated by (P.I^n) scaled by fractions.
  -- 2. Target topology: completion uniformity of (iteratedMinusDatum_B P D₀ f).
  --    Basic opens: ideals generated by (P_B.I^n) scaled by fractions.
  -- 3. Under canonicalMap, P.I maps into P_B.I (bounded subsets map to bounded
  --    subsets under continuous ring hom between Tate rings).
  -- 4. Hence basic neighborhoods of 0 map into basic neighborhoods of 0.
  sorry
```

- [ ] **Step 5: Extend to completion**

```lean
/-- Forward RingHom between the two completions. -/
noncomputable def iteratedMinus_forwardHom :
    presheafValue (laurentMinusDatum D₀ f) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) := by
  letI : UniformSpace (Localization.Away (D₀.s * f)) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (D₀.s * f)) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (D₀.s * f)) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom
    (iteratedMinus_forwardToCompletion P D₀ f)
    (iteratedMinus_forwardToCompletion_continuous P D₀ f)
```

- [ ] **Step 6: Verify and commit**

```bash
lake env lean "Adic spaces/IteratedRational.lean" 2>&1 | grep error
lake build 2>&1 | tail -3
git add "Adic spaces/IteratedRational.lean"
git commit -m "IteratedRational: build forward hom for iteratedMinus_equiv (continuity sorry'd)"
```

### Task 2.3: Prove `presheafValue_iteratedMinus_equiv` backward ring hom

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`

- [ ] **Step 1: Build backward loc hom**

```lean
/-- Composite B → A (not directly possible) is instead: B → completion B, then
observe Loc_B(canonicalMap f) → completion B using isUnit of canonicalMap f. Wait —
backward direction: we need RHS → LHS.

LHS underlying: Localization.Away (D₀.s * f) over A.
RHS underlying: Localization.Away (canonicalMap f) over B.

Backward approach: build Localization.Away (canonicalMap f) → Completion(LHS).
  - B → Completion(LHS) via: presheafValue D₀ → presheafValue (laurentMinusDatum D₀ f)
    through the restriction map (since laurentMinus is a subset of D₀).
  - In this map, the image of canonicalMap f must be a unit (since f ∈ D₀.s * f
    localization becomes a unit after the laurentMinus is applied).
  - Hence B → Loc_B(canonicalMap f) → Completion(LHS). -/
```

- [ ] **Step 2: Show `canonicalMap f` maps to a unit in the LHS completion**

In `presheafValue (laurentMinusDatum D₀ f)`, `D₀.s * f` is a unit (localization element). Hence both `D₀.s` and `f` individually are units (a product of elements is a unit iff each is, in a commutative ring — this requires `D₀.s` to be already a unit there, which it is since laurentMinusDatum.s = D₀.s · f, so `algebraMap(D₀.s · f) = algebraMap(D₀.s) · algebraMap(f)` is a unit; but individually, `D₀.s` might not be a unit in `Localization.Away(D₀.s · f)` unless we know it is).

Actually wait — in `Localization.Away(D₀.s · f)`, is `D₀.s` a unit? We have (D₀.s · f) a unit, and if `f` is also a unit, then `D₀.s = (D₀.s · f) · f⁻¹` is a unit. But `f` might not be a unit.

Revised approach: use that `D₀.s · f` is a unit to invert. `algebraMap(D₀.s · f) · u = 1` for some `u ∈ Loc_A(D₀.s · f)`. Then `algebraMap(D₀.s) · (algebraMap(f) · u) = 1`, so `algebraMap(D₀.s)` has a right inverse, hence is a unit (commutative ring). Similarly `algebraMap(f)`.

```lean
theorem algebraMap_D₀s_isUnit_in_laurentMinus :
    IsUnit (algebraMap A (Localization.Away (D₀.s * f)) D₀.s) := by
  -- D₀.s divides D₀.s * f, which is a unit in Loc(D₀.s * f).
  have h : algebraMap A _ (D₀.s * f) = algebraMap A _ D₀.s * algebraMap A _ f := map_mul _ _ _
  have hu : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [h] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem algebraMap_f_isUnit_in_laurentMinus :
    IsUnit (algebraMap A (Localization.Away (D₀.s * f)) f) := by
  have h : algebraMap A _ (D₀.s * f) = algebraMap A _ D₀.s * algebraMap A _ f := map_mul _ _ _
  have hu : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [h] at hu
  exact isUnit_of_mul_isUnit_right hu
```

- [ ] **Step 3: Build the backward loc hom**

```lean
/-- The canonical image of `canonicalMap f` in `presheafValue (laurentMinusDatum D₀ f)`
is a unit. -/
theorem canonicalMap_f_isUnit_in_laurentMinus :
    IsUnit ((laurentMinusDatum D₀ f).canonicalMap f) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map _ (algebraMap_f_isUnit_in_laurentMinus P D₀ f)

/-- Backward ring hom: B → presheafValue (laurentMinusDatum D₀ f). This is
just the restriction map. -/
noncomputable def iteratedMinus_backwardB :
    presheafValue D₀ →+* presheafValue (laurentMinusDatum D₀ f) :=
  restrictionMapHom D₀ (laurentMinusDatum D₀ f) (laurentMinus_subset D₀ f)

/-- The backward hom sends canonicalMap f to a unit. -/
theorem iteratedMinus_backwardB_canonicalMap_f_isUnit :
    IsUnit (iteratedMinus_backwardB P D₀ f (D₀.canonicalMap f)) := by
  -- restrictionMapHom factors through canonicalMap: restrictionMap ∘ canonicalMap_D₀ =
  -- canonicalMap of the refined datum.
  sorry -- use restrictionMap.canonicalMap compatibility
```

- [ ] **Step 4: Build the backward loc lift**

```lean
/-- Backward loc lift. -/
noncomputable def iteratedMinus_backwardLocLift :
    Localization.Away (D₀.canonicalMap f) →+*
      presheafValue (laurentMinusDatum D₀ f) :=
  IsLocalization.Away.lift (D₀.canonicalMap f)
    (iteratedMinus_backwardB_canonicalMap_f_isUnit P D₀ f)
```

- [ ] **Step 5: Show continuous**

Similar obligation to Task 2.2 Step 4. Sorry'd with detailed comment.

- [ ] **Step 6: Extend to completion**

```lean
noncomputable def iteratedMinus_backwardHom :
    presheafValue (iteratedMinusDatum_B P D₀ f) →+*
      presheafValue (laurentMinusDatum D₀ f) := by
  sorry -- mirror the forward construction
```

- [ ] **Step 7: Commit**

```bash
git add "Adic spaces/IteratedRational.lean"
git commit -m "IteratedRational: build backward hom for iteratedMinus_equiv"
```

### Task 2.4: Show the two homs are inverse

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`

- [ ] **Step 1: Show round trip on dense image (algebraMap A side)**

```lean
theorem iteratedMinus_round_trip_coeRingHom (a : Localization.Away (D₀.s * f)) :
    iteratedMinus_backwardHom P D₀ f
      (iteratedMinus_forwardHom P D₀ f ((laurentMinusDatum D₀ f).coeRingHom a)) =
      (laurentMinusDatum D₀ f).coeRingHom a := by
  sorry -- compute on algebraMap generators and divByS, extend by ring-hom-ness
```

- [ ] **Step 2: Show round trip on dense image (other side)**

```lean
theorem iteratedMinus_round_trip_coeRingHom_other (b : Localization.Away (D₀.canonicalMap f)) :
    iteratedMinus_forwardHom P D₀ f
      (iteratedMinus_backwardHom P D₀ f ((iteratedMinusDatum_B P D₀ f).coeRingHom b)) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom b := by
  sorry
```

- [ ] **Step 3: Extend to completion by density + T2**

```lean
theorem iteratedMinus_round_trip_full :
    (iteratedMinus_backwardHom P D₀ f).comp
      (iteratedMinus_forwardHom P D₀ f).toRingHom =
    RingHom.id (presheafValue (laurentMinusDatum D₀ f)) := by
  -- Use UniformSpace.Completion density + T2 extension uniqueness.
  sorry
```

- [ ] **Step 4: Commit**

```bash
git add "Adic spaces/IteratedRational.lean"
git commit -m "IteratedRational: round-trip for iteratedMinus homs"
```

### Task 2.5: Assemble `presheafValue_iteratedMinus_equiv`

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`
- Modify: `Adic spaces/LaurentRefinement.lean` (delete the stub, import IteratedRational)

- [ ] **Step 1: Define the full equiv**

```lean
/-- **Iterated rational identification, minus branch (Wedhorn Lemma 2.13).** -/
noncomputable def presheafValue_iteratedMinus_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) ≃+*
      presheafValue (iteratedMinusDatum_B P D₀ f) where
  toFun := iteratedMinus_forwardHom P D₀ f
  invFun := iteratedMinus_backwardHom P D₀ f
  left_inv := fun x => by
    have h := iteratedMinus_round_trip_full P D₀ f
    exact congr_fun (congr_arg DFunLike.coe h) x
  right_inv := fun y => by
    have h := iteratedMinus_round_trip_full_reverse P D₀ f
    exact congr_fun (congr_arg DFunLike.coe h) y
  map_mul' := map_mul _
  map_add' := map_add _
```

- [ ] **Step 2: Remove the stub from LaurentRefinement.lean**

Delete the sorry'd `presheafValue_iteratedMinus_equiv` def in `LaurentRefinement.lean:504`. It's now defined in `IteratedRational.lean`.

- [ ] **Step 3: Verify everything still compiles**

```bash
lake build
```

Expected: 3080 jobs success. Sorry count should have net −1 (new def replaces old sorry, provided tasks 2.2–2.4 left some sorries, count changes are local).

- [ ] **Step 4: Commit**

```bash
git add "Adic spaces/IteratedRational.lean" "Adic spaces/LaurentRefinement.lean"
git commit -m "IteratedRational: assemble presheafValue_iteratedMinus_equiv"
```

---

## Phase 2b — Iterated plus + `f − X` primitive

### Task 2.6: Prove `presheafValue_iteratedPlus_equiv` (mirror of 2.2–2.5)

Same structure as Phase 2.2–2.5 but with `laurentPlusDatum` and `iteratedPlusDatum_B` in place of their minus counterparts. The underlying localization on both sides is `Localization.Away (D₀.s)` (LHS) vs `Localization.Away (1 : B) ≃ B` (RHS), with T-extension by f.

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`
- Modify: `Adic spaces/LaurentRefinement.lean` (delete the stub)

- [ ] **Task 2.6a: Build forward loc hom `Loc_A(D₀.s) → Loc_B(1)` via A → B → Loc_B(1).**

`Loc_B(1) ≃ B` so the composite is just `A → B`, i.e., `D₀.canonicalMap`. `D₀.s` must map to a unit: `D₀.canonicalMap(D₀.s) = canonicalMap(D₀.s)` is a unit (we already proved this). ✓

```lean
noncomputable def iteratedPlus_forwardLocHom :
    Localization.Away D₀.s →+* presheafValue D₀ :=
  IsLocalization.Away.lift D₀.s (canonicalMap_D₀s_isUnit D₀)
```

- [ ] **Task 2.6b: Show this is continuous wrt the plus topologies.**

The plus topology on `Loc_A(D₀.s)` extends `T = insert f D₀.T` (forces f to be power-bounded). The plus topology on `Loc_B(1) = B` (via iteratedPlusDatum_B with T_B = {canonicalMap f}) also extends by canonicalMap f. So the forward hom preserves these. ~50 lines.

- [ ] **Task 2.6c: Extend to completion, build backward, show round trip.** Similar to 2.2–2.4.

- [ ] **Task 2.6d: Assemble the full equiv, commit.**

### Task 2.7: Prove `presheafValue_trivialPlus_fSubX_equiv` (Q3-STEP2D — the genuinely new primitive)

**Files:**
- Modify: `Adic spaces/IteratedRational.lean`

**Target statement:**
```lean
noncomputable def presheafValue_trivialPlus_fSubX_equiv
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    presheafValue (iteratedPlusDatum_B P D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f)
```

The LHS is `Completion(B, τ_plus)` where `τ_plus` extends B's ring of definition by `canonicalMap f`. The RHS is `TateAlgebra B ⧸ (algebraMap(canonicalMap f) − X)`.

**Strategy:** both are universal complete nonarchimedean `B`-algebras in which `canonicalMap f` is power-bounded. We build a forward RingHom LHS → RHS by sending `algebraMap b` to itself (the map is `B` on constants) and extending. The backward map uses the fact that in RHS, `X = algebraMap(canonicalMap f)` (by the quotient relation), so RHS is generated over `B` by `algebraMap(canonicalMap f)` (which already lives in `B`). Hence RHS is a quotient of `B` modulo some relations, which is the completion LHS.

Subtasks:

- [ ] **Task 2.7a: Build forward hom `Completion(B, τ_plus) → B⟨X⟩ ⧸ (alg(cf) − X)`.** The idea: in the RHS, we have a ring map `B → B⟨X⟩ ⧸ (alg(cf) − X)` (the algebraMap). This is continuous wrt B's original topology. We extend it along the plus completion via the universal property. ~40 lines.

- [ ] **Task 2.7b: Build backward hom.** The RHS is `B⟨X⟩ ⧸ (alg(cf) − X)`. There's a ring hom from `B⟨X⟩` to `Completion(B, τ_plus)` sending `X` to the image of `canonicalMap f` (which is power-bounded in the τ_plus topology, hence gives a Tate-algebra eval). This passes to the quotient because `alg(cf) − X` maps to 0 (X = cf in the completion). ~60 lines.

- [ ] **Task 2.7c: Round trip.** Both composites are identity on generators (constants `b ∈ B` and the element `X = cf`). Extend by density. ~30 lines.

- [ ] **Task 2.7d: Assemble, commit.**

```bash
git add "Adic spaces/IteratedRational.lean"
git commit -m "IteratedRational: prove presheafValue_trivialPlus_fSubX_equiv (Q3-STEP2D)"
```

---

## Phase 3 — `presheafValueTateQuotientEquiv` hypothesis discharges at B (Q3-STEP4)

### Task 3.1: Discharge `hb` — `invS (iteratedMinusDatum_B)` is power-bounded

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean` (replace the sorry in `laurentMinusBridge`)

- [ ] **Step 1: Understand the goal.**

`invS D = 1 - D.T.sum * divByS D.s` or similar (check `invS` definition in TopologyComparison.lean).

Actually `invS` is the specific Tate-algebra element: for the minus datum with `s_B = canonicalMap f`, `invS = 1 - 1 * divByS(canonicalMap f) = 1 - 1/canonicalMap(f)` in `Loc_B(canonicalMap f)`.

This element being power-bounded follows from `canonicalMap f` being power-bounded... actually no, 1/canonicalMap f being power-bounded in the minus completion.

- [ ] **Step 2: Prove it.**

```lean
theorem iteratedMinus_hb :
    TopologicalRing.IsPowerBounded (invS (iteratedMinusDatum_B P D₀ f)) := by
  sorry
```

- [ ] **Step 3: Commit.**

### Task 3.2: Discharge `hcs` — `CompleteSpace (quotientTUniformSpace (canonicalMap f))`

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean`

Use `quotientTTopology_completeSpace` from `TopologyComparison.lean:1283` at `A := presheafValue D₀`. Check hypotheses (is `P` or noeth needed?).

- [ ] **Step 1: Invoke the existing theorem.**

```lean
theorem iteratedMinus_hcs :
    @CompleteSpace _ (quotientTUniformSpace (D₀.canonicalMap f)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  exact quotientTTopology_completeSpace (D₀.canonicalMap f)
```

- [ ] **Step 2: Commit.**

### Task 3.3: Discharge `ht0`

Similar to 3.2 — use `quotientTTopology_t0Space`.

### Task 3.4: Discharge `hcont_eval`

Use `tateQuotientToPresheafHom_continuous` with appropriate ideal. Substantial — may require ~40 lines to construct the ideal structure.

### Task 3.5: Discharge `hdense`

Use `locToQuotientOneSubfX_gen_denseRange_canonical` at A := B. May require switching to `presheafValueCanonicalQuotientEquiv` if the canonical/T-topology mismatch bites.

### Task 3.6: Plug discharges back into `laurentMinusBridge`

- [ ] **Step 1: Rewrite `laurentMinusBridge` proof replacing the 5 sorries.**

```lean
noncomputable def laurentMinusBridge ... :=
  (presheafValue_iteratedMinus_equiv P D₀ f).trans
    (presheafValueTateQuotientEquiv (iteratedMinusDatum_B P D₀ f)
      (iteratedMinus_hb P D₀ f)
      (iteratedMinus_hcs P D₀ f)
      (iteratedMinus_ht0 P D₀ f)
      (iteratedMinus_hcont_eval P D₀ f)
      (iteratedMinus_hdense P D₀ f))
```

- [ ] **Step 2: Build, verify `laurentMinusBridge` has 0 sorries.**

```bash
lake env lean "Adic spaces/LaurentRefinement.lean" 2>&1 | grep "sorry"
```

- [ ] **Step 3: Commit.**

---

## Phase 4 — Bridge compat theorems (Q3-STEP5)

### Task 4.1: Prove `laurentPlusBridge_restrictionMap`

**Target:**
```lean
theorem laurentPlusBridge_restrictionMap ... :
    ∀ x : presheafValue D₀,
      laurentPlusBridge P D₀ f
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1
```

With `laurentPlusBridge = iteratedPlus_equiv ≫ trivialPlus_fSubX_equiv`, compute the LHS on `x : presheafValue D₀`:
1. `restrictionMap D₀ (laurentPlusDatum D₀ f) x` lives in `presheafValue(laurentPlusDatum D₀ f)`.
2. Apply `iteratedPlus_equiv` → `presheafValue(iteratedPlusDatum_B)`.
3. Apply `trivialPlus_fSubX_equiv` → `B₁_gen(canonicalMap f)`.
4. Show this equals `(epsilonHom_gen (canonicalMap f) x).1 = mk(algebraMap x)` in `B₁_gen(canonicalMap f)`.

Subtasks:

- [ ] **Task 4.1a: Prove on a dense subring — the image of `canonicalMap`.** For `x = D₀.canonicalMap a`, both sides reduce to `mk(algebraMap a)` in the quotient. ~40 lines.

- [ ] **Task 4.1b: Extend by continuity + density + T2 of the target.** `B₁_gen` is T2 (noetherian Tate quotient). The map `x ↦ laurentPlusBridge(restrictionMap x)` and `x ↦ (epsilonHom_gen x).1` are both continuous (or at least algebraic — check), agree on dense subring, hence agree everywhere.

- [ ] **Task 4.1c: Commit.**

### Task 4.2: Prove `laurentMinusBridge_restrictionMap` (symmetric)

Same structure as 4.1, mutatis mutandis.

### Task 4.3: Prove `laurentBridge_delta_eq_zero_of_compat`

This is the 3×3 diagram chase using the two preceding compat theorems. The target:

```lean
deltaMap_gen (canonicalMap f) (τ_plus uplus, τ_minus uminus) = 0
```

given that `uplus` and `uminus` are compatible on every common refinement.

**Strategy:** apply `hcompat` at the specific double-refinement `laurentMinusDatum (laurentPlusDatum D₀ f) f` (or similar) to get a common restriction, then use the two bridge restriction identities to show their difference maps to 0 in `B₁₂_gen`.

- [ ] **Task 4.3a: Construct the common refinement `D₃`.** `D₃` has `s = D₀.s · f` and `T` containing both plus's T and minus's T. ~20 lines.

- [ ] **Task 4.3b: Apply `hcompat` at `D₃` + the two bridge restriction identities.**

- [ ] **Task 4.3c: Show `deltaMap_gen` vanishes on the resulting pair.** Use the explicit form of `deltaMap_gen` and the computed restrictions. ~30 lines.

- [ ] **Task 4.3d: Commit.**

---

## Phase 5a — Cor 8.32 + `restrictionMapHom_injective` rewrite

### Task 5.1: Create `Cor832.lean` with faithful flatness

**Files:**
- Create: `Adic spaces/Cor832.lean`
- Modify: `Adic spaces.lean` (add import)

- [ ] **Step 1: State the target**

```lean
/-- **Wedhorn Cor 8.32**: for a rational covering C, the product restriction
  `presheafValue C.base → ∏_{D ∈ C.covers} presheafValue D`
is faithfully flat. -/
theorem productRestriction_faithfullyFlat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ (D : ↥C.covers), presheafValue D.1) := by
  sorry
```

- [ ] **Step 2: Each individual restriction is flat.** Use `presheafValue_flat_of_tateQuotient` (or the `restrictionMap_isLocalization` once restrictionMapHom_surj is unblocked — but the surjection is blocked too). Alternative: use Phase 2 iso + `flat_quotient_oneSubfX_general`. ~30 lines.

- [ ] **Step 3: Product of flat modules is flat.** `Module.Flat.pi`. ~5 lines.

- [ ] **Step 4: Faithfully flat = flat + every prime of `C.base` extends to a prime in the product.** The Spa-point radical argument from `base_s_in_annihilator_radical_of_covering` (extended to generic primes) shows no prime of `presheafValue C.base` is in the annihilator of all restrictions. ~80 lines.

- [ ] **Step 5: Import in root, commit.**

```bash
git add "Adic spaces/Cor832.lean" "Adic spaces.lean"
git commit -m "Cor832: prove productRestriction_faithfullyFlat"
```

### Task 5.2: Rewrite `restrictionMapHom_injective` via Cor 8.32

**Files:**
- Modify: `Adic spaces/PresheafTateStructure.lean:1162`

- [ ] **Step 1: Replace the sorry with the flatness route.**

```lean
theorem restrictionMapHom_injective
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Function.Injective (restrictionMapHom D₀ D h) := by
  -- Consider the trivial covering by D alone of D₀.
  -- Apply Cor 8.32 to get faithful flatness of the single-element product restriction.
  -- Faithfully flat → injective.
  sorry  -- ~15 lines
```

Needs `[IsNoetherianRing (locSubring D.P D.T D.s)]` hypothesis or `P` — which isn't in the current signature. May require signature tightening OR a self-contained argument using just that D itself is a flat localization.

- [ ] **Step 2: Build + commit.**

---

## Phase 5b — Lemma 8.34 refinement transfer

### Task 5.3: Create `Lemma834.lean`

**Files:**
- Create: `Adic spaces/Lemma834.lean`
- Modify: `Adic spaces.lean` (add import)

**Target:** Wedhorn Lemma 8.34 — if acyclicity holds for the Laurent cover, it holds for any rational covering by induction on `|T|`.

Substantial proof (~80-120 lines). Uses:
- `CechCohomology.Refinement` infrastructure (check if present).
- `laurentCover_gluing_presheaf` as base case.
- Induction on the size of the finite set `T`.

Subtasks similar to 5.1.

- [ ] **Task 5.3a: Set up refinement API.**
- [ ] **Task 5.3b: Base case (Laurent cover).**
- [ ] **Task 5.3c: Inductive step.**
- [ ] **Task 5.3d: Assemble and commit.**

---

## Phase 6 — Finish `tateAcyclicity`

### Task 6.1: Rewrite `tateAcyclicity` Part 1 via Cor 8.32

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean:659-667`

Replace the `restrictionMapHom_injective` call with the faithful-flatness-derived injectivity (since Part 1 already uses `restrictionMapHom_injective`, if that's rewritten in 5.2, Part 1 auto-works).

- [ ] **Step 1: Verify Part 1 closes without changes.**
- [ ] **Step 2: If hypotheses don't match, tighten signatures.**

### Task 6.2: Rewrite `tateAcyclicity` Part 2 via Lemma 8.34

**Files:**
- Modify: `Adic spaces/LaurentRefinement.lean:698`

Replace the `sorry` at Part 2 with a call to `Lemma834.refinement_transfer` applied to the Laurent-cover base case.

- [ ] **Step 1: Construct the call.** ~20 lines.
- [ ] **Step 2: Verify `tateAcyclicity` is sorry-free.**

```bash
lake env lean "Adic spaces/LaurentRefinement.lean" 2>&1 | grep -A 3 "tateAcyclicity"
```

Expected: no sorry on tateAcyclicity.

- [ ] **Step 3: Verify axioms are clean.**

```bash
echo "#print axioms ValuationSpectrum.tateAcyclicity" | lake env lean --stdin
```

Expected: only `propext, Classical.choice, Quot.sound` (no custom axioms).

- [ ] **Step 4: Commit.**

---

## Phase 7 — Downstream cleanup

### Task 7.1: Propagate `tateAcyclicity` usage

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean` — `isSheafy_ofStronglyNoetherianTate_flat` (line 996) uses `tateAcyclicity`; update if needed.
- Modify: `Adic spaces/LaurentRefinement.lean` — `rationalCovering_hasGluing` automatically works once `tateAcyclicity` is sorry-free.

- [ ] **Step 1: Fix any broken callsites.**
- [ ] **Step 2: Run full `lake build`, sorry count check.**

Expected: sorries reduced significantly from 103. Target: ≤ 80 (bridge chain + layer A + Part 2 all closed).

- [ ] **Step 3: Commit.**

### Task 7.2: Update tracker and plan docs

- [ ] **Step 1: Mark Q3-STEP2C, Q3-STEP2D, Q3-STEP4, Q3-STEP5 as DONE in `.mathlib-quality/tickets.md`.**
- [ ] **Step 2: Add a closing note to `docs/plans/2026-04-14-tate-acyclicity-finish-plan.md`.**
- [ ] **Step 3: Commit.**

---

## Cross-cutting concerns

1. **Typeclass propagation.** Several tasks add `P : PairOfDefinition A` / `[IsNoetherianRing P.A₀]` to signatures. Downstream callers (gluing theorems) will need these too. Audit and tighten in each phase.

2. **Axiom hygiene.** The entire project eschews custom axioms per `feedback_no_axioms`. Every `sorry` filled must not introduce `axiom` statements. Verify via `#print axioms` after each major phase.

3. **Line packing.** Per `feedback_line_packing`, theorem parameters should be packed densely up to 100-char limit.

4. **Phase 1 can be skipped for an initial partial run** — it only blocks Phase 5a (Cor 8.32). Phases 2, 3, 4 can deliver a sorry-free `laurentCover_gluing_presheaf` without Phase 1.

5. **Build after each commit.** `lake build` must succeed at every commit (the build is fast, ~7s incremental).

6. **Commit discipline.** Per project CLAUDE.md, commit frequently with descriptive messages referencing Wedhorn sections.

---

## Total effort estimate (original plan)

| Phase | Est. lines | Est. sessions | Blocks |
|---|---|---|---|
| 1. Spa-point nonOpen | ~180 | 1–2 | 5a |
| 2. Iterated rational minus | ~200 | 1–2 | 3 |
| 2b. Iterated rational plus + f−X | ~250 | 2 | 4, 6 |
| 3. Hypothesis discharges | ~150 | 1 | 4 |
| 4. Bridge compat | ~100 | 1 | 6 |
| 5a. Cor 8.32 + injective rewrite | ~150 | 1 | 6 |
| 5b. Lemma 8.34 | ~120 | 1 | 6 |
| 6. tateAcyclicity assembly | ~30 | 0.5 | 7 |
| 7. Cleanup | ~30 | 0.5 | — |
| **Total** | **~1210** | **~9–11 sessions** | |

Aggressive single-session targets: Phases 2 + 3 alone unlock `laurentMinusBridge` sorry-free. Phase 5b alone (assuming laurentCover_gluing_presheaf is a given) unlocks Part 2.

---

## 2026-04-15 reviewer-guided plan revision

Second reviewer round (2026-04-15) delivered three decisive architectural pivots.
The plan above is **superseded** on the critical path by the following revised
sequencing.

### Key directives

**Q1 (Phase 1/5a retirement):** abandon the Spa-point-at-non-open-prime route
on the critical path. Replace with **standard-cover reduction** — any rational
covering reduces to a cover by elements `{f₀, ..., fₙ}` with `Ideal.span {fᵢ} = ⊤`.
Once reduced, the acyclicity proof is algebraic/topological on the Čech complex,
and no non-open-prime valuation construction is required. This entirely bypasses
the Bourbaki CA III §2.8 blocker.

**Q2 (hybrid continuity):** for the iterated rational equivs (minus and plus):
- **Forward** direction — use the universal property: the algebraic generators
  land as products of visibly power-bounded elements, so continuity follows from
  existing `locTopology_continuous_lift`-style lemmas.
- **Backward** direction — a single direct ring-of-definition comparison.
  Identify a common open ring of definition on the common algebraic localization;
  the algebraic inverse carries one neighborhood basis into the other.
- **Round trips** — use `UniformSpace.Completion.extension_unique` /
  `Completion.ext` / `Completion.map_unique`. Agreement on the dense algebraic
  subring plus T2 of the target gives equality. No Banach-dense-subring detour.

**Q3 (generic Example 6.38):** the single new primitive to build is
**Wedhorn Example 6.38** *over an arbitrary complete strongly noetherian Tate
base `B` and any power-bounded (in the relevant branch) `b ∈ B`*:
- Plus: `𝒪_X(R(b/1)) ≃+* B⟨X⟩ / (b − X)`.
- Minus: `𝒪_X(R(1/b)) ≃+* B⟨X⟩ / (1 − b·X)`.

Drop the `[IsDomain]`-based Krull injectivity entirely. The primitive is smaller
than originally scoped:
- Forward (TateAlgebra side → presheafValue): `X ↦ b` (plus) / `X ↦ 1/b` (minus);
  the relation maps to 0, hence factors through the quotient.
- Backward (dense algebraic localization → TateAlgebra quotient): `f ↦ X` (plus)
  / `1/f ↦ X` (minus). Continuity via the same coefficient estimate as the
  existing `(1−sX)` work, over `B` instead of `A`.
- Extend to completion via `UniformSpace.Completion.extensionHom`.
- Round trips via the Completion ext-API.
- Completeness of `B⟨X⟩/(b−X)` comes from "ideals in noetherian Tate rings are
  closed" (already proved in the project).

Once this primitive exists generically, **Lemma 2.13** (iterated rational) lets
us instantiate it at `B := presheafValue D₀`, `b := D₀.canonicalMap f` to close
the Laurent-branch bridges.

### Revised phase order

| Rev | Phase | Est. lines | Replaces |
|---|---|---|---|
| R1 | **Standard-cover reduction** — reduce `RationalCovering A` to a cover by `{fᵢ}` with `Ideal.span {fᵢ} = ⊤`, then induct via Laurent-cover gluing to recover acyclicity for the original cover. | ~120 | Phase 5b (Lemma 8.34) and part of Phase 5a |
| R2 | **Iterated rational minus continuity (hybrid)** — finish the 4 sorries in `IteratedRational.lean` using Q2's hybrid strategy. | ~60 | Phase 2 tail |
| R3 | **Generic Example 6.38 plus + minus** — Q3's primitive, over arbitrary complete strongly noetherian Tate `B`. | ~200 | Phase 2b + parts of Phase 3 |
| R4 | **Iterated rational plus continuity** — mirror of R2. | ~60 | Phase 2 mirror |
| R5 | **Instantiate at `B := presheafValue D₀`** — collapse the 4 `laurent±Bridge` stubs and their compat theorems. | ~50 | Phase 4 |
| R6 | **`tateAcyclicity` final assembly** — Part 1 via `productRestriction` injectivity (derived from standard-cover reduction), Part 2 via Laurent gluing + R1 refinement transfer. | ~50 | Phase 6 |
| R7 | **Cleanup** — retire quarantined sorries, remove dead code, update tickets. | ~30 | Phase 7 |
| **Total revised** | | **~570** | **~5 sessions** |

### Retired / deferred from original plan

- **Phase 1 (Spa-point non-open prime)** — retired from critical path. Revisit
  only if downstream theorem still needs it after R1–R7 land.
- **Phase 5a (Cor 8.32 faithful-flatness)** — retired. The standard-cover
  reduction (R1) gives separation via a more direct route: for each `x ∈
  presheafValue C.base` with `restrictionMap x = 0` on every cover piece, use
  the standard-cover unit decomposition to construct `1 · x` as a sum that
  evaluates to `0`.
- **Phase 3 (hypothesis discharges for `presheafValueTateQuotientEquiv`)** —
  subsumed by R3 (the generic Example 6.38 primitive uses its own completion
  API directly, not via `presheafValueTateQuotientEquiv`).

### Remaining blockers

None on the critical path. R1–R7 are all independent of the Bourbaki CA III §2.8
blocker.

### Suggested order for the next execution session

1. **R1** first — it's the most structural change and unblocks R5/R6.
2. **R3** next — the generic Example 6.38 is the load-bearing primitive.
3. R2 / R4 / R5 can run in parallel once R3 is in place.
4. R6 / R7 close the plan.

---

## 2026-04-15 execution progress (50 commits from fc6e61b)

Substantial execution batch across the revised plan. Major deliverables:

### R3 complete (generic Example 6.38 primitives)
- `example638Plus_equiv` and `example638Minus_equiv` both fully proved in
  `Adic spaces/Example638.lean` (1500 lines, extracted from IteratedRational to
  break import cycle).
- Forward maps via `evalHomBounded` at `b` (plus) / `invS` (minus), backward
  via dense algebraic localization + completion extension.
- Round trips via `Completion.ext'` on `coeRingHom` image.
- Complete `plusFSubXIdeal` topology infrastructure (quotient complete +
  T2 mirroring `oneSubfXIdeal`).

### R1 scaffolded (standard-cover reduction)
- `Adic spaces/StandardCover.lean` (~180 lines).
- `StandardCover` structure + `RationalCovering.refines_by_standard_cover`
  proved modulo 1 targeted Nullstellensatz helper + 1 pathological edge case.
- `tateAcyclicity_via_standard_cover` delegates to existing `tateAcyclicity`
  (circular but consistent; breaking the circularity is R6 work).

### R5 (instantiation of R3 at B := presheafValue D₀)
- `laurentMinusBridge`: 5 sorries → 2 (hnoeth_B + hcont_eval_B hoisted as
  explicit hypotheses; body sorry-free via `presheafValueCanonicalQuotientEquiv`).
- `laurentPlusBridge`: via `presheafValue_trivialPlus_fSubX_equiv` now closed
  using `example638Plus_equiv.symm` (no sorry in body). Hypotheses hoisted.

### Bridge compatibility theorems (R5 / R6 tail)
- `laurentPlusBridge_restrictionMap` and `laurentMinusBridge_restrictionMap`:
  both main theorems fully proved, reduced to 1 atomic sub-sorry each
  (`_restrictionMap_canonicalMap`, the action of the iterated-rational equiv
  on canonicalMap values).
- `laurentBridge_delta_eq_zero_of_compat`: main theorem fully proved via new
  `LaurentOverlapBridgeCompatible` predicate bundling the 3 original
  intertwining obligations into one primitive (the Laurent-analog of
  Example 6.38, capturing a bivariate evalHomBounded-style bridge).

### Wedhorn 2.13 (iterated rational) partial progress
- `presheafValue_iteratedPlus_equiv` and `presheafValue_iteratedMinus_equiv`:
  uncompleted-level infrastructure fully built (13 new helper lemmas, 0
  sorries). Equivs themselves have concrete `toFun` and `invFun`; remaining
  sorries are: 4 continuity obligations (Wedhorn Prop 8.2 analog A → B) +
  2 round-trip density obligations.

### Q1 (non-open prime Spa-point) — retired per reviewer
- 3 Q1-FIX callsites consolidated into 1 shared helper
  `spa_point_nonOpen_of_rational_subset`, documented as Bourbaki CA III §2.8
  blocked (unchanged critical-path status — retired per 2026-04-15 reviewer).

### Supporting helpers
- `gluing_of_finer_rational` and `tateAcyclicity_gluing_via_refinement`
  (`Adic spaces/RationalRefinement.lean` + `LaurentRefinement.lean`): gluing
  transfer under refinement — both sorry-free.
- `restrictionMapHom_canonicalMap`: the key compatibility between
  `restrictionMap` and canonicalMap (used throughout the compat proofs).

### Cleanup
- Removed deprecated iteratedMinus infrastructure (~538 lines) superseded by
  R3. `IteratedRational.lean` trimmed from 1542 lines to 66 lines (just
  `canonicalMap_s_isUnit` + `restrictionMapHom_canonicalMap` helpers).

### Current sorry distribution (bridge chain + acyclicity)

| Location | Count | Content |
|---|---|---|
| `LaurentRefinement.lean` | ~8 | Wedhorn 2.13 continuity + round trip (6) + Laurent overlap bridge (1) + tateAcyclicity Part 2 (1) |
| `StandardCover.lean` | 2 | Nullstellensatz helper (1) + pathological edge (1) |
| `Presheaf.lean` (shared Q1) | 1 | Bourbaki-blocked Spa-point helper (retired from critical path) |

Everything else in the bridge chain is now **concretely structured** with
no vague sorries — all remaining sorries point to specific, named
mathematical obligations that are individually tractable or documented as
upstream-Mathlib blockers.

### Critical path to `tateAcyclicity` sorry-free

1. Wedhorn 2.13 equivs: fill 4 continuity + 2 round-trip sorries → closes 2
   equivs + 2 `_restrictionMap_canonicalMap` sub-sorries cascade.
2. Laurent-analog of Example 6.38 (the new overlap primitive) → closes
   `laurentOverlapBridge_exists_compatible` → closes delta-vanishing.
3. With 1+2 done: `laurentCover_gluing_presheaf` becomes sorry-free.
4. Fill `tateAcyclicity` Part 2 via `tateAcyclicity_gluing_via_refinement`
   applied to a Laurent refinement (standard-cover reduction + Laurent gluing).

Estimated remaining effort post-2026-04-15 session: ~3-4 sessions for the
Wedhorn 2.13 route + ~2 sessions for the Laurent overlap primitive.
