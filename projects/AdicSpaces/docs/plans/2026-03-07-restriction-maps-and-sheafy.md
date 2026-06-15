# Restriction Maps & IsSheafy Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Remove the 3 sorries in `restrictionMap`, `restrictionMap_comp`, `restrictionMap_id` (Presheaf.lean), and give `IsSheafy` real mathematical content.

**Architecture:** The restriction map `σ: A⟨T/s⟩ → A⟨T'/s'⟩` for `R(T'/s') ⊆ R(T/s)` is constructed in three layers: (1) algebraic lift via `IsLocalization.Away.lift` from `Localization.Away s` to the completion `A⟨T'/s'⟩`, (2) continuity proof with respect to the localization topology, (3) extension to the completion via `UniformSpace.Completion.extensionHom`. The `IsSheafy` class is refined to require the Čech sheaf condition for rational coverings.

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3. Key Mathlib APIs: `IsLocalization.Away.lift`, `UniformSpace.Completion.extensionHom`, `UniformSpace.Completion.mapRingHom`, `RingSubgroupsBasis`.

---

## Dependency Graph

```
Task 1 (instances) ──→ Task 2 (canonical maps) ──→ Task 3 (s is unit) ──→ Task 4 (algebraic lift)
                                                                              │
                                                                              ▼
Task 7 (IsSheafy) ←── Task 6 (compose/id) ←── Task 5 (continuity + extension)
```

Tasks 1–2 are pure infrastructure. Task 3 is the key mathematical input. Tasks 4–5 are the construction. Task 6 is functoriality. Task 7 is the payoff.

---

## Phase 1: Infrastructure

### Task 1: Expose Instances on `presheafValue`

**Problem:** `presheafValue D` is defined via `by ... exact UniformSpace.Completion ...`, hiding the instances inside the tactic proof. We cannot access `CommRing (presheafValue D)`, `TopologicalSpace (presheafValue D)`, etc. from outside.

**Files:**
- Modify: `Adic spaces/Presheaf.lean` (lines 154–178, the `PresheafValue` section)

**Step 1: Add explicit instance defs on `RationalLocData`**

Add after `RationalLocData.topology` (line 161):

```lean
/-- The `IsTopologicalRing` instance on `Localization.Away D.s`
with the localization topology. -/
noncomputable def RationalLocData.isTopologicalRing (D : RationalLocData A) :
    @IsTopologicalRing (Localization.Away D.s) D.topology _ :=
  (locBasis D.P D.T D.s D.hopen).toRingFilterBasis.isTopologicalRing

/-- The `UniformSpace` on `Localization.Away D.s` from the localization topology. -/
noncomputable def RationalLocData.uniformSpace (D : RationalLocData A) :
    UniformSpace (Localization.Away D.s) :=
  @IsTopologicalAddGroup.rightUniformSpace _ D.topology
    (@IsTopologicalRing.toIsTopologicalAddGroup _ _ D.topology D.isTopologicalRing)
```

**Step 2: Redefine `presheafValue` in term mode**

Replace the tactic definition with:

```lean
noncomputable def presheafValue (D : RationalLocData A) : Type _ :=
  @UniformSpace.Completion (Localization.Away D.s) D.uniformSpace
```

**Step 3: Add instances on `presheafValue`**

```lean
noncomputable instance (D : RationalLocData A) :
    TopologicalSpace (presheafValue D) := inferInstance

noncomputable instance (D : RationalLocData A) :
    CommRing (presheafValue D) :=
  @UniformSpace.Completion.instCommRing _ _ D.uniformSpace
    D.isTopologicalRing (by infer_instance)

noncomputable instance (D : RationalLocData A) :
    UniformSpace (presheafValue D) := inferInstance

instance (D : RationalLocData A) : CompleteSpace (presheafValue D) :=
  inferInstance

instance (D : RationalLocData A) : T0Space (presheafValue D) :=
  inferInstance
```

**Step 4: Verify compilation**

Run: `lean_diagnostic_messages` on `Presheaf.lean`
Expected: No errors. Downstream `StructureSheaf.lean` still compiles.

**Risk:** The `@` explicit instance passing may fight with Lean's instance resolution. If `inferInstance` fails, provide the instances manually by chaining the `RationalLocData` instances. The `IsUniformAddGroup` instance is the trickiest — it comes from `IsTopologicalAddGroup.rightUniformSpace` which provides `IsUniformAddGroup` by construction.

**Step 5: Commit**

```
feat(Presheaf): expose CommRing/TopologicalSpace instances on presheafValue
```

---

### Task 2: Define Canonical Maps

**Files:**
- Modify: `Adic spaces/Presheaf.lean` (add after Task 1 instances)

**Step 1: The embedding `Localization.Away D.s → presheafValue D`**

```lean
/-- The dense embedding of `Localization.Away D.s` into its completion. -/
noncomputable def RationalLocData.coeRingHom (D : RationalLocData A) :
    Localization.Away D.s →+* presheafValue D :=
  @UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
    D.isTopologicalRing (by infer_instance)
```

**Step 2: The canonical map `A →+* presheafValue D`**

```lean
/-- The canonical ring homomorphism `ρ : A →+* A⟨T/s⟩` (the composition of
`algebraMap` with the completion embedding). -/
noncomputable def RationalLocData.canonicalMap (D : RationalLocData A) :
    A →+* presheafValue D :=
  D.coeRingHom.comp (algebraMap A (Localization.Away D.s))
```

**Step 3: Verify and commit**

```
feat(Presheaf): add canonical maps A →+* presheafValue D
```

---

## Phase 2: The Restriction Map Construction

### Task 3: Show `s` Maps to a Unit in `presheafValue D'`

This is the key mathematical input. For `R(T'/s') ⊆ R(T/s)`, the element `s` must be a unit in `A⟨T'/s'⟩ = presheafValue D'`.

**Mathematical argument (Lemma 8.1 proof):**
- `U' ⊆ U` means: for all `v ∈ Spa A A⁺`, if `v ∈ U'` then `v ∈ U`
- In `U`, we have `¬ v.vle s 0` (s is nonvanishing)
- Every `v ∈ Spa(A⟨T'/s'⟩)` arises from a `v ∈ U'` via `Spa(ρ')`
- So `v(s) ≠ 0` for all such `v`
- By Prop 7.52 (`isUnit_of_forall_not_vle_zero`), `s` is a unit in `A⟨T'/s'⟩`

**Difficulty:** This requires `Spa` on `presheafValue D'`, which requires `presheafValue D'` to be an affinoid ring (CommRing + TopologicalSpace + PlusSubring + open maximal ideals). This is deep infrastructure we don't have.

**Files:**
- Modify: `Adic spaces/Presheaf.lean`

**Step 1: State the theorem (initially with sorry)**

```lean
/-- The image of `s` under the canonical map `A → A⟨T'/s'⟩` is a unit
when `R(T'/s') ⊆ R(T/s)` (key ingredient of Lemma 8.1 / Prop 8.2). -/
theorem isUnit_canonicalMap_s (D D' : RationalLocData A) [PlusSubring A]
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  sorry
```

**Step 2: Attempt proof for cases where s ∈ Submonoid.powers D'.s**

In many practical cases (e.g., `s = s'`, or `s` is a power of `s'`), `s` is already a unit in `Localization.Away D'.s` (hence in its completion). Add a helper:

```lean
/-- If `s` is a power of `s'`, then `s` is already a unit in the localization. -/
theorem isUnit_canonicalMap_s_of_mem_powers (D D' : RationalLocData A)
    (hs : D.s ∈ Submonoid.powers D'.s) :
    IsUnit (D'.canonicalMap D.s) := by
  -- s is a unit in Localization.Away D'.s, hence in its completion
  sorry
```

**Step 3: Commit (with sorry)**

```
feat(Presheaf): state isUnit_canonicalMap_s (sorry — needs Prop 7.52 for completions)
```

**Note:** The full proof requires showing `presheafValue D'` is an affinoid ring and applying `isUnit_of_forall_not_vle_zero`. This is a major piece of future work (see Appendix A).

---

### Task 4: Algebraic Lift via `IsLocalization.Away.lift`

**Files:**
- Modify: `Adic spaces/Presheaf.lean`

**Step 1: Construct the ring hom from Localization.Away s to presheafValue D'**

```lean
/-- The algebraic part of the restriction map: a ring homomorphism
`Localization.Away D.s →+* presheafValue D'` extending the canonical map
`A → presheafValue D'`, using `IsLocalization.Away.lift`. -/
noncomputable def restrictionMapAlg (D D' : RationalLocData A) [PlusSubring A]
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  IsLocalization.Away.lift D.s (isUnit_canonicalMap_s D D' h)
```

**Step 2: Verify the compatibility property**

```lean
theorem restrictionMapAlg_comp (D D' : RationalLocData A) [PlusSubring A]
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    (restrictionMapAlg D D' h).comp (algebraMap A _) = D'.canonicalMap :=
  IsLocalization.Away.lift_comp D.s _
```

**Step 3: Commit**

```
feat(Presheaf): algebraic restriction map via IsLocalization.Away.lift
```

---

### Task 5: Continuity and Extension to Completion

**Files:**
- Modify: `Adic spaces/Presheaf.lean`

**Step 1: Prove the algebraic lift is continuous (hard — initially sorry)**

The ring hom `restrictionMapAlg D D' h : Localization.Away D.s →+* presheafValue D'` must be continuous with respect to the localization topology on the source and the completion topology on the target.

The proof strategy: show that the preimage of every neighborhood of 0 in `presheafValue D'` contains a neighborhood of 0 in `Localization.Away D.s`. Since both topologies are defined by `RingSubgroupsBasis`, it suffices to show that for each `n`, there exists `m` such that `restrictionMapAlg` maps `locNhd D.P D.T D.s m` into the `n`-th neighborhood of 0 in `presheafValue D'`.

```lean
theorem restrictionMapAlg_continuous (D D' : RationalLocData A) [PlusSubring A]
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology (by infer_instance) (restrictionMapAlg D D' h) := by
  sorry
```

**Step 2: Extend to the completion using `extensionHom`**

```lean
/-- The restriction map `σ : A⟨T/s⟩ →+* A⟨T'/s'⟩` for `R(T'/s') ⊆ R(T/s)`,
constructed as the completion-extension of the algebraic lift
(Proposition 8.2(1) of Wedhorn). -/
noncomputable def restrictionMapHom (D D' : RationalLocData A) [PlusSubring A]
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D →+* presheafValue D' :=
  @UniformSpace.Completion.extensionHom _ _ D.uniformSpace
    D.isTopologicalRing (by infer_instance) -- IsUniformAddGroup source
    _ _ _ _ _ -- instances on target
    (restrictionMapAlg D D' h)
    (restrictionMapAlg_continuous D D' h)
```

**Step 3: Redefine `restrictionMap` using `restrictionMapHom`**

Replace the sorry-based `restrictionMap` with:

```lean
noncomputable def restrictionMap (D D' : RationalLocData A)
    (_ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D → presheafValue D' :=
  restrictionMapHom D D' ‹_›
```

**Step 4: Verify and commit**

```
feat(Presheaf): restriction map via extensionHom (sorry: continuity + isUnit)
```

---

### Task 6: Composition and Identity Laws

**Files:**
- Modify: `Adic spaces/Presheaf.lean`

**Step 1: Prove identity law**

The restriction map for `D = D'` should be the identity. This follows from uniqueness of the lift: `IsLocalization.Away.lift` applied to the identity map gives the identity.

```lean
theorem restrictionMap_id (D : RationalLocData A) [PlusSubring A] :
    restrictionMap D D (le_refl _) = id := by
  -- By uniqueness of the lift: the only ring hom Completion(Loc.Away s) →+* Completion(Loc.Away s)
  -- that extends algebraMap is the identity.
  -- Use: extensionHom of coeRingHom = id (from Completion.extension_coe)
  sorry -- reducible to uniqueness of IsLocalization.lift
```

**Step 2: Prove composition law**

```lean
theorem restrictionMap_comp (D D' D'' : RationalLocData A) [PlusSubring A]
    (h₁ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (h₂ : rationalOpen D''.T D''.s ⊆ rationalOpen D'.T D'.s) :
    restrictionMap D' D'' h₂ ∘ restrictionMap D D' h₁ =
      restrictionMap D D'' (h₂.trans h₁) := by
  -- Both sides are ring homs Completion(Loc.Away s) →+* Completion(Loc.Away s'')
  -- agreeing on the dense image of A (both equal D''.canonicalMap).
  -- By density + T2, they agree everywhere.
  sorry -- reducible to uniqueness + density argument
```

**Step 3: Commit**

```
feat(Presheaf): restriction map identity and composition (sorry — density argument)
```

---

## Phase 3: Refine IsSheafy

### Task 7: Give `IsSheafy` Real Content

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean`

**Step 1: Define the Čech condition for rational coverings**

```lean
/-- The Čech sheaf condition for a rational covering: the canonical map from
the presheaf value on `U` to the equalizer of the maps to the double
intersections is an isomorphism of topological rings.

For a covering `R(T/s) = ⋃ R(Tᵢ/sᵢ)`, the sequence
  0 → A⟨T/s⟩ → ∏ A⟨Tᵢ/sᵢ⟩ ⇉ ∏ A⟨Tᵢ ∩ Tⱼ / sᵢsⱼ⟩
is exact, and the first map is a topological embedding. -/
def IsCechExact ... := sorry -- to be defined
```

**Step 2: Refine `IsSheafy` with a real field**

```lean
class IsSheafy [IsTopologicalRing A] : Prop where
  /-- Every finite rational covering of every rational subset satisfies the
  Čech exactness condition with topological embedding. -/
  cech_exact : ∀ (D : RationalLocData A) (Ds : Finset (RationalLocData A))
    (hcover : ∀ v ∈ rationalOpen D.T D.s,
      ∃ Di ∈ Ds, v ∈ rationalOpen Di.T Di.s),
    IsCechExact D Ds
```

**Step 3: Maintain `IsSheafy.discrete` instance**

For the discrete case, `IsCechExact` reduces to the algebraic Čech condition for `Spec A`, which holds by the acyclicity of the structure sheaf on affine schemes.

**Step 4: Commit**

```
feat(StructureSheaf): refine IsSheafy with Čech exactness condition
```

---

## Sorry Inventory & Proof Roadmap

After completing all tasks, the remaining sorries are:

| Sorry | Location | Difficulty | What's Needed |
|-------|----------|------------|---------------|
| `isUnit_canonicalMap_s` | Task 3 | **Hard** | Prop 7.52 for `presheafValue D'` as affinoid ring |
| `restrictionMapAlg_continuous` | Task 5 | **Medium** | Localization topology neighborhoods map correctly |
| `restrictionMap_id` | Task 6 | **Easy** | Uniqueness of `IsLocalization.lift` + density |
| `restrictionMap_comp` | Task 6 | **Easy** | Uniqueness + density |
| `IsCechExact` definition | Task 7 | **Medium** | Formalizing the Čech complex |
| `IsSheafy.discrete` proof | Task 7 | **Hard** | Acyclicity of affine scheme structure sheaf |

---

## Appendix A: Proof of `isUnit_canonicalMap_s` (Future Work)

The full proof of Lemma 8.1's key hypothesis requires:

1. **`presheafValue D'` is an affinoid ring.** This means showing:
   - It's an f-adic ring with pair of definition `(D', I·D')`
   - This is stated (without proof) by Wedhorn after the construction in §8.1

2. **The support map `Spa(presheafValue D') → Spa A` factors through U'.**
   - The canonical map `ρ': A → presheafValue D'` induces `Spa(ρ')` in the opposite direction
   - By construction, `Spa(ρ')` maps into `R(T'/s')` (Prop 8.2(2))

3. **Apply `isUnit_of_forall_not_vle_zero` to conclude `s` is a unit.**
   - For every `v ∈ Spa(presheafValue D')`, the pushforward `v ∘ ρ'` lies in `U' ⊆ U`
   - In `U`, `v(s) ≠ 0`
   - By Prop 7.52, `s` is a unit

**Prerequisites not yet formalized:**
- `presheafValue D'` has `PlusSubring` instance
- `presheafValue D'` has open maximal ideals (or `IsOpen {a | IsTopologicallyNilpotent a}`)
- `Spa(ρ')` factors through the rational subset
- Prop 7.52 applies to `presheafValue D'`

## Appendix B: Proof of `restrictionMapAlg_continuous` (Future Work)

The continuity proof requires showing that for each neighborhood `V` of 0 in `presheafValue D'`, the preimage under `restrictionMapAlg` contains a neighborhood of 0 in `Localization.Away D.s`.

**Strategy:** Both source and target have `RingSubgroupsBasis` neighborhoods:
- Source: `locNhd D.P D.T D.s n = image(J^n)` where `J = I·D`
- Target: `locNhd D'.P D'.T D'.s n = image(J'^n)` where `J' = I·D'` (embedded in completion)

We need: for each `n'`, find `n` such that `restrictionMapAlg` maps `locNhd D ... n` into the closure of `locNhd D' ... n'` in the completion.

The key ingredients:
1. `algebraMap A → presheafValue D'` is continuous (composition of continuous maps)
2. The localization topology neighborhoods are generated by images of `I^n` from `A₀`
3. The restriction map sends `algebraMap(a)` to `D'.canonicalMap(a)`, which is continuous

This reduces to showing that the map on generators (the `algebraMap` part) is continuous, plus handling the `1/s` factor using the `hopen` condition (similar to `locNhd_leftMul`).

## Appendix C: Alternative — Discrete Case First

If the general case proves too difficult, a valuable intermediate milestone is to prove everything for **discrete rings** (Theorem 8.28(c)):

1. When `A` has discrete topology, show `presheafValue D ≃+* Localization.Away D.s` (completion of discrete = identity, via `completeEquivSelf`)
2. The restriction map reduces to `IsLocalization.Away.lift` directly
3. Continuity is automatic (discrete topology)
4. The sheaf condition reduces to the algebraic structure sheaf on `Spec A`

This requires:
- Showing the localization topology on `Localization.Away s` is discrete when `A` is discrete
- Using `DiscreteUniformity.instCompleteSpace` and `completeEquivSelf`
