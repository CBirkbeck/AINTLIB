# AdicCompletion Bridge Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a ring isomorphism `UniformSpace.Completion R ≃+* AdicCompletion I R` for rings with subring-adic topology, unlocking Mathlib's exactness/flatness for `presheafValue`.

**Architecture:** Equip `AdicCompletion I R` with a uniform structure from the projective limit, show it satisfies `AbstractCompletion` (complete, T₀, uniform inducing, dense range), then use `AbstractCompletion.compareEquiv` to get the equivalence with `UniformSpace.Completion`. Ring structure follows by density + T₂.

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3 (`AdicCompletion`, `AbstractCompletion`, `UniformSpace.Completion`).

**Spec:** `docs/superpowers/specs/2026-03-26-adic-completion-bridge-design.md`

---

## File Structure

| File | Responsibility |
|------|---------------|
| `Adic spaces/AdicCompletionBridge.lean` (CREATE) | Core bridge: `IsSubringAdic`, quotient equiv, uniform structure on AdicCompletion, `AbstractCompletion` instance, `adicCompletionRingEquiv` |
| `Adic spaces/AdicCompletionTransfer.lean` (CREATE) | Transfer lemmas: `completion_map_injective`, `completion_map_exact`, `completion_flat` |
| `Adic spaces/PresheafAdicCompletion.lean` (CREATE) | Instantiation: `locNhd` is subring-adic, `presheafValue D ≃+* AdicCompletion locIdeal (Localization.Away D.s)` |
| `Adic spaces/StructureSheaf.lean` (MODIFY) | Replace quarantined IsSheafy proof with new route through bridge |
| `Adic spaces.lean` (MODIFY) | Add imports for new files |

---

## Chunk 1: Core Bridge

### Task 1: Predicate and submodule identification

**Files:**
- Create: `Adic spaces/AdicCompletionBridge.lean`

- [ ] **Step 1: File header and imports**

Create `Adic spaces/AdicCompletionBridge.lean` with:

```lean
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a ring `R` whose topology arises from powers of an ideal `I` in a
subring `R₀ ⊆ R` (i.e., neighborhoods of 0 are images of `I^n`), we
construct a ring isomorphism:

  `UniformSpace.Completion R ≃+* AdicCompletion I R`

where `R` is viewed as an `R₀`-module.

## Strategy

1. Show `I^n • ⊤ = B(n)` as submodules of `R` over `R₀` (Layer 1).
2. Equip `AdicCompletion I R` with a uniform structure from the
   projective limit topology.
3. Show `AdicCompletion.of I R : R → AdicCompletion I R` satisfies the
   `AbstractCompletion` axioms (uniform inducing, dense range, complete, T₀).
4. Use `AbstractCompletion.compareEquiv` for the equivalence.
5. Prove multiplicativity by density + T₂.
-/
```

Verify: `lean_diagnostic_messages` — 0 errors.

- [ ] **Step 2: IsSubringAdic predicate**

```lean
variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- A `RingSubgroupsBasis` is *subring-adic* if the neighborhoods are images of
powers of an ideal `I` in a subring `R₀` under the subring inclusion. -/
structure RingSubgroupsBasis.IsSubringAdic {B : ℕ → AddSubgroup R}
    (_ : RingSubgroupsBasis B) where
  /-- The subring of definition. -/
  R₀ : Subring R
  /-- The ideal of definition inside `R₀`. -/
  I : Ideal R₀
  /-- The `n`-th neighborhood equals the image of `I^n`. -/
  eq_image : ∀ n, B n = (I ^ n).toAddSubgroup.map R₀.subtype.toAddMonoidHom
```

Verify: compiles.

- [ ] **Step 3: smul_top_eq — the key submodule identification**

```lean
/-- `I^n • ⊤` as a submodule of `R` over `R₀` equals the `n`-th neighborhood.
This bridges the topological filtration with the algebraic filtration used
by `AdicCompletion`. -/
theorem RingSubgroupsBasis.IsSubringAdic.smul_top_eq
    {B : ℕ → AddSubgroup R} {hB : RingSubgroupsBasis B}
    (h : hB.IsSubringAdic) (n : ℕ) :
    (h.I ^ n • ⊤ : Submodule h.R₀ R) = (B n).toSubmodule (R := R) := by
  ...
```

The proof: `I^n • ⊤ = I^n.map(subtype)` as submodules (since smul by ideal on ⊤ = image under inclusion). Match with `eq_image`.

Verify with `lean_goal` and `lean_diagnostic_messages`.

- [ ] **Step 4: Commit**

```
AdicCompletionBridge: IsSubringAdic predicate + smul_top_eq
```

### Task 2: Layer 1 — Quotient identification with naturality

**Files:**
- Modify: `Adic spaces/AdicCompletionBridge.lean`

- [ ] **Step 1: quotientEquiv**

```lean
/-- Pointwise quotient identification: `R / B(n) ≃ R / (I^n • ⊤)`. -/
noncomputable def IsSubringAdic.quotientEquiv (n : ℕ) :
    R ⧸ (B n).toSubmodule ≃ₗ[h.R₀] R ⧸ (h.I ^ n • ⊤) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (h.smul_top_eq n)
```

Verify: compiles.

- [ ] **Step 2: quotientEquiv_natural — commutes with transition maps**

Prove that the quotient equivalences commute with the transition maps
`R/(I^n•⊤) → R/(I^m•⊤)` (for m ≤ n) used in the projective limit
definition of `AdicCompletion`.

```lean
theorem IsSubringAdic.quotientEquiv_natural (hmn : m ≤ n) :
    AdicCompletion.transitionMap h.I R hmn ∘ₗ
      (h.quotientEquiv n).toLinearMap =
    (h.quotientEquiv m).toLinearMap ∘ₗ
      (Submodule.mapQ _ _ (Submodule.inclusion (B_antitone hmn))) := by
  ...
```

- [ ] **Step 3: quotientEquiv_commutes_coe — commutes with canonical maps**

```lean
theorem IsSubringAdic.quotientEquiv_commutes_coe (n : ℕ) (r : R) :
    h.quotientEquiv n (Submodule.Quotient.mk r) =
      AdicCompletion.eval n (AdicCompletion.of h.I R r) := by
  ...
```

- [ ] **Step 4: Commit**

```
AdicCompletionBridge: Layer 1 quotient identification + naturality
```

### Task 3: Layer 2 — Uniform structure on AdicCompletion

**Files:**
- Modify: `Adic spaces/AdicCompletionBridge.lean`

- [ ] **Step 1: Define uniform structure on AdicCompletion**

The projective limit topology on `AdicCompletion I R` is induced by the
evaluation maps `eval n : AdicCompletion I R → R/(I^n•⊤)`, where each
quotient has the discrete topology.

```lean
/-- Uniform structure on `AdicCompletion I R` induced by the projective
limit: the coarsest uniformity making each `eval n` uniformly continuous
(with discrete uniformity on quotients). -/
noncomputable instance IsSubringAdic.adicCompletionUniformSpace :
    UniformSpace (AdicCompletion h.I R) :=
  ⨅ n, UniformSpace.comap (AdicCompletion.eval n) ⊥
```

(Here `⊥` is the discrete uniformity on the quotient.)

- [ ] **Step 2: TopologicalSpace, IsTopologicalAddGroup, T0Space, CompleteSpace instances**

Derive the necessary instances from the projective limit uniformity:
- `TopologicalSpace` from `UniformSpace`
- `IsTopologicalAddGroup` (projective limit of add groups)
- `T0Space` (separated: elements equal iff equal at all levels)
- `CompleteSpace` (projective limit of complete discrete spaces)

- [ ] **Step 3: Commit**

```
AdicCompletionBridge: uniform structure on AdicCompletion
```

### Task 4: Layer 2 — AbstractCompletion instance

**Files:**
- Modify: `Adic spaces/AdicCompletionBridge.lean`

- [ ] **Step 1: IsUniformInducing for AdicCompletion.of**

Show `AdicCompletion.of h.I R : R → AdicCompletion h.I R` is uniform
inducing for the B-uniformity on R and the projective limit uniformity
on AdicCompletion.

```lean
theorem IsSubringAdic.isUniformInducing_of :
    @IsUniformInducing R (AdicCompletion h.I R)
      hB.topology.toUniformSpace h.adicCompletionUniformSpace
      (AdicCompletion.of h.I R) := by
  ...
```

Proof: the pullback of the projective limit uniformity along `of` has
basic entourages `{(x,y) : eval n (of x) = eval n (of y)}` = `{(x,y) : x - y ∈ I^n•⊤}` = `{(x,y) : x - y ∈ B(n)}`, which is exactly the B-uniformity.

- [ ] **Step 2: DenseRange for AdicCompletion.of**

```lean
theorem IsSubringAdic.denseRange_of :
    @DenseRange (AdicCompletion h.I R) h.adicCompletionTopology R
      (AdicCompletion.of h.I R) := by
  ...
```

Proof: for any element `x` of AdicCompletion and any basic open `eval n⁻¹({eval n x})`, the representative at level n lifts to an element of R mapping into this set.

- [ ] **Step 3: Build the AbstractCompletion instance**

```lean
/-- `AdicCompletion I R` with the projective limit uniformity is an
abstract completion of `R` with the B-uniformity. -/
noncomputable def IsSubringAdic.adicAbstractCompletion :
    @AbstractCompletion R hB.topology.toUniformSpace where
  space := AdicCompletion h.I R
  coe := AdicCompletion.of h.I R
  uniformStruct := h.adicCompletionUniformSpace
  complete := h.adicCompletionCompleteSpace
  separation := h.adicCompletionT0Space
  isUniformInducing := h.isUniformInducing_of
  dense := h.denseRange_of
```

- [ ] **Step 4: The equivalence via AbstractCompletion.compareEquiv**

```lean
/-- The bridge: `UniformSpace.Completion R ≃ᵤ AdicCompletion I R`. -/
noncomputable def IsSubringAdic.adicCompletionEquiv :
    @UniformSpace.Completion R hB.topology.toUniformSpace ≃ᵤ
      AdicCompletion h.I R :=
  UniformSpace.Completion.cPkg.compareEquiv h.adicAbstractCompletion
```

And the linear map version (using the R₀-module structure):

```lean
noncomputable def IsSubringAdic.adicCompletionLinearEquiv :
    @UniformSpace.Completion R hB.topology.toUniformSpace ≃ₗ[h.R₀]
      AdicCompletion h.I R := by
  ...
```

- [ ] **Step 5: Verify `adicCompletionEquiv_coe`**

```lean
theorem IsSubringAdic.adicCompletionEquiv_coe (r : R) :
    h.adicCompletionEquiv (coe r) = AdicCompletion.of h.I R r := by
  exact AbstractCompletion.compare_coe _ _ r
```

- [ ] **Step 6: Commit**

```
AdicCompletionBridge: Layer 2 AbstractCompletion + equivalence
```

### Task 5: Layer 3 — Ring structure

**Files:**
- Modify: `Adic spaces/AdicCompletionBridge.lean`

- [ ] **Step 1: adicCompletionRingEquiv**

```lean
/-- The bridge as a ring isomorphism. Multiplicativity follows from
density + T₂: the two maps `(x,y) ↦ e(xy)` and `(x,y) ↦ e(x)e(y)`
are continuous and agree on the dense `R × R`, so they agree everywhere. -/
noncomputable def IsSubringAdic.adicCompletionRingEquiv :
    @UniformSpace.Completion R hB.topology.toUniformSpace ≃+*
      AdicCompletion h.I R where
  toFun := h.adicCompletionEquiv
  invFun := h.adicCompletionEquiv.symm
  left_inv := h.adicCompletionEquiv.symm_apply_apply
  right_inv := h.adicCompletionEquiv.apply_symm_apply
  map_mul' x y := by
    -- Both sides are continuous and agree on the dense image of R.
    ...
  map_add' x y := by
    -- From the linear equivalence.
    ...
```

- [ ] **Step 2: Compatibility lemma**

```lean
theorem IsSubringAdic.adicCompletionRingEquiv_coe (r : R) :
    h.adicCompletionRingEquiv (coe r) = AdicCompletion.of h.I R r :=
  h.adicCompletionEquiv_coe r
```

- [ ] **Step 3: Commit**

```
AdicCompletionBridge: Layer 3 ring isomorphism (0 sorry)
```

- [ ] **Step 4: Verify file**

Run `lean_diagnostic_messages` on `Adic spaces/AdicCompletionBridge.lean`.
Expected: 0 errors, 0 sorry.

---

## Chunk 2: Transfer Lemmas

### Task 6: Transfer file

**Files:**
- Create: `Adic spaces/AdicCompletionTransfer.lean`

- [ ] **Step 1: File header**

```lean
import «Adic spaces».AdicCompletionBridge
import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Transfer of AdicCompletion results to UniformSpace.Completion

Using the bridge `adicCompletionRingEquiv`, transfer Mathlib's
exactness, injectivity, and flatness results from `AdicCompletion`
to `UniformSpace.Completion` for rings with subring-adic topology.
-/
```

- [ ] **Step 2: Transfer injectivity**

```lean
/-- Completion preserves injectivity of linear maps between finitely
generated modules over noetherian rings with subring-adic topology. -/
theorem IsSubringAdic.completion_map_injective
    [IsNoetherianRing h.R₀] [Module.Finite h.R₀ M] [Module.Finite h.R₀ N]
    {f : M →ₗ[h.R₀] N} (hf : Function.Injective f) :
    Function.Injective (UniformSpace.Completion.map f) := by
  -- Transfer via the bridge: Completion.map f ↔ AdicCompletion.map I f
  ...
```

- [ ] **Step 3: Transfer exactness**

```lean
theorem IsSubringAdic.completion_map_exact
    [IsNoetherianRing h.R₀] [Module.Finite h.R₀ K]
    [Module.Finite h.R₀ M] [Module.Finite h.R₀ N]
    {f : K →ₗ[h.R₀] M} {g : M →ₗ[h.R₀] N}
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Function.Exact (Completion.map f) (Completion.map g) := by
  ...
```

- [ ] **Step 4: Transfer flatness**

```lean
theorem IsSubringAdic.completion_flat [IsNoetherianRing h.R₀] :
    Module.Flat h.R₀ (UniformSpace.Completion R) := by
  -- AdicCompletion.flat_of_isNoetherian + transport via bridge
  ...
```

- [ ] **Step 5: Commit**

```
AdicCompletionTransfer: exactness + injectivity + flatness transfers
```

---

## Chunk 3: Localization Instantiation and IsSheafy

### Task 7: Instantiation for presheafValue

**Files:**
- Create: `Adic spaces/PresheafAdicCompletion.lean`

- [ ] **Step 1: locNhd is subring-adic**

```lean
import «Adic spaces».AdicCompletionTransfer
import «Adic spaces».Presheaf

/-- The localization topology neighborhoods form a subring-adic basis:
`locNhd n = image((locIdeal)^n)` by definition. -/
theorem locBasis_isSubringAdic (D : RationalLocData A) :
    (locBasis D.P D.T D.s D.hopen).IsSubringAdic where
  R₀ := locSubring D.P D.T D.s
  I := locIdeal D.P D.T D.s
  eq_image n := rfl  -- by definition of locNhd
```

- [ ] **Step 2: presheafValue as AdicCompletion**

```lean
/-- `presheafValue D ≃+* AdicCompletion locIdeal (Localization.Away D.s)`. -/
noncomputable def presheafValueAdicCompletionEquiv (D : RationalLocData A) :
    presheafValue D ≃+*
      AdicCompletion (locIdeal D.P D.T D.s) (Localization.Away D.s) :=
  (locBasis_isSubringAdic D).adicCompletionRingEquiv
```

- [ ] **Step 3: Commit**

```
PresheafAdicCompletion: locNhd is subring-adic + presheafValue bridge
```

### Task 8: IsSheafy via completed Laurent exactness

**Files:**
- Modify: `Adic spaces/StructureSheaf.lean`

- [ ] **Step 1: Replace quarantined IsSheafy proof**

Using the bridge + Laurent exactness + refinement, replace
`separation_ofStronglyNoetherianTate` with a sorry-free proof:

1. The algebraic epsilon map is injective (`epsilonHom_gen_injective`)
2. Transfer via `completion_map_injective` (for the finitely generated
   Tate quotient modules) gives completed injectivity
3. TopologyComparison isomorphism identifies completed terms with `presheafValue`
4. For general covers: Laurent-to-standard refinement + `Refinement.separation_of_finer`

Note: Step 4 (refinement) may still need a sorry for Lemma 8.34
(the combinatorial Laurent-to-standard step). If so, leave it as a
clean standalone sorry.

- [ ] **Step 2: Update imports in `Adic spaces.lean`**

Add imports for the three new files.

- [ ] **Step 3: Full build**

```bash
lake build
```

Expected: builds successfully.

- [ ] **Step 4: Commit**

```
IsSheafy: route through AdicCompletion bridge + Laurent exactness
```

---

## Verification checkpoints

After each chunk:

1. `lake env lean "Adic spaces/AdicCompletionBridge.lean"` — 0 error, 0 sorry
2. `lake env lean "Adic spaces/AdicCompletionTransfer.lean"` — 0 error, 0 sorry
3. `lake env lean "Adic spaces/PresheafAdicCompletion.lean"` — 0 error, 0 sorry
4. `lake env lean "Adic spaces/StructureSheaf.lean"` — 0 error, minimal sorry
5. `lake build` — success

## Dependencies

```
AdicCompletionBridge.lean (Chunk 1)
    ↓
AdicCompletionTransfer.lean (Chunk 2)
    ↓
PresheafAdicCompletion.lean (Chunk 3, Task 7)
    ↓
StructureSheaf.lean (Chunk 3, Task 8)
```

Chunks must be executed in order.
