# AdicCompletion Bridge API — Design Spec

## Purpose

Build a standalone bridge identifying `UniformSpace.Completion R` with
`AdicCompletion I R` for rings whose topology arises from powers of an ideal
in a subring. This unlocks Mathlib's exactness, injectivity, and flatness
results for the project's `presheafValue` (which uses `UniformSpace.Completion`).

## Approach

**Approach B**: build the isomorphism as new infrastructure without touching
existing definitions (`presheafValue`, `locTopology`, etc.).

## File

`Adic spaces/AdicCompletionBridge.lean` (new file).

Imports: Mathlib's `AdicCompletion` suite + project's `LocalizationTopology.lean`.

## Core predicate

```
structure RingSubgroupsBasis.IsSubringAdic (B : ℕ → AddSubgroup R) where
  R₀ : Subring R
  I : Ideal R₀
  eq_image : ∀ n, B n = (I ^ n).map R₀.subtype.toAddMonoidHom
```

Says: the n-th neighborhood is exactly the image of `I^n` from `R₀` into `R`.

Key connecting lemma:

```
IsSubringAdic.smul_top_eq :
    (I ^ n • ⊤ : Submodule R₀ R) = (B n).toSubmodule
```

This bridges the topological world (`B n` neighborhoods) with the algebraic
world (`I^n • ⊤` filtration used by `AdicCompletion`).

## Layer 1: Quotient identification

For each `n`, identify the topological quotient with the algebraic quotient:

```
quotientEquiv (n : ℕ) :
    R ⧸ (B n).toSubmodule ≃ₗ[R₀] R ⧸ (I ^ n • ⊤)
```

Immediate from `smul_top_eq`.

**Naturality lemmas** (essential for Layer 2):

```
quotientEquiv_natural (h : m ≤ n) :
    transitionMap I R h ∘ₗ quotientEquiv n = quotientEquiv m ∘ₗ (B-transitionMap h)

quotientEquiv_commutes_coe (n : ℕ) (r : R) :
    quotientEquiv n (Submodule.Quotient.mk r) = AdicCompletion.eval n (AdicCompletion.of I R r)
```

The quotient spaces should be treated as discrete topological modules so that
extension from the completion is immediate.

## Layer 2: Completion identification

The key insight: show `AdicCompletion I R` is itself a completion of `R`
for the `B`-uniformity, then invoke uniqueness of completion.

**Step 1:** The canonical map `ι := AdicCompletion.of I R : R → AdicCompletion I R`
is uniformly continuous for the `B`-uniformity on `R` and the uniformity on
`AdicCompletion I R` induced by the projective limit topology.

**Step 2:** The pullback of the neighborhood basis at 0 along `ι` is exactly
`{B n}`. Equivalently, the induced topology on `R` via `ι` is the `B`-topology.
This makes `ι` a uniform inducing.

**Step 3:** `DenseRange ι`. Elements of `AdicCompletion I R` can be approximated
by `ι(r)` for `r ∈ R` at each finite level.

**Step 4:** `AdicCompletion I R` is complete and T₂ with the projective limit
topology/uniformity.

These four facts give:

```
denseUniformInducing_toAdicCompletion :
    IsDenseInducing ι ∧ IsUniformInducing ι ∧ CompleteSpace (AdicCompletion I R)
```

By uniqueness of completion (Mathlib: `IsUniformInducing.isDenseInducing_of_completeSpace`
or `AbstractCompletion` API):

```
adicCompletionEquiv :
    UniformSpace.Completion R ≃ₗ[R₀] AdicCompletion I R
```

satisfying `adicCompletionEquiv (coe r) = ι r` for all `r : R`.

**No Hausdorff hypothesis on R is needed.** Both sides automatically quotient
out `⋂ B(n) = ⋂ I^n • ⊤`, so we compare separated completions on both sides.

## Layer 3: Ring structure

The linear equivalence from Layer 2 is multiplicative:

```
adicCompletionRingEquiv :
    UniformSpace.Completion R ≃+* AdicCompletion I R
```

**Proof:** The two maps `(x, y) ↦ e(x * y)` and `(x, y) ↦ e(x) * e(y)` from
`Completion R × Completion R` to `AdicCompletion I R` are continuous and agree
on the dense subset `R × R` (since `e(coe r) = ι(r)` and both `ι` and `coe`
are ring homs). Since the target is T₂, they agree everywhere. Layer 3 is a
corollary of Layer 2 plus density.

## Transfer lemmas

Once the bridge is built, the following Mathlib results transfer to
`UniformSpace.Completion`:

### Transfer 1: Exactness preservation

```
completion_map_exact [IsNoetherianRing R₀] [Module.Finite R₀ M] :
    Function.Exact f g → Function.Exact (Completion.map f) (Completion.map g)
```

Via `AdicCompletion.map_exact`. Gives completed Laurent cover exactness.

### Transfer 2: Injectivity preservation

```
completion_map_injective [IsNoetherianRing R₀] [Module.Finite R₀ M] :
    Function.Injective f → Function.Injective (Completion.map f)
```

Via `AdicCompletion.map_injective`.

**Caveat:** Requires `Module.Finite R₀ M`. For `M = Localization.Away s` as
a `locSubring`-module, this is NOT finitely generated in general. The Laurent
exactness route (Transfer 1) is safer: exactness of the epsilon sequence can
be checked at the `R₀`-module level where the terms ARE finitely generated
quotients of `A⟨X⟩`.

### Transfer 3: Flatness

```
completion_flat [IsNoetherianRing R₀] :
    Module.Flat R₀ (UniformSpace.Completion R)
```

Via `AdicCompletion.flat_of_isNoetherian`.

## Application to IsSheafy

### Instantiation

For `presheafValue D`:
- `R = Localization.Away D.s`
- `R₀ = locSubring D.P D.T D.s`
- `I = locIdeal D.P D.T D.s`
- `B n = locNhd D.P D.T D.s n`
- The `IsSubringAdic` instance holds by definition of `locNhd`

### IsSheafy proof via Laurent exactness

1. The algebraic Laurent epsilon map `A →+* B₁ × B₂` is injective (sorry-free:
   `epsilonHom_gen_injective`).
2. The algebraic Laurent sequence is exact (sorry-free: `laurentCover_exact`).
3. The maps are between finitely generated `A₀`-modules (Tate algebra quotients).
4. **Transfer 1** gives completed exactness.
5. The TopologyComparison isomorphism identifies the completed terms with
   `presheafValue` values.
6. For general covers: Laurent-to-standard refinement (Lemma 8.34) +
   `Refinement.separation_of_finer` (sorry-free).
7. Assembly: `IsSheafy`.

### Alternative: IsSheafy via faithful flatness

1. **Transfer 3** gives `presheafValue D` flat over `locSubring`.
2. Flat over `locSubring` + localization flat over `A` → flat over `A`.
3. Product of flat modules is flat (`Module.Flat.pi`, sorry-free).
4. Covering condition → faithfully flat.
5. Faithfully flat → `productRestriction` injective → `IsSheafy`.

## Theorem stack summary

```
1. smul_top_eq                              -- I^n • ⊤ = B(n) as submodules
2. quotientEquiv                            -- pointwise quotient identification
3. quotientEquiv_natural                    -- commutes with transition maps
4. quotientEquiv_commutes_coe              -- commutes with canonical maps
5. uniformContinuous_toAdicCompletion      -- ι is uniformly continuous
6. isUniformInducing_toAdicCompletion      -- ι induces the B-uniformity
7. denseRange_toAdicCompletion             -- ι has dense range
8. completeSpace_adicCompletion            -- AdicCompletion is complete
9. adicCompletionEquiv                      -- linear equivalence (uniqueness of completion)
10. adicCompletionRingEquiv                 -- ring equivalence (density + T₂)
11. completion_map_exact                    -- transfer: exactness
12. completion_map_injective               -- transfer: injectivity (Module.Finite)
13. completion_flat                         -- transfer: flatness
```

## Estimated size

~300-400 lines for the bridge (Layers 1-3).
~100-150 lines for the transfers + instantiation for localization.
~100-150 lines for the IsSheafy assembly.

Total: ~500-700 lines of new code.
