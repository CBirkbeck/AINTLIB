# Laurent Refinement API — Design Spec

## Goal

Fill the single remaining sorry in `isSheafy_ofStronglyNoetherianTate_flat`:
`productRestriction_injective_of_laurentRefinement` (Lemma 8.34 of Wedhorn).

Prove that for strongly noetherian Tate rings, every rational covering has
injective product restriction, using Laurent covers + concrete refinement.

## Architecture

Three-layer stack, each in its own file:

```
Layer 3: LaurentRefinement.lean
  Laurent covers, products, Lemma 7.54, Lemma 8.34, assembly
         │ uses
Layer 2: RationalRefinement.lean
  RationalRefinement structure, separation_of_finer_rational
         │ uses
Layer 1: RestrictionComposition.lean
  restrictionMap_comp (restriction maps compose)
```

All three files import `Presheaf.lean`. Layer 3 also imports
`LaurentCoverExact.lean` and `TopologyComparison.lean`.

## Approach

**Direct concrete refinement (Approach B):** No `AbPresheaf` wrapping.
We define a concrete `RationalRefinement` between `RationalCovering`s and
prove that refinement preserves injectivity of `productRestriction` directly.

## Layer 1 — RestrictionComposition.lean (~80 lines)

### Core theorem

```lean
theorem restrictionMap_comp (D₁ D₂ D₃ : RationalLocData A)
    (h₁₂ : rationalOpen D₂.T D₂.s ⊆ rationalOpen D₁.T D₁.s)
    (h₂₃ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.T D₂.s) (x) :
    restrictionMap D₁ D₃ (h₂₃.trans h₁₂) x =
      restrictionMap D₂ D₃ h₂₃ (restrictionMap D₁ D₂ h₁₂ x)
```

### Proof strategy

Both sides are continuous maps `presheafValue D₁ → presheafValue D₃` that
agree on the dense image of `D₁.coeRingHom : Localization.Away D₁.s →
presheafValue D₁`. Agreement on the dense subalgebra follows from the
algebraic universal property of localization (`IsLocalization.Away.lift`
uniqueness). Extension to the full completion uses `T₂` + density
(`DenseRange.equalizer`).

### Algebraic helper

```lean
theorem restrictionMapAlg_comp (D₁ D₂ D₃ : RationalLocData A) ... :
    restrictionMapAlg D₁ D₃ (h₂₃.trans h₁₂) =
      (restrictionMapHom D₂ D₃ h₂₃).comp (restrictionMapAlg D₁ D₂ h₁₂)
```

This is the algebraic composition: the lift of `A[1/s₁] → presheafValue D₃`
equals the composition of `A[1/s₁] → presheafValue D₂ → presheafValue D₃`.
Proved by `IsLocalization.ringHom_ext` (both agree on `algebraMap A`).

## Layer 2 — RationalRefinement.lean (~60 lines)

### Definition

```lean
structure RationalRefinement (V U : RationalCovering A) where
  base_eq : V.base = U.base
  τ : { D // D ∈ V.covers } → { E // E ∈ U.covers }
  hτ : ∀ d, rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s
```

`V` refines `U`: same base, each V-piece inside some U-piece via map `τ`.

### Core theorem

```lean
theorem separation_of_finer_rational (V U : RationalCovering A)
    (r : RationalRefinement V U)
    (hV : Function.Injective (productRestriction A V)) :
    Function.Injective (productRestriction A U)
```

### Proof

Given `productRestriction A U x = productRestriction A U y`:
1. For each `E ∈ U.covers`: `restrictionMap base E x = restrictionMap base E y`
2. For each `D ∈ V.covers` with `τ(D) = E`:
   `restrictionMap base D = restrictionMap E D ∘ restrictionMap base E`
   (by `restrictionMap_comp`, using `base_eq` to rewrite base)
3. So `restrictionMap base D x = restrictionMap base D y` for all V-pieces
4. By V-separation: `x = y`

## Layer 3 — LaurentRefinement.lean (~300 lines)

### Part A: Laurent cover construction

```lean
noncomputable def laurentPlusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A
```

The "plus half" rational datum: `R(T₀ ∪ {f} / s₀)` — adds `f` to the
numerator generators of `D₀`. Represents `{v ∈ R(D₀) : v(f) ≤ v(s₀)}`.

```lean
noncomputable def laurentMinusDatum (D₀ : RationalLocData A) (f : A) :
    RationalLocData A
```

The "minus half": `R(T₀ · s₀ / s₀ · f)` using `rationalOpen_inter` to
express `R(D₀) ∩ R({s₀}/f)`. Represents `{v ∈ R(D₀) : v(s₀) ≤ v(f)}`.

**Note:** May require `s₀ ∈ T₀` or `f ∈ T₀ ∪ {s₀}` conditions for
well-formedness. Handle by adjoining `s₀` to `T₀` if needed (this does
not change `rationalOpen T₀ s₀`).

```lean
noncomputable def laurentCovering (D₀ : RationalLocData A) (f : A) :
    RationalCovering A where
  base := D₀
  covers := {laurentPlusDatum D₀ f, laurentMinusDatum D₀ f}
  hsubset := ...  -- both halves ⊆ base
  hcover := ...   -- trichotomy: v(f) ≤ v(s) ∨ v(s) ≤ v(f)
```

### Part B: Laurent separation

```lean
theorem laurentCovering_injective
    [IsTateRing A] [IsNoetherianRing A] [IsDomain A]
    [T2Space A] [NonarchimedeanRing A] [FirstCountableTopology A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) (f : A) (hf : ¬IsUnit f)
    -- TopologyComparison hypotheses for D₀ and both halves:
    ... :
    Function.Injective (productRestriction A (laurentCovering D₀ f))
```

Connects `epsilonHom_gen_injective` to `productRestriction`. The proof
transfers through the TopologyComparison isomorphisms:
1. `presheafValue D₀ ≃+* A⟨X⟩/(1-s₀X)` via `presheafValueTateQuotientEquiv`
2. Similarly for both Laurent halves
3. The transferred map is essentially `epsilonHom_gen`
4. Apply `epsilonHom_gen_injective`

### Part C: Product of Laurent covers

```lean
noncomputable def laurentProduct (D₀ : RationalLocData A) :
    List A → RationalCovering A
  | [] => trivialCovering D₀   -- single-piece covering = {D₀}
  | f :: fs => crossCovering (laurentCovering D₀ f) (laurentProduct D₀ fs)
```

where `crossCovering` takes two coverings of the same base and forms the
covering by pairwise intersections. The result has `2^n` pieces.

```lean
theorem laurentProduct_injective
    [IsTateRing A] [IsNoetherianRing A] [IsDomain A] ...
    (D₀ : RationalLocData A) (fs : List A)
    (hfs : ∀ f ∈ fs, ¬IsUnit f) :
    Function.Injective (productRestriction A (laurentProduct D₀ fs))
```

By induction on `fs`:
- Base: trivial covering, identity map, injective
- Step: cross = Laurent × product, use Laurent separation for the
  first factor + inductive hypothesis for the remaining + refinement

### Part D: Lemma 7.54 — Rational decomposition

```lean
theorem rationalOpen_eq_iInter (T : Finset A) (s : A) :
    rationalOpen T s = ⋂ t ∈ T, rationalOpen {t} s
```

Each `R({t}/s)` participates in the Laurent cover at `f = t`:
`R({t}/s) ⊆ R(T₀ ∪ {t} / s₀)` = the plus half.

### Part E: Lemma 8.34 — Every covering has a Laurent refinement

```lean
theorem exists_laurentProduct_refinement (C : RationalCovering A) :
    ∃ fs : List A,
      RationalRefinement (laurentProduct C.base fs) C
```

Construction: take `fs` to be the list of all `D.s` for `D ∈ C.covers`.
Each piece of the Laurent product is an intersection of halves, and by
the covering condition + Lemma 7.54, it sits inside some cover piece of C.

### Part F: Assembly

```lean
theorem productRestriction_injective
    [IsTateRing A] [IsNoetherianRing A] [IsDomain A] ...
    (C : RationalCovering A) :
    Function.Injective (productRestriction A C) :=
  let ⟨fs, r⟩ := exists_laurentProduct_refinement C
  separation_of_finer_rational _ _ r (laurentProduct_injective C.base fs ...)
```

## Dependencies

```
StructureSheaf.lean
  └─ LaurentRefinement.lean
       ├─ RationalRefinement.lean
       │    └─ RestrictionComposition.lean
       │         └─ Presheaf.lean
       ├─ LaurentCoverExact.lean
       ├─ TopologyComparison.lean
       └─ RationalSubsets.lean
```

New files must be added to `Adic spaces.lean` (root import file).

## Tricky Points

1. **Laurent minus datum well-formedness:** The `RationalLocData` for the
   minus half needs a valid `hopen` witness. May need to adjoin `s₀` to `T₀`.

2. **Connecting ε to productRestriction:** The algebraic `epsilonHom_gen`
   maps A, while `productRestriction` maps from a completion. The bridge
   goes through TopologyComparison isomorphisms. For the base = whole ring
   case, presheafValue ≅ A (trivially complete). For general base, uses the
   full isomorphism.

3. **Cross covering construction:** Taking pairwise intersections of two
   coverings requires `rationalOpen_inter` and constructing the new
   `RationalLocData` for each intersection piece.

4. **Product induction:** The inductive step requires showing the cross
   covering of (Laurent × product) refines the (n+1)-element Laurent product.

## Testing / Verification

Each file should compile independently with `lake env lean "Adic spaces/File.lean"`.
The final check: `lean_verify` on `isSheafy_ofStronglyNoetherianTate_flat` shows
only standard axioms (no `sorryAx`).

## References

- Wedhorn, *Adic Spaces*, Lemma 7.54, Lemma 8.33, Lemma 8.34, Theorem 8.28
