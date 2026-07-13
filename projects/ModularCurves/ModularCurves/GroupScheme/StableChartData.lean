import ModularCurves.GroupScheme.ChartCoaction
import ModularCurves.GroupScheme.HopfGaloisCharts
import ModularCurves.GroupScheme.ActPairImmersion

/-!
# The per-chart Hopf–Galois datum (`[HG-C1d]` assembly + `[HG-C2]` last mile)

Construction support for `[CHARTER-HOPF]` Wave C (`.mathlib-quality/decomposition-hopf-crux.md`,
appendix "Wave C — pin-map + C3 cover strategy"). On a `G`-stable affine chart patch `P`
(an `AffineChartPatch`), the abstract Hopf–Galois theorem M5 consumes a
`StableAffineChartData P.baseRing P.groupRing P.chartRing`, whose three fields are:
* `coaction := P.chartCoaction` (`StableCharts`) — DONE upstream,
* `isCoaction := P.chartCoaction_isCoaction` (`ChartCoaction`) — DONE upstream,
* `precursorSurjective` — the `Γ`-dual of C2's `isClosedImmersion_actPair_left`.

The chart group ring's **Hopf-algebra structure is already available**:
`PatchHopf.instHopfAlgebraOpens : HopfAlgebra P.baseRing P.groupRing`, built via
`Bialgebra.ofAlgHom`/`HopfAlgebra.ofAlgHom` from the opens-level `comulAlg`/`counitAlg`/`antipodeAlg`
— i.e. **over the geometric `AffineChartPatch` algebra instance**, so there is no instance diamond
(one only appears if a *free* `[HopfAlgebra …]` variable is introduced, which shadows the ambient
instance with a fresh `Bialgebra`-derived algebra — this file never does that).

This file supplies:
* `instModuleFiniteGroupRing : Module.Finite P.baseRing P.groupRing` — from `G.π` finite.
* `chartCoaction_productMap_surjective` — surjectivity of the Galois precursor (the `Γ`-dual of
  `isClosedImmersion_actPair_left`); reduced to the one geometric sorry
  `chartPrecursorSpec_isClosedImmersion`.
* `chartData` / `isHopfGalois_chartCoaction` — the **C1d assembly**: `IsHopfGalois P.chartCoaction`
  (the M6 milestone), consumed by `isColimit_of_isHopfGalois` in the `[HG-C4]` glue. The sole
  hypothesis is `Module.Free P.baseRing P.groupRing` (freeness of `G` per chart, from `[HG-C3]`
  base-shrinking; diamond-free to hypothesis-wire).
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

namespace ModularCurves

/-- **A ring hom is surjective if its `Spec` is a closed immersion.** For `φ : R ⟶ S` in
`CommRingCat`, if `Spec.map φ` is a closed immersion then `φ` is surjective: the target
`Spec R` is affine, so a closed immersion has surjective sections over `⊤`, and that map is
`φ` conjugated by the `Γ`–`Spec` isomorphisms. The converse is
`IsClosedImmersion.spec_of_surjective`. -/
theorem surjective_hom_of_isClosedImmersion_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsClosedImmersion (AlgebraicGeometry.Spec.map φ)] : Function.Surjective φ.hom := by
  have hsurj := (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    (AlgebraicGeometry.Spec.map φ)).2
  have hnat : (AlgebraicGeometry.Spec.map φ).appTop
      = (AlgebraicGeometry.Scheme.ΓSpecIso R).hom ≫ φ ≫ (AlgebraicGeometry.Scheme.ΓSpecIso S).inv := by
    rw [← Category.assoc, ← AlgebraicGeometry.Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hnat] at hsurj
  have hbijR : Function.Bijective (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hbijS : Function.Bijective (AlgebraicGeometry.Scheme.ΓSpecIso S).inv.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hsurj
  have h1 := (Function.Surjective.of_comp_iff
    (⇑(AlgebraicGeometry.Scheme.ΓSpecIso S).inv.hom ∘ ⇑φ.hom) hbijR.surjective).mp hsurj
  intro y
  obtain ⟨x, hx⟩ := h1 ((AlgebraicGeometry.Scheme.ΓSpecIso S).inv.hom y)
  exact ⟨x, hbijS.injective hx⟩

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

namespace AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : FiniteLocallyFreeSubgroup E}
  (P : G.AffineChartPatch)

/-- **The group ring is module-finite over the base ring.** The structure morphism
`G.π = G.ι ≫ E.π` is finite (`G.finite`), so its sections over the affine base patch `V`
are a finite module over `Γ(S, V)`. This is the `Module.Finite R A` input to the M5
Hopf–Galois theorem. -/
instance instModuleFiniteGroupRing : Module.Finite P.baseRing P.groupRing := by
  haveI : IsFinite G.π := G.finite
  show (G.π.appLE P.V P.groupOpen le_rfl).hom.Finite
  rw [Scheme.Hom.appLE_eq_app]
  exact G.π.finite_app P.V P.hV

/-- **`[HG-C2]` geometric heart — the `Spec` of the Galois precursor is a closed immersion.**
The precursor `β = productMap includeLeft chartCoaction : B ⊗[R] B →ₐ[R] B ⊗[R] A` has, under
the chart Künneth identifications `Spec(B⊗B) ≅ U ×_V U` and `Spec(B⊗A) ≅ G ×_V U`, the shape
`Spec.map β ≅ swap ∘ ⟨act, pr⟩|_chart` — the chart-restricted action pair. The action pair is a
closed immersion (`isClosedImmersion_actPair_left`: the base-changed `ι` composed with the shear
automorphism), and closed immersions are stable under the iso conjugation, hence `Spec.map β` is
a closed immersion.

The precursor legs are pinned by pure algebra + `pullbackSpecIso` naturality:
`β ∘ includeLeft = includeLeft` and `β ∘ includeRight = chartCoaction`, so under `pullbackSpecIso`
`Spec.map β` conjugates to `pullback.lift (pullback.fst) (pullbackSpecIso.hom ≫ Spec.map chartCoaction)`.
BANKED: `.mathlib-quality/decomposition-hopf-crux.md`, `[HG-C2]` geometric-identification. -/
theorem chartPrecursorSpec_isClosedImmersion :
    IsClosedImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft
          (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
        P.chartCoaction).toRingHom)) := by
  set β := (Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
    P.chartCoaction).toRingHom with hβ
  set e1 := AlgebraicGeometry.pullbackSpecIso P.baseRing P.chartRing P.groupRing with he1
  set e2 := AlgebraicGeometry.pullbackSpecIso P.baseRing P.chartRing P.chartRing with he2
  set g := e1.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom β) ≫ e2.inv with hg
  -- `Spec.map β` is `g` conjugated back by the two `pullbackSpecIso`s; conjugation by isos
  -- preserves closed immersions, so it suffices to show `g` is a closed immersion.
  have hrw : AlgebraicGeometry.Spec.map (CommRingCat.ofHom β) = e1.inv ≫ g ≫ e2.hom := by
    rw [hg]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [hrw]
  suffices hCI : IsClosedImmersion g by
    haveI := hCI
    infer_instance
  -- Leg computations (Step 2): β ∘ includeLeft = includeLeft (into B⊗A), β ∘ includeRight = chartCoaction.
  have key_incL :
      β.comp (Algebra.TensorProduct.includeLeftRingHom :
          P.chartRing →+* P.chartRing ⊗[P.baseRing] P.chartRing)
        = (Algebra.TensorProduct.includeLeftRingHom :
          P.chartRing →+* P.chartRing ⊗[P.baseRing] P.groupRing) := by
    ext b
    simp [hβ, Algebra.TensorProduct.productMap_apply_tmul]
  have key_incR :
      β.comp (Algebra.TensorProduct.includeRight :
          P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.chartRing).toRingHom
        = P.chartCoaction.toRingHom := by
    ext b
    simp only [hβ, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
  sorry

/-- **`[HG-C2]` last mile — the Galois precursor is surjective on the chart.** The `Spec` of the
Galois precursor is a closed immersion (`chartPrecursorSpec_isClosedImmersion`), and its target
`Spec (B ⊗[R] B)` is affine, so the precursor — in the Hopf-free form
`productMap includeLeft chartCoaction : B ⊗[R] B →ₐ[R] B ⊗[R] A` — is surjective. Since
`galoisPrecursor R A ρ` unfolds to this product map, this directly discharges the
`precursorSurjective` field of `StableAffineChartData` (see `chartData`). -/
theorem chartCoaction_productMap_surjective :
    Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
      P.chartCoaction) := by
  haveI := P.chartPrecursorSpec_isClosedImmersion
  exact surjective_hom_of_isClosedImmersion_specMap
    (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
      P.chartCoaction).toRingHom)

variable [Module.Free P.baseRing P.groupRing]

/-- **`[HG-C1d]`: the per-chart Hopf–Galois datum.** With the chart group-ring's Hopf-algebra
structure (`PatchHopf.instHopfAlgebraOpens`, built via `Bialgebra.ofAlgHom`/`HopfAlgebra.ofAlgHom`
over the **geometric** algebra — so no instance diamond) and its finiteness
(`instModuleFiniteGroupRing`), the proven co-action `chartCoaction`, its `IsCoaction` proof
(`chartCoaction_isCoaction`), and the precursor surjectivity (`chartCoaction_productMap_surjective`)
assemble into a `StableAffineChartData`. The lone hypothesis `Module.Free P.baseRing P.groupRing` is
the freeness of `G` per chart, provided by shrinking the base patch in `[HG-C3]` (it bundles no
competing algebra instance, so hypothesis-wiring it is diamond-free). -/
noncomputable def chartData : StableAffineChartData P.baseRing P.groupRing P.chartRing where
  coaction := P.chartCoaction
  isCoaction := P.chartCoaction_isCoaction
  precursorSurjective := P.chartCoaction_productMap_surjective

/-- **The chart co-action is Hopf–Galois** (`[HG-C1d]` → M5): the abstract Hopf–Galois theorem
(`StableAffineChartData.isHopfGalois`) applied to the chart datum. This is the per-chart property
consumed by `isColimit_of_isHopfGalois` in the `[HG-C4]` glue that discharges the six
`SubgroupQuotient` pins. -/
theorem isHopfGalois_chartCoaction : IsHopfGalois P.chartCoaction :=
  P.chartData.isHopfGalois

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
