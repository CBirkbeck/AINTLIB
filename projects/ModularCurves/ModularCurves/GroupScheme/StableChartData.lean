import ModularCurves.GroupScheme.ChartCoaction
import ModularCurves.GroupScheme.HopfGaloisCharts
import ModularCurves.GroupScheme.ActPairImmersion

/-!
# The per-chart Hopf–Galois inputs (`[HG-C1d]`/`[HG-C2]` last mile)

Construction support for `[CHARTER-HOPF]` Wave C (`.mathlib-quality/decomposition-hopf-crux.md`,
appendix "Wave C — pin-map + C3 cover strategy"). On a `G`-stable affine chart patch `P`
(an `AffineChartPatch`), the abstract Hopf–Galois theorem M5 consumes a
`StableAffineChartData P.baseRing P.groupRing P.chartRing`, whose three fields are:
* `coaction := P.chartCoaction` (`StableCharts`) — DONE upstream,
* `isCoaction := P.chartCoaction_isCoaction` (`ChartCoaction`) — DONE upstream,
* `precursorSurjective` — the `Γ`-dual of C2's `isClosedImmersion_actPair_left`.

This file supplies the two non-co-action inputs that do **not** need the (not-yet-landed)
`HopfAlgebra P.baseRing P.groupRing` instance:

* `instModuleFiniteGroupRing : Module.Finite P.baseRing P.groupRing` — from `G.π` finite.
* `chartCoaction_productMap_surjective` — surjectivity of the Galois precursor written in the
  **Hopf-free** form `productMap includeLeft chartCoaction`. Since
  `galoisPrecursor R A ρ` is *by definition* `productMap includeLeft ρ` (the `HopfAlgebra`
  hypothesis on its section is spurious for the map itself), this lemma discharges the
  `precursorSurjective` field verbatim once the `HopfAlgebra` instance lands.

**Boarded blocker (the HopfAlgebra diamond).** Feeding `P.chartCoaction` into M5 (the C1d
`StableAffineChartData` assembly and `IsHopfGalois P.chartCoaction`) is blocked until p2's
Hopf-instance layer provides `HopfAlgebra P.baseRing P.groupRing` **whose underlying
`Algebra P.baseRing P.groupRing` is (defeq to) the geometric `AffineChartPatch` instance** —
a free `[HopfAlgebra …]` variable supplies its own `Bialgebra`-derived algebra instance, which
does not match the geometric one that `chartCoaction` is typed against. The two lemmas here are
exactly the parts of that assembly that sidestep the diamond.
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
  sorry

/-- **`[HG-C2]` last mile — the Galois precursor is surjective on the chart.** The `Spec` of the
Galois precursor is a closed immersion (`chartPrecursorSpec_isClosedImmersion`), and its target
`Spec (B ⊗[R] B)` is affine, so the precursor — in the Hopf-free form
`productMap includeLeft chartCoaction : B ⊗[R] B →ₐ[R] B ⊗[R] A` — is surjective. This is the
`precursorSurjective` field of `StableAffineChartData` (`galoisPrecursor R A ρ` unfolds to this
product map, so once `HopfAlgebra P.baseRing P.groupRing` lands this discharges that field). -/
theorem chartCoaction_productMap_surjective :
    Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
      P.chartCoaction) := by
  haveI := P.chartPrecursorSpec_isClosedImmersion
  exact surjective_hom_of_isClosedImmersion_specMap
    (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
      P.chartCoaction).toRingHom)

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
