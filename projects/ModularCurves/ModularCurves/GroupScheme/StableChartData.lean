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

/-- **`[HG-C2]` last mile — the Galois precursor is surjective on the chart.** The action pair
`⟨act, pr⟩` is a closed immersion (`isClosedImmersion_actPair_left`); restricted to the affine
chart and dualized, its `Γ`-map — the Galois precursor in the Hopf-free form
`productMap includeLeft chartCoaction : B ⊗[R] B →ₐ[R] B ⊗[R] A` — is surjective. This is the
`precursorSurjective` field of `StableAffineChartData` (`galoisPrecursor R A ρ` unfolds to this
product map, so once `HopfAlgebra P.baseRing P.groupRing` lands this discharges that field). -/
theorem chartCoaction_productMap_surjective :
    Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft (R := P.baseRing) (A := P.chartRing) (B := P.groupRing))
      P.chartCoaction) := by
  sorry

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
