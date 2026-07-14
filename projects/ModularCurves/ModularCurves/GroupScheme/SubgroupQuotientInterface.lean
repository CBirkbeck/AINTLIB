import ModularCurves.GroupScheme.Subgroup

/-!
# The `G`-invariance interface for the quotient `E/G`

**Low interface layer (T-G3d-infra).** The descent condition
`FiniteLocallyFreeSubgroup.IsInvariant` on a morphism out of `E`, extracted here — *below*
`TranslationAction` — so that the quotient construction (which imports `TranslationAction`) can in
turn be imported by `SubgroupQuotient.lean` when discharging the six pins, with no import cycle.
Only `IsInvariant` (+ `IsInvariant.comp`) lives here; the pins
(`quotient` / `quotientS` / `quotientπ` / …) stay in `SubgroupQuotient.lean`, where they are
discharged against the glue construction.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

/-- A morphism `f : E ⟶ Y` is **invariant** under the translation action of the finite locally free
subgroup scheme `G ⊆ E` when `f(x + t) = f(x)` for every point `x : E.Point g` and every `G`-point
`t` (`t ∈ G.pointSubgroup g`). This is the functor-of-points form of the coequalizer condition cut
out by the two maps `G ×_S E ⇉ E` (translate `(t, x) ↦ x + t`, project `(t, x) ↦ x`); it is the
universal condition for a morphism to factor through `E/G`. -/
def FiniteLocallyFreeSubgroup.IsInvariant (G : FiniteLocallyFreeSubgroup E) {Y : Scheme.{u}}
    (f : E.E ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (x t : E.Point g), t ∈ G.pointSubgroup g →
    (x + t).1 ≫ f = x.1 ≫ f

namespace FiniteLocallyFreeSubgroup

/-- Invariance is preserved by post-composition: if `f` collapses `G`-translates, so does `f ≫ h`. -/
theorem IsInvariant.comp {G : FiniteLocallyFreeSubgroup E} {Y Z : Scheme.{u}} {f : E.E ⟶ Y}
    (hf : G.IsInvariant f) (h : Y ⟶ Z) : G.IsInvariant (f ≫ h) := fun _ g x t ht => by
  rw [← Category.assoc, hf g x t ht, Category.assoc]

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
