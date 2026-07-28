/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveAdicPresentation
import «Adic spaces».SpaVIso
import «Adic spaces».VRestrict
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# The `𝒴`-side leg of the Fargues–Fontaine adic-space capstone

`𝒴` is *by definition* a restriction of the ambient adic spectrum,
`yPresheafedSpace p F ϖ = (yAmbientPresheafedSpace p F).restrict (yIncl_isOpenEmbedding p F ϖ)`.
Consequently, for an open `V` of `𝒴`, the slice `𝒴|_V` sits inside the ambient
`Spa(A_inf)` as a composite of two `ofRestrict`s — hence as an open immersion, whose
range is the ambient image of `V`.  Any *other* open immersion into `Spa(A_inf)` with
that same range is therefore canonically isomorphic to `𝒴|_V` (`ySliceIso`).

The second half instantiates this at the Fargues–Fontaine window charts: for a
rational datum `D'` over the `n`-th window chart ring `B_n`, the composite comparison
`Spa(𝒪(D')) ⟶ Spa(B_n) = Spa(𝒪(D₀)) ⟶ Spa(A_inf)` is an open immersion landing inside
`𝒴`, so it exhibits `Spa(𝒪(D'))` as an open slice of `𝒴` (`windowSubYSliceIso`).

Section 1 (`ySliceIncl` … `ySliceIsoOfSubset`) only needs
`«Adic spaces».FarguesFontaine.YStalks`, `«Adic spaces».VRestrict` and
`Mathlib.Geometry.RingedSpace.OpenImmersion`; the heavier imports are for section 2.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology
  Filter CategoryTheory Opposite Pointwise
open scoped AlgebraicGeometry

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-! ## 1. The `𝒴`-side leg -/

/-! ### The slice inclusion `𝒴|_V ⟶ Spa(A_inf)` -/

/-- The inclusion of a slice of `𝒴` into the ambient adic spectrum: the composite
of the two restriction inclusions `𝒴|_V ⟶ 𝒴 ⟶ Spa(A_inf)`. -/
def ySliceIncl (V : Opens ↥(yTop p F ϖ)) :
    (yPresheafedSpace p F ϖ).restrict
        (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ) V)
      ⟶ yAmbientPresheafedSpace p F :=
  (yPresheafedSpace p F ϖ).ofRestrict
      (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ) V) ≫
    (yAmbientPresheafedSpace p F).ofRestrict (yIncl_isOpenEmbedding p F ϖ)

/-- **The slice inclusion is an open immersion.**  Both legs are `ofRestrict`s, but
neither instance is found by search alone: `(yAmbientPresheafedSpace p F).carrier`
only *definitionally* equals `SpaTop (Ainf p F)`, and typeclass unification is
reducible-only — so mathlib's `ofRestrict` / `comp` instances are applied by hand. -/
instance ySliceIncl_isOpenImmersion (V : Opens ↥(yTop p F ϖ)) :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion (ySliceIncl p F ϖ V) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
    (f := (yPresheafedSpace p F ϖ).ofRestrict
      (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ) V))
    (H := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict
      (yPresheafedSpace p F ϖ)
      (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ) V))
    (g := (yAmbientPresheafedSpace p F).ofRestrict (yIncl_isOpenEmbedding p F ϖ))
    (hg := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict
      (yAmbientPresheafedSpace p F) (yIncl_isOpenEmbedding p F ϖ))

/-- **The range of the slice inclusion is the ambient image of `V`.**  Proved in term
mode against `ValuationSpectrum.range_val_val`: the carrier spellings
(`Opens ↥(yTop p F ϖ)` versus `Opens ↑↑((yAmbientPresheafedSpace p F).restrict ⋯)`)
are only definitionally equal, so `rw` — which matches up to implicit transparency —
would make `Membership.mem` ill-typed on the goal. -/
theorem range_ySliceIncl (V : Opens ↥(yTop p F ϖ)) :
    Set.range (ConcreteCategory.hom (ySliceIncl p F ϖ V).base)
      = (Subtype.val : ↥(yTop p F ϖ) → ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
          '' (V : Set ↥(yTop p F ϖ)) :=
  (ValuationSpectrum.range_val_val (α := ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      (ySpaSet p F ϖ) (V : Set ↥(yTop p F ϖ))).trans Subtype.range_coe

/-! ### The leg itself -/

/-- **The `𝒴`-side leg**: an open immersion into the ambient `Spa(A_inf)` whose range
is the image of an open `V` of `𝒴` induces `Spa(B) ≅ 𝒴|_V`. -/
noncomputable def ySliceIso {Z : ValuationSpectrum.TopRingPresheafedSpace}
    (f : Z ⟶ FarguesFontaine.yAmbientPresheafedSpace p F)
    [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f]
    (V : Opens ↥(FarguesFontaine.yTop p F ϖ))
    (hrange : Set.range (ConcreteCategory.hom f.base)
      = Subtype.val '' (V : Set ↥(FarguesFontaine.yTop p F ϖ))) :
    Z ≅ (FarguesFontaine.yPresheafedSpace p F ϖ).restrict
          (ValuationSpectrum.openIncl_isOpenEmbedding
            (X := yPresheafedSpace p F ϖ) V) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq f
    (ySliceIncl p F ϖ V) (hrange.trans (range_ySliceIncl p F ϖ V).symm)

/-! ### Producing the open `V` from a range contained in `𝒴` -/

/-- The `𝒴`-trace of an open subset of the ambient `Spa (A_inf, A_inf)`. -/
def yTrace (S : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (hS : IsOpen S) :
    Opens ↥(yTop p F ϖ) :=
  ⟨(Subtype.val : ↥(yTop p F ϖ) → ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) ⁻¹' S,
    hS.preimage continuous_subtype_val⟩

omit [CharP F p] in
/-- **A subset of `Spa(A_inf)` contained in `𝒴` is the ambient image of its
`𝒴`-trace.**  This is what makes the `hrange` hypothesis of `ySliceIso` hold *by
construction* for any open immersion whose range lands in `𝒴`. -/
theorem image_yTrace (S : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hS : IsOpen S) (hsub : S ⊆ ySpaSet p F ϖ) :
    (Subtype.val : ↥(yTop p F ϖ) → ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        '' ((yTrace p F ϖ S hS : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
      = S :=
  (Subtype.image_preimage_coe (ySpaSet p F ϖ) S).trans (Set.inter_eq_right.mpr hsub)

/-- **The `𝒴`-side leg, range form**: an open immersion into `Spa(A_inf)` whose range
lands inside `𝒴` is an isomorphism onto the slice of `𝒴` cut out by the `𝒴`-trace of
that range.  No `hrange` hypothesis is needed — the open `V` is built from `f`. -/
noncomputable def ySliceIsoOfSubset {Z : ValuationSpectrum.TopRingPresheafedSpace}
    (f : Z ⟶ FarguesFontaine.yAmbientPresheafedSpace p F)
    [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f]
    (hsub : Set.range (ConcreteCategory.hom f.base) ⊆ ySpaSet p F ϖ) :
    Z ≅ (FarguesFontaine.yPresheafedSpace p F ϖ).restrict
          (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ)
            (yTrace p F ϖ (Set.range (ConcreteCategory.hom f.base))
              (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open
                (f := f)).isOpen_range)) :=
  ySliceIso p F ϖ f _
    (image_yTrace p F ϖ (Set.range (ConcreteCategory.hom f.base))
      (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open
        (f := f)).isOpen_range hsub).symm

/-! ## 2. Instantiation at the Fargues–Fontaine window charts

`CurveAdicPresentation.lean` declares the Tate / strongly-noetherian / noetherian
facts for `windowChartRing` as **`local instance`s**, so they are re-declared here,
together with their rational-subdatum consequences. -/

noncomputable local instance instTateWindow (n : ℤ) :
    IsTateRing (windowChartRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

noncomputable local instance instStronglyNoetherianWindow (n : ℤ) :
    IsStronglyNoetherian (windowChartRing p F ϖ n) :=
  isStronglyNoetherian_canonical_window p F ϖ n

noncomputable local instance instNoetherianWindow (n : ℤ) :
    IsNoetherianRing (windowChartRing p F ϖ n) :=
  IsStronglyNoetherian.isNoetherianRing _

noncomputable local instance instDecEqAinf : DecidableEq (Ainf p F) := Classical.decEq _

noncomputable local instance instDecEqWindow (n : ℤ) :
    DecidableEq (windowChartRing p F ϖ n) := Classical.decEq _

noncomputable local instance instTateWindowSub (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsTateRing (presheafValue D') :=
  presheafValue_isTateRing_concrete D'

noncomputable local instance instStronglyNoetherianWindowSub (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsStronglyNoetherian (presheafValue D') :=
  presheafValue_isStronglyNoetherian_faithful D'

noncomputable local instance instNoetherianWindowSub (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsNoetherianRing (presheafValue D') :=
  IsStronglyNoetherian.isNoetherianRing _

variable (n : ℤ) (D' : RationalLocData (windowChartRing p F ϖ n))
  (u' : (presheafValue D')ˣ)
  (hu' : IsTopologicallyNilpotent ((u' : (presheafValue D')ˣ) : presheafValue D'))
  (u : (windowChartRing p F ϖ n)ˣ)
  (hu : IsTopologicallyNilpotent
    ((u : (windowChartRing p F ϖ n)ˣ) : windowChartRing p F ϖ n))

/-- **The two-step chart comparison** `Spa(𝒪(D')) ⟶ Spa(B_n) ⟶ Spa(A_inf)`.  The
middle identification is definitional: `bSpace (chartData …) = spaSpace (A := B_n)`
and `spaSpace (A := A_inf) = yAmbientPresheafedSpace p F` are both `rfl`, because
`windowChartRing p F ϖ n` *is* `presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)`. -/
noncomputable def windowSubCompHom :
    ValuationSpectrum.SpaVIso.bSpace D' ⟶ yAmbientPresheafedSpace p F :=
  ValuationSpectrum.SpaVIso.spaCompHom D' u' hu' ≫
    ValuationSpectrum.SpaVIso.spaCompHom
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu

/-- **The two-step chart comparison is an open immersion** — a composite of two
`spaCompHom`s.  Again applied by hand: `spaSpace (A := B_n)` and `bSpace (chartData …)`
are definitionally, not reducibly, equal. -/
instance windowSubCompHom_isOpenImmersion :
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
      (windowSubCompHom p F ϖ n D' u' hu' u hu) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
    (f := ValuationSpectrum.SpaVIso.spaCompHom D' u' hu')
    (H := ValuationSpectrum.SpaVIso.spaCompHom_isOpenImmersion D' u' hu')
    (g := ValuationSpectrum.SpaVIso.spaCompHom
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)
    (hg := ValuationSpectrum.SpaVIso.spaCompHom_isOpenImmersion
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)

/-- **The shadow of a window-chart point lies in `𝒴`**: it lies in the `n`-th Big
window (Wedhorn 8.2 for the chart datum), and Big windows exhaust `𝒴`. -/
theorem shadow_windowDatum_mem_ySpaSet (hp : 1 < p)
    (y : ↥(Spa (windowChartRing p F ϖ n) (windowChartRing p F ϖ n)⁺)) :
    ValuationSpectrum.SpaVIso.shadow
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1) y ∈ ySpaSet p F ϖ := by
  show comap (chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
      (y : Spv (windowChartRing p F ϖ n)) ∈ Y p F ϖ
  refine mem_Y_of_mem_bigWindow p F ϖ hp n ?_
  rw [bigWindow_eq_rationalOpen_windowUnif p F ϖ n]
  exact (comap_canonicalMap_mem_rationalOpen_inter_spa
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1) y).1

/-- **The range of the two-step comparison lands inside `𝒴`.** -/
theorem range_windowSubCompHom_subset (hp : 1 < p) :
    Set.range (ConcreteCategory.hom
        (windowSubCompHom p F ϖ n D' u' hu' u hu).base) ⊆ ySpaSet p F ϖ := by
  rintro _ ⟨w, rfl⟩
  exact shadow_windowDatum_mem_ySpaSet p F ϖ n hp _

/-- The open of `𝒴` cut out by a rational subdatum of the `n`-th window chart: the
`𝒴`-trace of the range of the two-step comparison. -/
def windowSubOpen : Opens ↥(yTop p F ϖ) :=
  yTrace p F ϖ
    (Set.range (ConcreteCategory.hom (windowSubCompHom p F ϖ n D' u' hu' u hu).base))
    (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open
      (f := windowSubCompHom p F ϖ n D' u' hu' u hu)).isOpen_range

/-- **The window-chart instance of the `𝒴`-side leg**: for a rational datum `D'` over
the `n`-th window chart ring, `Spa(𝒪(D'))` is isomorphic, as a presheafed space of
complete topological rings, to the slice of `𝒴` over `windowSubOpen`. -/
noncomputable def windowSubYSliceIso (hp : 1 < p) :
    ValuationSpectrum.SpaVIso.bSpace D' ≅
      (yPresheafedSpace p F ϖ).restrict
        (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ)
          (windowSubOpen p F ϖ n D' u' hu' u hu)) :=
  ySliceIsoOfSubset p F ϖ (windowSubCompHom p F ϖ n D' u' hu' u hu)
    (range_windowSubCompHom_subset p F ϖ n D' u' hu' u hu hp)

end FarguesFontaine

end
