/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveYSlice

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

noncomputable local instance instTateWindowK (n : ℤ) :
    IsTateRing (windowChartRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

noncomputable local instance instStronglyNoetherianWindowK (n : ℤ) :
    IsStronglyNoetherian (windowChartRing p F ϖ n) :=
  isStronglyNoetherian_canonical_window p F ϖ n

noncomputable local instance instNoetherianWindowK (n : ℤ) :
    IsNoetherianRing (windowChartRing p F ϖ n) :=
  IsStronglyNoetherian.isNoetherianRing _

noncomputable local instance instDecEqAinfK : DecidableEq (Ainf p F) := Classical.decEq _

noncomputable local instance instDecEqWindowK (n : ℤ) :
    DecidableEq (windowChartRing p F ϖ n) := Classical.decEq _

noncomputable local instance instTateWindowSubK (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsTateRing (presheafValue D') :=
  presheafValue_isTateRing_concrete D'

noncomputable local instance instStronglyNoetherianWindowSubK (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsStronglyNoetherian (presheafValue D') :=
  presheafValue_isStronglyNoetherian_faithful D'

noncomputable local instance instNoetherianWindowSubK (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsNoetherianRing (presheafValue D') :=
  IsStronglyNoetherian.isNoetherianRing _

variable (n : ℤ) (D' : RationalLocData (windowChartRing p F ϖ n))
  (u' : (presheafValue D')ˣ)
  (hu' : IsTopologicallyNilpotent ((u' : (presheafValue D')ˣ) : presheafValue D'))
  (u : (windowChartRing p F ϖ n)ˣ)
  (hu : IsTopologicallyNilpotent
    ((u : (windowChartRing p F ϖ n)ˣ) : windowChartRing p F ϖ n))

-- probe 1: can we restate the two legs?
example (z : ↥(Spa (presheafValue D') (presheafValue D')⁺)) :
    stalkValue (ValuationSpectrum.SpaVIso.shadow D' z)
      = comap (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom D' u' hu') z).hom'
        (stalkValue z) :=
  ValuationSpectrum.SpaVIso.comap_ringStalkMap_spaCompHom_stalkValue D' u' hu' z

example (w : ↥(Spa (windowChartRing p F ϖ n) (windowChartRing p F ϖ n)⁺)) :
    stalkValue (ValuationSpectrum.SpaVIso.shadow
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1) w)
      = comap (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu) w).hom'
        (stalkValue w) :=
  ValuationSpectrum.SpaVIso.comap_ringStalkMap_spaCompHom_stalkValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu w

-- probe 2: does `windowSubCompHom` unfold to the composite by `rfl` in this file?
example : windowSubCompHom p F ϖ n D' u' hu' u hu
    = ValuationSpectrum.SpaVIso.spaCompHom D' u' hu' ≫
      ValuationSpectrum.SpaVIso.spaCompHom
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu := rfl

/-- **(★) The two-step chart comparison intertwines the stalk valuations.**  Each
leg is a `spaCompHom`, whose valuation compatibility is unconditional
(`comap_ringStalkMap_spaCompHom_stalkValue`); the composite follows by
contravariant functoriality of `ringStalkMap` and of `comap`. -/
theorem comap_ringStalkMap_windowSubCompHom_stalkValue
    (z : ↥(Spa (presheafValue D') (presheafValue D')⁺)) :
    stalkValue (ConcreteCategory.hom
        (windowSubCompHom p F ϖ n D' u' hu' u hu).base z)
      = comap (ringStalkMap (windowSubCompHom p F ϖ n D' u' hu' u hu) z).hom'
          (stalkValue z) := by
  have h1 : stalkValue (ValuationSpectrum.SpaVIso.shadow D' z)
      = comap (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom D' u' hu') z).hom'
        (stalkValue z) :=
    ValuationSpectrum.SpaVIso.comap_ringStalkMap_spaCompHom_stalkValue D' u' hu' z
  have h2 : stalkValue (ValuationSpectrum.SpaVIso.shadow
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
        (ValuationSpectrum.SpaVIso.shadow D' z))
      = comap (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)
          (ValuationSpectrum.SpaVIso.shadow D' z)).hom'
        (stalkValue (ValuationSpectrum.SpaVIso.shadow D' z)) :=
    ValuationSpectrum.SpaVIso.comap_ringStalkMap_spaCompHom_stalkValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu
      (ValuationSpectrum.SpaVIso.shadow D' z)
  have hcomp : ringStalkMap (windowSubCompHom p F ϖ n D' u' hu' u hu) z
      = ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom
            (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)
          (ValuationSpectrum.SpaVIso.shadow D' z)
        ≫ ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom D' u' hu') z :=
    ringStalkMap_comp
      (X := ValuationSpectrum.SpaVIso.bSpace D')
      (Y := ValuationSpectrum.SpaVIso.bSpace
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1))
      (Z := yAmbientPresheafedSpace p F)
      (ValuationSpectrum.SpaVIso.spaCompHom D' u' hu')
      (ValuationSpectrum.SpaVIso.spaCompHom
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu) z
  have h4 := congrFun (comap_comp
      (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)
        (ValuationSpectrum.SpaVIso.shadow D' z)).hom'
      (ringStalkMap (ValuationSpectrum.SpaVIso.spaCompHom D' u' hu') z).hom')
    (stalkValue z)
  refine Eq.trans ?_ (congrArg
    (fun ρ => comap (CommRingCat.Hom.hom' ρ) (stalkValue z)) hcomp.symm)
  exact h2.trans ((congrArg (ValuationSpectrum.comap (ringStalkMap
    (ValuationSpectrum.SpaVIso.spaCompHom
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1) u hu)
    (ValuationSpectrum.SpaVIso.shadow D' z)).hom') h1).trans h4.symm)


/-! ### The two `𝒴`-side inclusions -/

section YIncl

variable (V : Opens ↥(yTop p F ϖ))

/-- The `𝒴`-inclusion `𝒴 ⟶ Spa(A_inf)`. -/
noncomputable abbrev yAmbOfRestrict :
    yPresheafedSpace p F ϖ ⟶ yAmbientPresheafedSpace p F :=
  (yAmbientPresheafedSpace p F).ofRestrict (yIncl_isOpenEmbedding p F ϖ)

/-- The slice inclusion `𝒴|_V ⟶ 𝒴`, in the `openIncl` spelling of `ySliceIncl`. -/
noncomputable abbrev ySliceOfRestrict :
    ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace ⟶ yPresheafedSpace p F ϖ :=
  (yPresheafedSpace p F ϖ).ofRestrict
    (ValuationSpectrum.openIncl_isOpenEmbedding (X := yPresheafedSpace p F ϖ) V)

theorem ySliceIncl_eq :
    ySliceIncl p F ϖ V = ySliceOfRestrict p F ϖ V ≫ yAmbOfRestrict p F ϖ := rfl

/-- **The `𝒴`-stalk comparison inverts the inclusion's stalk map** (mathlib's
`restrictStalkIso_inv_eq_ofRestrict` in the `ringStalkMap` spelling). -/
theorem yRingStalkEquiv_ringStalkMap_yAmbOfRestrict (x : yTop p F ϖ)
    (t : ToType ((yAmbientPresheafedSpace p F).ringStalk (ySpaPoint p F ϖ x))) :
    (yRingStalkEquiv p F ϖ x)
        ((ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' t) = t := by
  have h1 : ringStalkMap (yAmbOfRestrict p F ϖ) x = (yRingStalkIso p F ϖ x).inv :=
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict
      (yAmbientRingSpace p F) (yIncl_isOpenEmbedding p F ϖ) x).symm
  rw [h1]
  exact congrFun (congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m).toFun)
    ((yRingStalkIso p F ϖ x).inv_hom_id)) t

/-- The `𝒴`-inclusion's stalk map is surjective. -/
theorem ringStalkMap_yAmbOfRestrict_surjective (x : yTop p F ϖ) :
    Function.Surjective (ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' := fun c =>
  ⟨yRingStalkEquiv p F ϖ x c, (yRingStalkEquiv p F ϖ x).injective
    (yRingStalkEquiv_ringStalkMap_yAmbOfRestrict p F ϖ x _)⟩

/-- **The `𝒴`-inclusion is valuation-compatible**: the ambient stalk valuation
pulls back the `𝒴`-stalk valuation. -/
theorem stalkValue_eq_comap_yVPreObj_val (x : yTop p F ϖ) :
    stalkValue (ySpaPoint p F ϖ x)
      = comap (ringStalkMap (yAmbOfRestrict p F ϖ) x).hom'
          ((yVPreObj p F ϖ).val x) := by
  refine ValuationSpectrum.ext (funext₂ fun a b => propext ?_)
  show (stalkValue (ySpaPoint p F ϖ x)).vle a b
      ↔ ((yVPreObj p F ϖ).val x).vle
          ((ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' a)
          ((ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' b)
  show (stalkValue (ySpaPoint p F ϖ x)).vle a b
      ↔ (stalkValue (ySpaPoint p F ϖ x)).vle
          ((yRingStalkEquiv p F ϖ x)
            ((ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' a))
          ((yRingStalkEquiv p F ϖ x)
            ((ringStalkMap (yAmbOfRestrict p F ϖ) x).hom' b))
  rw [yRingStalkEquiv_ringStalkMap_yAmbOfRestrict p F ϖ x a,
    yRingStalkEquiv_ringStalkMap_yAmbOfRestrict p F ϖ x b]

/-- The stalk-map splitting of the slice inclusion `𝒴|_V ⟶ Spa(A_inf)`.  The two
legs are passed to `ringStalkMap_comp` explicitly: inference otherwise picks the
wrong (only definitionally equal) spelling of the middle object. -/
theorem ringStalkMap_ySliceIncl (y : ↥V) :
    ringStalkMap (ySliceIncl p F ϖ V) y
      = ringStalkMap (yAmbOfRestrict p F ϖ)
          (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)
        ≫ ringStalkMap (ySliceOfRestrict p F ϖ V) y :=
  ringStalkMap_comp
    (X := ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace)
    (Y := yPresheafedSpace p F ϖ) (Z := yAmbientPresheafedSpace p F)
    (ySliceOfRestrict p F ϖ V) (yAmbOfRestrict p F ϖ) y

/-- **The slice inclusion's stalk map is surjective** — both legs are restriction
inclusions, whose stalk maps invert the restriction stalk comparisons. -/
theorem ringStalkMap_ySliceIncl_surjective (y : ↥V) :
    Function.Surjective (ringStalkMap (ySliceIncl p F ϖ V) y).hom' := by
  have hsplit : (ringStalkMap (ySliceIncl p F ϖ V) y).hom'
      = (ringStalkMap (ySliceOfRestrict p F ϖ V) y).hom'.comp
          (ringStalkMap (yAmbOfRestrict p F ϖ)
            (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)).hom' :=
    congrArg CommRingCat.Hom.hom' (ringStalkMap_ySliceIncl p F ϖ V y)
  rw [hsplit]
  exact (ValuationSpectrum.ringStalkMap_ofRestrict_surjective
      (X := yVPreObj p F ϖ) V y).comp
    (ringStalkMap_yAmbOfRestrict_surjective p F ϖ _)

/-- **The slice inclusion `𝒴|_V ⟶ Spa(A_inf)` is valuation-compatible**: the
ambient stalk valuation pulls back the slice stalk valuation.  Both legs are
restriction inclusions, so this is `VPreHom.ofRestrictOpen` followed by the
`𝒴`-inclusion compatibility. -/
theorem stalkValue_eq_comap_ySliceIncl_val (y : ↥V) :
    stalkValue (ConcreteCategory.hom (ySliceIncl p F ϖ V).base y)
      = comap (ringStalkMap (ySliceIncl p F ϖ V) y).hom'
          (((yVPreObj p F ϖ).restrictOpen V).val y) := by
  have hincl : (yVPreObj p F ϖ).val
        (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)
      = comap (ringStalkMap (ySliceOfRestrict p F ϖ V) y).hom'
          (((yVPreObj p F ϖ).restrictOpen V).val y) :=
    (ValuationSpectrum.VPreHom.ofRestrictOpen (X := yVPreObj p F ϖ) V).val_compat y
  refine (stalkValue_eq_comap_yVPreObj_val p F ϖ
    (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)).trans ?_
  refine (congrArg (ValuationSpectrum.comap (ringStalkMap (yAmbOfRestrict p F ϖ)
    (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)).hom') hincl).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun m => ValuationSpectrum.comap (CommRingCat.Hom.hom' m)
      (((yVPreObj p F ϖ).restrictOpen V).val y))
    (ringStalkMap_ySliceIncl p F ϖ V y).symm)
  exact (congrFun (comap_comp (ringStalkMap (yAmbOfRestrict p F ϖ)
      (ConcreteCategory.hom (ySliceOfRestrict p F ϖ V).base y)).hom'
    (ringStalkMap (ySliceOfRestrict p F ϖ V) y).hom') _).symm

/-- **The `𝒴`-slice valuation criterion.**  A morphism `k` from a `𝒱^pre`-object
`Z` into the slice `𝒴|_V` is valuation-compatible as soon as its composite into
the ambient `Spa(A_inf)` is: the slice inclusion's stalk map is surjective, so
`comap` along it is injective and may be cancelled. -/
theorem val_compat_of_ambient {Z : ValuationSpectrum.VPreObj}
    (k : Z.toPresheafedSpace
      ⟶ ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace)
    (z : Z.toPresheafedSpace)
    (hamb : stalkValue (ConcreteCategory.hom (k ≫ ySliceIncl p F ϖ V).base z)
      = comap (ringStalkMap (k ≫ ySliceIncl p F ϖ V) z).hom' (Z.val z)) :
    ((yVPreObj p F ϖ).restrictOpen V).val (ConcreteCategory.hom k.base z)
      = comap (ringStalkMap k z).hom' (Z.val z) := by
  refine comap_injective (ringStalkMap_ySliceIncl_surjective p F ϖ V
    (ConcreteCategory.hom k.base z)) ?_
  refine (stalkValue_eq_comap_ySliceIncl_val p F ϖ V
    (ConcreteCategory.hom k.base z)).symm.trans ?_
  refine hamb.trans ?_
  refine (congrArg (fun m => ValuationSpectrum.comap (CommRingCat.Hom.hom' m)
    (Z.val z)) (ringStalkMap_comp (X := Z.toPresheafedSpace)
      (Y := ((yVPreObj p F ϖ).restrictOpen V).toPresheafedSpace)
      (Z := yAmbientPresheafedSpace p F) k (ySliceIncl p F ϖ V) z)).trans ?_
  exact congrFun (comap_comp (ringStalkMap (ySliceIncl p F ϖ V)
    (ConcreteCategory.hom k.base z)).hom' (ringStalkMap k z).hom') (Z.val z)

end YIncl


/-! ### The chart `𝒱^pre`-isomorphism -/

/-- The chart comparison factors the two-step comparison through the slice
inclusion (mathlib's `IsOpenImmersion.lift_fac` at `ySliceIncl`). -/
theorem windowSubYSliceIso_hom_fac (hp : 1 < p) :
    (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom
        ≫ ySliceIncl p F ϖ (windowSubOpen p F ϖ n D' u' hu' u hu)
      = windowSubCompHom p F ϖ n D' u' hu' u hu :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
    (ySliceIncl p F ϖ (windowSubOpen p F ϖ n D' u' hu' u hu))
    (windowSubCompHom p F ϖ n D' u' hu' u hu)
    (le_of_eq
      (((image_yTrace p F ϖ
          (Set.range (ConcreteCategory.hom
            (windowSubCompHom p F ϖ n D' u' hu' u hu).base))
          (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open
            (f := windowSubCompHom p F ϖ n D' u' hu' u hu)).isOpen_range
          (range_windowSubCompHom_subset p F ϖ n D' u' hu' u hu hp)).symm).trans
        (range_ySliceIncl p F ϖ
          (windowSubOpen p F ϖ n D' u' hu' u hu)).symm))

/-- **The chart comparison respects the stalk valuations.**  The ambient identity
is (★); the slice criterion `val_compat_of_ambient` transports it down. -/
theorem windowSubYSliceIso_val_compat (hp : 1 < p)
    (z : ↥(ValuationSpectrum.spaVObjTate
      (A := presheafValue D')).toVPreObj.toTopCat) :
    ((yVPreObj p F ϖ).restrictOpen
          (windowSubOpen p F ϖ n D' u' hu' u hu)).val
        (ConcreteCategory.hom
          (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom.base z)
      = comap (ringStalkMap
            (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom z).hom'
          ((ValuationSpectrum.spaVObjTate
            (A := presheafValue D')).toVPreObj.val z) := by
  refine val_compat_of_ambient p F ϖ (windowSubOpen p F ϖ n D' u' hu' u hu)
    (Z := (ValuationSpectrum.spaVObjTate (A := presheafValue D')).toVPreObj)
    (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom z ?_
  have key : ∀ m : ValuationSpectrum.SpaVIso.bSpace D'
        ⟶ yAmbientPresheafedSpace p F,
      m = windowSubCompHom p F ϖ n D' u' hu' u hu →
      stalkValue (ConcreteCategory.hom m.base z)
        = comap (ringStalkMap m z).hom' (stalkValue z) := by
    rintro m rfl
    exact comap_ringStalkMap_windowSubCompHom_stalkValue p F ϖ n D' u' hu' u hu z
  exact key _ (windowSubYSliceIso_hom_fac p F ϖ n D' u' hu' u hu hp)

/-- **THE CHART `𝒱^pre`-ISOMORPHISM** (the last step of the Fargues–Fontaine
capstone): for a rational datum `D'` over the `n`-th window chart ring, the
affinoid `Spa(𝒪(D'))` is isomorphic *in Wedhorn's category `𝒱^pre`* — carrying
the structure presheaf, the stalk local rings and the stalk valuations — to the
slice of `𝒴` that it cuts out. -/
noncomputable def windowSubVPreHom (hp : 1 < p) :
    ValuationSpectrum.VPreHom
      (ValuationSpectrum.spaVObjTate (A := presheafValue D')).toVPreObj
      ((yVPreObj p F ϖ).restrictOpen
        (windowSubOpen p F ϖ n D' u' hu' u hu)) :=
  ValuationSpectrum.VPreHom.ofValCompat
    (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom
    (windowSubYSliceIso_val_compat p F ϖ n D' u' hu' u hu hp)

theorem windowSubVPreHom_toHom (hp : 1 < p) :
    (windowSubVPreHom p F ϖ n D' u' hu' u hu hp).toHom
      = (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).hom := rfl

theorem isIso_windowSubVPreHom_toHom (hp : 1 < p) :
    IsIso (windowSubVPreHom p F ϖ n D' u' hu' u hu hp).toHom := by
  rw [windowSubVPreHom_toHom p F ϖ n D' u' hu' u hu hp]
  exact (windowSubYSliceIso p F ϖ n D' u' hu' u hu hp).isIso_hom

noncomputable def windowSubVPreIso (hp : 1 < p) :
    (ValuationSpectrum.spaVObjTate (A := presheafValue D')).toVPreObj
      ≅ (yVPreObj p F ϖ).restrictOpen
          (windowSubOpen p F ϖ n D' u' hu' u hu) :=
  have := isIso_windowSubVPreHom_toHom p F ϖ n D' u' hu' u hu hp
  ValuationSpectrum.VPreHom.asIso (windowSubVPreHom p F ϖ n D' u' hu' u hu hp)

/-- **`hviso`** — the last hypothesis of `isAdicSpace_xVObj_of_windowVIso`. -/
theorem nonempty_windowSubVPreIso (hp : 1 < p) :
    Nonempty ((ValuationSpectrum.spaVObjTate (A := presheafValue D')).toVPreObj
      ≅ (yVPreObj p F ϖ).restrictOpen
          (windowSubOpen p F ϖ n D' u' hu' u hu)) :=
  ⟨windowSubVPreIso p F ϖ n D' u' hu' u hu hp⟩

end FarguesFontaine

end
