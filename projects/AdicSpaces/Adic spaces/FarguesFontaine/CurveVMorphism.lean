/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveObject
import «Adic spaces».VRestrict

/-!
# The curve projection as a morphism of Wedhorn's category (P5-5a)

`xVPreObj.val x` is *defined* through a chosen fiber point `fiberPoint x`, so
making the quotient projection `π : 𝒴 → X` a morphism of `𝒱^pre` is not
formal: it needs the stalk valuation to be independent of that choice.  Two
points of a fiber differ by a Frobenius translate, so the independence is the
Frobenius equivariance of the projection's stalk maps — which in turn rests on
the fact that a `φ`-invariant section is invariant under *every* integral power
of `φ`, not just the generator recorded by `frobFixed`.

The file proves exactly that chain and packages `piYVPreHom`.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology
  Filter CategoryTheory Opposite Pointwise

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **The successor step for `φ`-invariance**: if the `m`-th transport of `s`
is its restriction along the stability equality, so is the `(m+1)`-st. -/
theorem limitFrobHom_eq_limitRestrict_succ
    {U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hstab : ∀ k : ℤ, frobOpens p F k U = U)
    {s : ↥(limitSections U)}
    (h1 : limitFrobHom p F 1 U s = limitRestrict (le_of_eq (hstab 1)) s)
    (m : ℤ)
    (hm : limitFrobHom p F m U s = limitRestrict (le_of_eq (hstab m)) s) :
    limitFrobHom p F (m + 1) U s
      = limitRestrict (le_of_eq (hstab (m + 1))) s := by
  have hA := limitFrobHom_add p F m 1 U s
  have hC := limitFrobHom_limitRestrict p F m (le_of_eq (hstab 1)) s
  have hcomp1 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (frobOpens_mono p F m (le_of_eq (hstab 1))) (le_of_eq (hstab m)))) s
  have hcomp2 := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (frobOpens_add p F m 1 U))
    ((frobOpens_mono p F m (le_of_eq (hstab 1))).trans (le_of_eq (hstab m))))) s
  calc limitFrobHom p F (m + 1) U s
      = limitRestrict (le_of_eq (frobOpens_add p F m 1 U))
          (limitFrobHom p F m (frobOpens p F 1 U)
            (limitFrobHom p F 1 U s)) := hA
    _ = limitRestrict (le_of_eq (frobOpens_add p F m 1 U))
          (limitFrobHom p F m (frobOpens p F 1 U)
            (limitRestrict (le_of_eq (hstab 1)) s)) := by rw [h1]
    _ = limitRestrict (le_of_eq (frobOpens_add p F m 1 U))
          (limitRestrict (frobOpens_mono p F m (le_of_eq (hstab 1)))
            (limitFrobHom p F m U s)) := by rw [hC]
    _ = limitRestrict (le_of_eq (frobOpens_add p F m 1 U))
          (limitRestrict (frobOpens_mono p F m (le_of_eq (hstab 1)))
            (limitRestrict (le_of_eq (hstab m)) s)) := by rw [hm]
    _ = limitRestrict (le_of_eq (frobOpens_add p F m 1 U))
          (limitRestrict ((frobOpens_mono p F m (le_of_eq (hstab 1))).trans
            (le_of_eq (hstab m))) s) := congrArg _ hcomp1
    _ = limitRestrict (le_of_eq (hstab (m + 1))) s := hcomp2

/-- **The predecessor step for `φ`-invariance**: transports are injective, so
invariance at `1 + k` pulls back to invariance at `k`. -/
theorem limitFrobHom_eq_limitRestrict_pred
    {U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hstab : ∀ k : ℤ, frobOpens p F k U = U)
    {s : ↥(limitSections U)}
    (h1 : limitFrobHom p F 1 U s = limitRestrict (le_of_eq (hstab 1)) s)
    (k : ℤ)
    (hm : limitFrobHom p F (1 + k) U s
      = limitRestrict (le_of_eq (hstab (1 + k))) s) :
    limitFrobHom p F k U s = limitRestrict (le_of_eq (hstab k)) s := by
  apply limitFrobHom_injective p F 1 (frobOpens p F k U)
  have hL := limitFrobHom_double p F 1 k U s
  have hR := limitFrobHom_limitRestrict p F 1 (le_of_eq (hstab k)) s
  have hcompL := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (frobOpens_add p F 1 k U).symm) (le_of_eq (hstab (1 + k))))) s
  have hcompR := congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (frobOpens_mono p F 1 (le_of_eq (hstab k))) (le_of_eq (hstab 1)))) s
  calc limitFrobHom p F 1 (frobOpens p F k U) (limitFrobHom p F k U s)
      = limitRestrict (le_of_eq (frobOpens_add p F 1 k U).symm)
          (limitFrobHom p F (1 + k) U s) := hL
    _ = limitRestrict (le_of_eq (frobOpens_add p F 1 k U).symm)
          (limitRestrict (le_of_eq (hstab (1 + k))) s) := by rw [hm]
    _ = limitRestrict ((le_of_eq (frobOpens_add p F 1 k U).symm).trans
          (le_of_eq (hstab (1 + k)))) s := hcompL
    _ = limitRestrict ((frobOpens_mono p F 1 (le_of_eq (hstab k))).trans
          (le_of_eq (hstab 1))) s := rfl
    _ = limitRestrict (frobOpens_mono p F 1 (le_of_eq (hstab k)))
          (limitRestrict (le_of_eq (hstab 1)) s) := hcompR.symm
    _ = limitRestrict (frobOpens_mono p F 1 (le_of_eq (hstab k)))
          (limitFrobHom p F 1 U s) := by rw [h1]
    _ = limitFrobHom p F 1 (frobOpens p F k U)
          (limitRestrict (le_of_eq (hstab k)) s) := hR.symm

/-- The predecessor step, index-flexible form. -/
theorem limitFrobHom_eq_limitRestrict_pred'
    {U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hstab : ∀ k : ℤ, frobOpens p F k U = U)
    {s : ↥(limitSections U)}
    (h1 : limitFrobHom p F 1 U s = limitRestrict (le_of_eq (hstab 1)) s)
    (k m : ℤ) (hkm : 1 + k = m)
    (hm : limitFrobHom p F m U s = limitRestrict (le_of_eq (hstab m)) s) :
    limitFrobHom p F k U s = limitRestrict (le_of_eq (hstab k)) s := by
  subst hkm
  exact limitFrobHom_eq_limitRestrict_pred p F hstab h1 k hm

/-- **Invariance under one Frobenius transport forces invariance under all of
them**, for a totally Frobenius-stable open. -/
theorem limitFrobHom_eq_limitRestrict_of_one
    {U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hstab : ∀ k : ℤ, frobOpens p F k U = U)
    {s : ↥(limitSections U)}
    (h1 : limitFrobHom p F 1 U s = limitRestrict (le_of_eq (hstab 1)) s)
    (k : ℤ) :
    limitFrobHom p F k U s = limitRestrict (le_of_eq (hstab k)) s := by
  induction k using Int.induction_on with
  | zero => exact limitFrobHom_zero p F U s
  | succ i ih => exact limitFrobHom_eq_limitRestrict_succ p F hstab h1 (i : ℤ) ih
  | pred i ih =>
      exact limitFrobHom_eq_limitRestrict_pred' p F hstab h1
        (-(i : ℤ) - 1) (-(i : ℤ)) (by ring) ih

/-- **The `φ`-fixed sections are fixed by every integral power of the
Frobenius transport**: the `k`-th transport of an invariant section is its
restriction along the stability equality `frobOpens p F k W = W`. -/
theorem frobFixed_zpow (V : Opens (Curve p F ϖ))
    (t : ↥(frobFixed p F ϖ V)) (k : ℤ) :
    limitFrobHom p F k ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) t.1
      = limitRestrict (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ k V))
          t.1 :=
  limitFrobHom_eq_limitRestrict_of_one p F
    (fun j => frobOpens_yFunctor_curvePreimage p F ϖ j V) t.2 k

/-- **Two points of `𝒴` over the same curve point differ by a Frobenius
translate.** -/
theorem exists_yFrob_eq_of_yTopToCurve_eq (y₁ y₂ : ↥(yTop p F ϖ))
    (h : yTopToCurve p F ϖ y₁ = yTopToCurve p F ϖ y₂) :
    ∃ k : ℤ, y₁ = yFrobTop p F ϖ k y₂ := by
  have hrel : yTopToY p F ϖ y₁
      ∈ MulAction.orbit (Multiplicative ℤ) (yTopToY p F ϖ y₂) :=
    MulAction.orbitRel_apply.mp (Quotient.eq''.mp h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  refine ⟨-(Multiplicative.toAdd g), (yTopToY_bijective p F ϖ).1 ?_⟩
  rw [yTopToY_yFrobTop p F ϖ (-(Multiplicative.toAdd g)) y₂, neg_neg,
    ofAdd_toAdd]
  exact hg.symm

/-- The fiber point lies in the saturated preimage of any curve open
containing the point. -/
theorem fiberPoint_mem_curvePreimage {x : Curve p F ϖ}
    {V : Opens (Curve p F ϖ)} (hx : x ∈ V) :
    fiberPoint p F ϖ x ∈ curvePreimage p F ϖ V := by
  show yTopToCurve p F ϖ (fiberPoint p F ϖ x) ∈ (V : Set (Curve p F ϖ))
  rw [yTopToCurve_fiberPoint p F ϖ x]
  exact hx

/-- **The curve stalk comparison on germs**: the comparison carries the germ
of an invariant section to the germ of its underlying `𝒴`-section at the
chosen fiber point. -/
theorem xStalkEquiv_germ (x : Curve p F ϖ) (V : Opens (Curve p F ϖ))
    (hx : x ∈ V) (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))) :
    (xStalkEquiv p F ϖ x)
        ((curveSpace p F ϖ).ringPresheaf.germ V x hx t)
      = (yPresheafedSpace p F ϖ).ringPresheaf.germ
          (curvePreimage p F ϖ V) (fiberPoint p F ϖ x)
          (fiberPoint_mem_curvePreimage p F ϖ hx)
          (piComponent p F ϖ V t) := by
  have hcongr : (ConcreteCategory.hom
      ((curveSpace p F ϖ).ringPresheaf.stalkCongr
        (Inseparable.of_eq (yTopToCurve_fiberPoint p F ϖ x).symm)).hom)
      ((curveSpace p F ϖ).ringPresheaf.germ V x hx t)
      = (curveSpace p F ϖ).ringPresheaf.germ V
          (yTopToCurve p F ϖ (fiberPoint p F ϖ x))
          (by rw [yTopToCurve_fiberPoint p F ϖ x]; exact hx) t :=
    TopCat.Presheaf.germ_stalkSpecializes_apply
      ((curveSpace p F ϖ).ringPresheaf) hx
      (Inseparable.of_eq (yTopToCurve_fiberPoint p F ϖ x).symm).ge t
  show (ConcreteCategory.hom (ValuationSpectrum.ringStalkMap
      (piYHom p F ϖ) (fiberPoint p F ϖ x)))
      ((ConcreteCategory.hom
        ((curveSpace p F ϖ).ringPresheaf.stalkCongr
          (Inseparable.of_eq (yTopToCurve_fiberPoint p F ϖ x).symm)).hom)
        ((curveSpace p F ϖ).ringPresheaf.germ V x hx t)) = _
  rw [hcongr]
  exact ringStalkMap_piYHom_germ p F ϖ (fiberPoint p F ϖ x) V _ t

/-- **The `k`-th Frobenius transport of an invariant section is its
restriction** (the `𝒴`-level form). -/
theorem yLimitFrobHom_piComponent (k : ℤ) (V : Opens (Curve p F ϖ))
    (t : ↥(frobFixed p F ϖ V)) :
    yLimitFrobHom p F ϖ k (curvePreimage p F ϖ V) (piComponent p F ϖ V t)
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE
          (le_of_eq (map_yFrobTop_curvePreimage p F ϖ k V)))))
          (piComponent p F ϖ V t) := by
  rw [← limitFrobHom_bridge p F ϖ k (curvePreimage p F ϖ V)
    (piComponent p F ϖ V t)]
  rw [show (piComponent p F ϖ V t) = t.1 from rfl]
  rw [frobFixed_zpow p F ϖ V t k]
  exact congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (yFunctor_frobOpens p F ϖ k (curvePreimage p F ϖ V)).symm)
    (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ k V)))) t.1

/-- **The projection stalk map is Frobenius-invariant** (L4): pulling an
invariant germ back along `φ^k` and then along `π` is the same as pulling it
back along `π` directly. -/
theorem ringStalkMap_yFrob_piYHom_germ (k : ℤ) (y : ↥(yTop p F ϖ))
    (V : Opens (Curve p F ϖ))
    (hy : yFrobTop p F ϖ k y ∈ curvePreimage p F ϖ V)
    (hy' : y ∈ curvePreimage p F ϖ V)
    (t : ↥(frobFixed p F ϖ V)) :
    (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) y).hom
        ((yPresheafedSpace p F ϖ).ringPresheaf.germ
          (curvePreimage p F ϖ V) (yFrobTop p F ϖ k y) hy
          (piComponent p F ϖ V t))
      = (yPresheafedSpace p F ϖ).ringPresheaf.germ
          (curvePreimage p F ϖ V) y hy' (piComponent p F ϖ V t) := by
  rw [ringStalkMap_yFrob_germ p F ϖ k y (curvePreimage p F ϖ V) hy
    (piComponent p F ϖ V t)]
  rw [yLimitFrobHom_piComponent p F ϖ k V t]
  exact yGerm_limitRestrict p F ϖ
    (le_of_eq (map_yFrobTop_curvePreimage p F ϖ k V)) hy
    (piComponent p F ϖ V t)

/-- Saturated preimages are Frobenius-stable, pointwise. -/
theorem mem_curvePreimage_yFrob (k : ℤ) (y : ↥(yTop p F ϖ))
    {V : Opens (Curve p F ϖ)} (hy : y ∈ curvePreimage p F ϖ V) :
    yFrobTop p F ϖ k y ∈ curvePreimage p F ϖ V := by
  show yTopToCurve p F ϖ (yFrobTop p F ϖ k y) ∈ (V : Set (Curve p F ϖ))
  rw [yTopToCurve_yFrobTop p F ϖ k y]
  exact hy

/-- **L5, the abstract form**: whatever comparison `φ` realises the curve stalk
as the `𝒴`-stalk at a Frobenius translate `y₀ = φ^k y` and computes on germs as
the underlying-section germ, the transported `𝒴`-stalk valuation is the pullback
of `y`'s along the projection. -/
theorem piY_val_compat_aux (y y₀ : ↥(yTop p F ϖ)) (k : ℤ)
    (hk : y₀ = yFrobTop p F ϖ k y)
    (φ : ToType ((curveSpace p F ϖ).ringStalk (yTopToCurve p F ϖ y))
          →+* ToType ((yPresheafedSpace p F ϖ).ringStalk y₀))
    (hφ : ∀ (V : Opens (Curve p F ϖ)) (hxV : yTopToCurve p F ϖ y ∈ V)
      (hyV : y₀ ∈ curvePreimage p F ϖ V)
      (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))),
      φ ((curveSpace p F ϖ).ringPresheaf.germ V (yTopToCurve p F ϖ y) hxV t)
        = (yPresheafedSpace p F ϖ).ringPresheaf.germ
            (curvePreimage p F ϖ V) y₀ hyV (piComponent p F ϖ V t)) :
    comap φ (yStalkValue p F ϖ y₀)
      = comap (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom'
          (yStalkValue p F ϖ y) := by
  subst hk
  have hfrob : yStalkValue p F ϖ (yFrobTop p F ϖ k y)
      = comap (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) y).hom'
          (yStalkValue p F ϖ y) := (yFrobVPreHom p F ϖ k).val_compat y
  have hring : ((ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) y).hom').comp φ
      = (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom' := by
    refine RingHom.ext fun a => ?_
    obtain ⟨V, hxV, t, rfl⟩ :=
      ((curveSpace p F ϖ).ringPresheaf).exists_germ_eq a
    have hyV : yFrobTop p F ϖ k y ∈ curvePreimage p F ϖ V :=
      mem_curvePreimage_yFrob p F ϖ k y hxV
    show (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) y).hom
        (φ ((curveSpace p F ϖ).ringPresheaf.germ V
          (yTopToCurve p F ϖ y) hxV t)) = _
    rw [hφ V hxV hyV t]
    rw [ringStalkMap_yFrob_piYHom_germ p F ϖ k y V hyV hxV t]
    exact (ringStalkMap_piYHom_germ p F ϖ y V hxV t).symm
  rw [hfrob, ← hring]
  exact (congr_fun (comap_comp φ
    ((ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) y).hom'))
    (yStalkValue p F ϖ y)).symm

/-- **L5**: the projection's valuation compatibility, at EVERY point of `𝒴`
(not just the chosen fiber points). -/
theorem piY_val_compat (y : ↥(yTop p F ϖ)) :
    (xVPreObj p F ϖ).val
        (ConcreteCategory.hom (piYHom p F ϖ).base y)
      = comap (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom'
          ((yVPreObj p F ϖ).val y) := by
  obtain ⟨k, hk⟩ := exists_yFrob_eq_of_yTopToCurve_eq p F ϖ
    (fiberPoint p F ϖ (yTopToCurve p F ϖ y)) y
    (yTopToCurve_fiberPoint p F ϖ (yTopToCurve p F ϖ y))
  exact piY_val_compat_aux p F ϖ y _ k hk
    ((xStalkEquiv p F ϖ (yTopToCurve p F ϖ y) : _ →+* _))
    (fun V hxV _ t => xStalkEquiv_germ p F ϖ (yTopToCurve p F ϖ y) V hxV t)

/-- **The curve projection as a morphism of `𝒱^pre`** (P5-5a). -/
noncomputable def piYVPreHom :
    ValuationSpectrum.VPreHom (yVPreObj p F ϖ) (xVPreObj p F ϖ) where
  toHom := piYHom p F ϖ
  isLocalHom_stalkMap := fun y =>
    ValuationSpectrum.isLocalHom_of_val_comap
      ((xVPreObj p F ϖ).isLocalRing_stalk _) ((yVPreObj p F ϖ).isLocalRing_stalk y)
      _ _ _ (piY_val_compat p F ϖ y)
      ((xVPreObj p F ϖ).val_supp _) ((yVPreObj p F ϖ).val_supp y)
  val_compat := fun y => piY_val_compat p F ϖ y


/-! ### The quotient leg (P5-5b)

`π` restricted to an open `V` of `𝒴` lands in the open image `xImage V`, so
`VPreHom.corestrict` turns it into a `𝒱^pre`-morphism `𝒴|_V ⟶ X|_{π V}`.
No wandering hypothesis is needed here — that only enters when one asks for
the morphism to be an isomorphism. -/

/-- The projection restricted to an open of `𝒴`. -/
noncomputable def yRestrictToCurve (V : Opens ↥(yTop p F ϖ)) :
    ValuationSpectrum.VPreHom ((yVPreObj p F ϖ).restrictOpen V)
      (xVPreObj p F ϖ) :=
  (ValuationSpectrum.VPreHom.ofRestrictOpen
    (X := yVPreObj p F ϖ) V).comp (piYVPreHom p F ϖ)

/-- The restricted projection lands in the open image. -/
theorem range_yRestrictToCurve (V : Opens ↥(yTop p F ϖ)) :
    Set.range (ConcreteCategory.hom (yRestrictToCurve p F ϖ V).toHom.base)
      ⊆ ((xImage p F ϖ V : Opens (Curve p F ϖ)) : Set (Curve p F ϖ)) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨v.1, v.2, rfl⟩

/-- **The quotient leg** (P5-5b): `𝒴|_V ⟶ X|_{π V}` as a morphism of
`𝒱^pre`. -/
noncomputable def quotientLegVPreHom (V : Opens ↥(yTop p F ϖ)) :
    ValuationSpectrum.VPreHom ((yVPreObj p F ϖ).restrictOpen V)
      ((xVPreObj p F ϖ).restrictOpen (xImage p F ϖ V)) :=
  ValuationSpectrum.VPreHom.corestrict (yRestrictToCurve p F ϖ V)
    (xImage p F ϖ V) (range_yRestrictToCurve p F ϖ V)

end FarguesFontaine

end
