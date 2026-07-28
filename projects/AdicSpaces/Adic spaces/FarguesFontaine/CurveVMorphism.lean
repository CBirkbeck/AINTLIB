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


/-! ### The section comparison of the quotient leg (P5-5c)

For a *wandering* open `W` of `𝒴` — all `φ^k W` disjoint from `W` for `k ≠ 0` —
restriction identifies the `φ`-invariant sections over `xImage W` with the
plain sections over `W`.  Bijectivity is the already-proven separation and
gluing; what needs an argument is that the inverse is **continuous**: a
continuous bijective ring hom need not be a topological isomorphism.  The tool
is the `isEmbedding` field of `IsLimitSheafOn`, which says the saturation's
topology is induced by restriction to the translates — and each translate
component of the glue is a Frobenius transport, hence continuous. -/

/-- An open sits inside the saturated preimage of its image. -/
theorem le_curvePreimage_xImage (W : Opens ↥(yTop p F ϖ)) :
    W ≤ curvePreimage p F ϖ (xImage p F ϖ W) :=
  fun y hy => ⟨y, hy, rfl⟩

/-- The `yFunctor`-image form of the previous inclusion. -/
theorem yFunctor_le_curvePreimage_xImage (W : Opens ↥(yTop p F ϖ)) :
    (yFunctor p F ϖ).obj W
      ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)) :=
  leOfHom ((yFunctor p F ϖ).map (homOfLE (le_curvePreimage_xImage p F ϖ W)))

/-- **The section comparison of the quotient leg**: an invariant section over
`xImage W` restricted to `W`. -/
noncomputable def curveSectionRestrict (W : Opens ↥(yTop p F ϖ)) :
    ↥(frobFixed p F ϖ (xImage p F ϖ W))
      →+* ↥(limitSections ((yFunctor p F ϖ).obj W)) :=
  (limitRestrict (yFunctor_le_curvePreimage_xImage p F ϖ W)).comp
    (frobFixed p F ϖ (xImage p F ϖ W)).subtype

/-- The section comparison is continuous — it is a `limitRestrict` after the subring
inclusion. The content of P5-5c is the continuity of the INVERSE, not of this map. -/
theorem curveSectionRestrict_continuous (W : Opens ↥(yTop p F ϖ)) :
    Continuous (curveSectionRestrict p F ϖ W) :=
  (limitRestrict_continuous _).comp continuous_subtype_val

/-- The zero translate factors through `W`. -/
theorem translate_zero_le_W (W : Opens ↥(yTop p F ϖ)) :
    (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ 0)).obj W)
      ≤ (yFunctor p F ϖ).obj W :=
  yFunctor_translate_zero_le p F ϖ W

/-- Restricting to `W` and then to the zero translate is restricting to the
zero translate. -/
theorem restrict_zero_factor (W : Opens ↥(yTop p F ϖ))
    (g : ↥(limitSections ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W))))) :
    limitRestrict (yFunctor_translate_le p F ϖ W 0) g
      = limitRestrict (translate_zero_le_W p F ϖ W)
          (limitRestrict (yFunctor_le_curvePreimage_xImage p F ϖ W) g) :=
  (congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (translate_zero_le_W p F ϖ W)
    (yFunctor_le_curvePreimage_xImage p F ϖ W))) g).symm

/-- Restriction along the zero-translate equality is injective. -/
theorem restrict_zero_injective (W : Opens ↥(yTop p F ϖ)) :
    Function.Injective (limitRestrict (translate_zero_le_W p F ϖ W)) := by
  intro a b h
  have hcomp := fun z => congr_fun (congrArg DFunLike.coe (limitRestrict_comp
    (le_of_eq (congrArg (yFunctor p F ϖ).obj
      (map_yFrobTop_zero p F ϖ W)).symm)
    (translate_zero_le_W p F ϖ W))) z
  have hid := fun z => congr_fun (congrArg DFunLike.coe
    (limitRestrict_id ((yFunctor p F ϖ).obj W))) z
  have h2 := congrArg (limitRestrict (le_of_eq (congrArg (yFunctor p F ϖ).obj
    (map_yFrobTop_zero p F ϖ W)).symm)) h
  calc a = limitRestrict (le_of_eq (congrArg (yFunctor p F ϖ).obj
          (map_yFrobTop_zero p F ϖ W)).symm)
        (limitRestrict (translate_zero_le_W p F ϖ W) a) :=
        ((hcomp a).trans (hid a)).symm
    _ = limitRestrict (le_of_eq (congrArg (yFunctor p F ϖ).obj
          (map_yFrobTop_zero p F ϖ W)).symm)
        (limitRestrict (translate_zero_le_W p F ϖ W) b) := h2
    _ = b := (hcomp b).trans (hid b)

/-- **Injectivity of the section comparison.** The wandering hypothesis is
carried for uniformity with the surjectivity half but is not used: separation of
invariant sections holds over any open. -/
theorem curveSectionRestrict_injective (W : Opens ↥(yTop p F ϖ))
    (_hdis : ∀ k : ℤ, k ≠ 0 →
      Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
          : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
        ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))) :
    Function.Injective (curveSectionRestrict p F ϖ W) := by
  intro t t' h
  refine invariant_sections_eq_of_zero_piece p F ϖ W t t' ?_
  rw [restrict_zero_factor p F ϖ W t.1, restrict_zero_factor p F ϖ W t'.1]
  exact congrArg _ h


variable (W : Opens ↥(yTop p F ϖ))
  (hdis : ∀ k : ℤ, k ≠ 0 →
    Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj W
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
      ((W : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)))

/-- The glued extension of a section over a wandering open. -/
noncomputable def glueInvRaw (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ↥(limitSections ((yFunctor p F ϖ).obj
      (curvePreimage p F ϖ (xImage p F ϖ W)))) :=
  (exists_glue_extending p F ϖ W hdis s).choose

/-- Every translate-component of the glue is the corresponding Frobenius transport of
`s`. This is what makes the glue continuous: each component is continuous in `s`. -/
theorem glueInvRaw_pieces (s : ↥(limitSections ((yFunctor p F ϖ).obj W)))
    (k : ℤ) :
    limitRestrict (yFunctor_translate_le p F ϖ W k) (glueInvRaw p F ϖ W hdis s)
      = translateFam p F ϖ W s k :=
  (exists_glue_extending p F ϖ W hdis s).choose_spec.1 k

/-- The glued section is `φ`-invariant, so it really is a section of the curve's
structure presheaf. -/
theorem glueInvRaw_invariant (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    glueInvRaw p F ϖ W hdis s ∈ frobFixed p F ϖ (xImage p F ϖ W) :=
  glue_invariant p F ϖ W s _ (glueInvRaw_pieces p F ϖ W hdis s)

/-- The glued extension, as an invariant section. -/
noncomputable def glueInv (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ↥(frobFixed p F ϖ (xImage p F ϖ W)) :=
  ⟨glueInvRaw p F ϖ W hdis s, glueInvRaw_invariant p F ϖ W hdis s⟩

/-- The glue is a right inverse of the section comparison: restricting it back to `W`
recovers the original section. -/
theorem curveSectionRestrict_glueInv
    (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    curveSectionRestrict p F ϖ W (glueInv p F ϖ W hdis s) = s := by
  refine restrict_zero_injective p F ϖ W ?_
  have h0 := glueInvRaw_pieces p F ϖ W hdis s 0
  rw [translateFam_zero p F ϖ W s] at h0
  rw [restrict_zero_factor p F ϖ W (glueInvRaw p F ϖ W hdis s)] at h0
  exact h0

/-- The cover of the saturation by the translates. -/
theorem saturation_cover :
    (((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))
      : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ m : ULift ℤ, (SetLike.coe ((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ m.down)).obj W))) := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := hv
  rw [show curvePreimage p F ϖ (xImage p F ϖ W)
      = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W from
    curvePreimage_xImage p F ϖ W] at hy
  rw [Opens.coe_iSup] at hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨⟨k⟩, ⟨y, hk, rfl⟩⟩

/-- **The glued extension is continuous** — the sheaf's `isEmbedding` field
says the saturation's topology is induced by restriction to the translates,
and each translate-component of the glue is a Frobenius transport. -/
theorem translateFam_continuous (k : ℤ) :
    Continuous (fun s : ↥(limitSections ((yFunctor p F ϖ).obj W)) =>
      translateFam p F ϖ W s k) := by
  show Continuous (fun s : ↥(limitSections ((yFunctor p F ϖ).obj W)) =>
    limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ k W).symm)
      (limitFrobHom p F k ((yFunctor p F ϖ).obj W) s))
  exact (limitRestrict_continuous
      (le_of_eq (yFunctor_frobOpens p F ϖ k W).symm)).comp
    (limitFrobHom_continuous p F k ((yFunctor p F ϖ).obj W))

/-- **The glue is continuous.** The sheaf's `isEmbedding` field says the saturation's
topology is induced by restriction to the translates, and by `glueInvRaw_pieces`
each such component is a Frobenius transport of `s`, hence continuous in `s`. -/
theorem glueInvRaw_continuous : Continuous (glueInvRaw p F ϖ W hdis) := by
  have hcont : Continuous (fun (s : ↥(limitSections ((yFunctor p F ϖ).obj W)))
      (m : ULift ℤ) => translateFam p F ϖ W s m.down) :=
    continuous_pi fun m => translateFam_continuous p F ϖ W m.down
  have hemb := (isLimitSheafOn_Y p F ϖ).isEmbedding
    (V := (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))
    (yFunctor_trace p F ϖ _)
    (ι := ULift ℤ)
    (U := fun m : ULift ℤ => (yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ m.down)).obj W))
    (fun m => yFunctor_translate_le p F ϖ W m.down)
    (saturation_cover p F ϖ W)
  refine hemb.toIsInducing.continuous_iff.mpr (hcont.congr fun s => ?_)
  exact (funext fun m : ULift ℤ =>
    glueInvRaw_pieces p F ϖ W hdis s m.down).symm

/-- Continuity of the glue, as a map into the invariant sections (the subring carries
the induced topology). -/
theorem glueInv_continuous : Continuous (glueInv p F ϖ W hdis) :=
  continuous_induced_rng.mpr (glueInvRaw_continuous p F ϖ W hdis)

include hdis in
/-- **The section comparison of the quotient leg is bijective.** -/
theorem curveSectionRestrict_bijective :
    Function.Bijective (curveSectionRestrict p F ϖ W) :=
  ⟨curveSectionRestrict_injective p F ϖ W hdis,
    fun s => ⟨glueInv p F ϖ W hdis s,
      curveSectionRestrict_glueInv p F ϖ W hdis s⟩⟩

include hdis in
/-- **The section comparison as a ring equivalence.** -/
noncomputable def curveSectionEquiv :
    ↥(frobFixed p F ϖ (xImage p F ϖ W))
      ≃+* ↥(limitSections ((yFunctor p F ϖ).obj W)) :=
  RingEquiv.ofBijective (curveSectionRestrict p F ϖ W)
    (curveSectionRestrict_bijective p F ϖ W hdis)

/-- The equivalence's inverse IS the glue — the identification that transfers
`glueInv_continuous` to `curveSectionEquiv.symm`. -/
theorem curveSectionEquiv_symm_eq :
    ((curveSectionEquiv p F ϖ W hdis).symm : _ → _)
      = glueInv p F ϖ W hdis := by
  funext s
  refine (curveSectionEquiv p F ϖ W hdis).injective ?_
  rw [RingEquiv.apply_symm_apply]
  exact (curveSectionRestrict_glueInv p F ϖ W hdis s).symm

/-- **The inverse of the section comparison is continuous** — review finding
(3), second half: the bijection is a homeomorphism, not merely a bijection. -/
theorem curveSectionEquiv_symm_continuous :
    Continuous ((curveSectionEquiv p F ϖ W hdis).symm) := by
  rw [show ((curveSectionEquiv p F ϖ W hdis).symm : _ → _)
      = glueInv p F ϖ W hdis from curveSectionEquiv_symm_eq p F ϖ W hdis]
  exact glueInv_continuous p F ϖ W hdis


/-! ### The section map of the quotient leg (P5-5d)

Both formulas below are `rfl`: `PresheafedSpace.comp_c_app` gives
`piYHom.c.app ≫ pushforward (ofRestrict.c.app)`, `ofRestrict.c.app` is
`presheaf.map (counit).op`, and `yPresheafedSpace.presheaf = (yFunctor).op ⋙
structurePresheaf` turns that into exactly a `limitRestrict`; the `≤`-witness
mismatch is absorbed by definitional proof irrelevance. -/

variable (W' : Opens (Curve p F ϖ))

/-- The `𝒴`-image of the slice `{y ∈ V : π y ∈ W}` sits inside the saturated
preimage of `W`. -/
theorem legOpen_le_curvePreimage (V : Opens ↥(yTop p F ϖ)) :
    (ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj
        ((Opens.map (yRestrictToCurve p F ϖ V).toHom.base).obj W')
      ≤ curvePreimage p F ϖ W' := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- **The section map of the quotient leg**: `c` at `W` sends an invariant
section to its underlying `𝒴`-section, restricted to the slice
`{y ∈ V : π y ∈ W}`. -/
theorem yRestrictToCurve_c_app_apply (V : Opens ↥(yTop p F ϖ))
    (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op W'))) :
    (ConcreteCategory.hom ((yRestrictToCurve p F ϖ V).toHom.c.app (op W'))) t
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map
          (homOfLE (legOpen_le_curvePreimage p F ϖ W' V))))
          (piComponent p F ϖ W' t) := rfl

/-- **The slice is the expected intersection**: the source open of the quotient
leg's `c` at `W` is `V ⊓ π⁻¹ W`. -/
theorem legOpen_eq (V : Opens ↥(yTop p F ϖ)) :
    (ValuationSpectrum.restrictOpenFunctor (yVPreObj p F ϖ) V).obj
        ((Opens.map (yRestrictToCurve p F ϖ V).toHom.base).obj W')
      = V ⊓ curvePreimage p F ϖ W' := by
  refine Opens.ext (Set.ext fun v => ⟨?_, ?_⟩)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hv, hw⟩
    exact ⟨⟨v, hv⟩, hw, rfl⟩

/-- The section map of the quotient leg, with the slice spelled `V ⊓ π⁻¹ W`. -/
theorem yRestrictToCurve_c_app_apply_inf (V : Opens ↥(yTop p F ϖ))
    (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op W'))) :
    limitRestrict (le_of_eq (congrArg (yFunctor p F ϖ).obj
          (legOpen_eq p F ϖ W' V).symm))
        ((ConcreteCategory.hom
          ((yRestrictToCurve p F ϖ V).toHom.c.app (op W'))) t)
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE
          (inf_le_right : V ⊓ curvePreimage p F ϖ W' ≤ curvePreimage p F ϖ W'))))
          (piComponent p F ϖ W' t) := rfl

end FarguesFontaine

end
