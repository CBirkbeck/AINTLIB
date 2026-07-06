import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Scheme-theoretic preimage of ideal sheaves is multiplicative

`(I * J).comap f = I.comap f * J.comap f` for ideal sheaves `I J` on `Y` and
`f : X ⟶ Y`. The scheme-theoretic preimage (`IdealSheafData.comap`, the kernel of the
first projection of the pulled-back closed subscheme) is affine-locally the extension
`Ideal.map` along the ring map, which is multiplicative.

Strategy (per the T-D6a-i design):
* `comap_ideal_top_of_isAffine`: over affine `X`, `Y` the top-value of `I.comap f` is
  `(I.ideal ⊤).map f.appTop` — the honest tensor computation
  (`Hom.ker_apply` + `pullbackSpecIso` + `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`).
* `comap_mul_of_isAffine`: `Ideal.map_mul` + the above.
* `comap_mul`: globalise over affine covers
  (`IdealSheafData.ext_of_iSup_eq_top` + comap-restriction compatibility).

Upstream candidate. Ticket: T-D6a-i (ModularCurves).
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Over affine schemes, the scheme-theoretic preimage of an ideal sheaf has top-value
the extension of the top-value: `(I.comap f).ideal ⊤ = (I.ideal ⊤).map f.appTop`.
The heart of `comap_mul`. -/
theorem comap_ideal_top_of_isAffine [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (hX : IsAffineOpen (⊤ : X.Opens))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (I.comap f).ideal ⟨⊤, hX⟩ =
      (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom := by
  have hker : (I.comap f).ideal ⟨⊤, hX⟩ =
      RingHom.ker ((Limits.pullback.fst f I.subschemeι).appTop).hom := by
    show ((Limits.pullback.fst f I.subschemeι).ker).ideal ⟨⊤, hX⟩ = _
    rw [ker_of_isAffine]
    simp
  rw [hker]
  refine le_antisymm ?_ ?_
  · -- the hard half: the kernel is at most the extension. Instead of computing the
    -- tensor product, map the competitor `Spec (Γ(X)/extension)` into the pullback
    -- and read off the kernel inclusion from the first projection.
    have hround : ∀ w : ↑Γ(X, ⊤),
        (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤)))).hom.hom
          ((X.isoSpec.inv.appTop).hom w) = w := by
      intro w
      have h1 : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
        rfl
      have h2 := congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) => g.hom w) h1
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        CommRingCat.hom_id, RingHom.coe_id, id_eq] at h2
      rw [show X.isoSpec.hom.appTop =
          (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤)))).hom from
        Scheme.toSpecΓ_appTop X] at h2
      exact h2
    set K := (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom with hK
    set ιX : Spec (.of (↑Γ(X, ⊤) ⧸ K)) ⟶ X :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ X.isoSpec.inv with hιX
    have hle : I.subschemeι.ker ≤ (ιX ≫ f).ker := by
      rw [ker_subschemeι, ker_of_isAffine]
      refine le_of_isAffine ?_
      rw [show (ofIdealTop (RingHom.ker ((ιX ≫ f).appTop).hom)).ideal
          ⟨⊤, isAffineOpen_top Y⟩ = RingHom.ker ((ιX ≫ f).appTop).hom by simp]
      intro x hx
      rw [RingHom.mem_ker]
      have hxK : (f.appTop).hom x ∈ K := Ideal.mem_map_of_mem _ hx
      have hval : ((ιX ≫ f).appTop).hom x =
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom
            ((X.isoSpec.inv.appTop).hom ((f.appTop).hom x)) := rfl
      rw [hval]
      have hnat1 := congrArg
        (fun g : Γ(Spec (CommRingCat.of (↑Γ(X, ⊤))), ⊤) ⟶
            CommRingCat.of (↑Γ(X, ⊤) ⧸ K) =>
          g.hom ((X.isoSpec.inv.appTop).hom ((f.appTop).hom x)))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
        CommRingCat.hom_ofHom] at hnat1
      rw [hround ((f.appTop).hom x)] at hnat1
      refine (Scheme.ΓSpecIso (CommRingCat.of
        (↑Γ(X, ⊤) ⧸ K))).commRingCatIsoToRingEquiv.injective ?_
      show (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤) ⧸ K))).hom.hom _ =
        (Scheme.ΓSpecIso (CommRingCat.of (↑Γ(X, ⊤) ⧸ K))).hom.hom 0
      rw [map_zero, hnat1,
        show Ideal.Quotient.mk K ((f.appTop).hom x) = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr hxK]
    set u : Spec (.of (↑Γ(X, ⊤) ⧸ K)) ⟶ Limits.pullback f I.subschemeι :=
      Limits.pullback.lift ιX (IsClosedImmersion.lift I.subschemeι (ιX ≫ f) hle)
        (IsClosedImmersion.lift_fac _ _ _).symm with hu
    have hufst : u ≫ Limits.pullback.fst f I.subschemeι = ιX :=
      Limits.pullback.lift_fst _ _ _
    intro z hz
    rw [RingHom.mem_ker] at hz
    have hzero : ((ιX).appTop).hom z = 0 := by
      rw [← hufst, Scheme.Hom.comp_appTop]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      rw [hz, map_zero]
    have hnatval := congrArg
      (fun g : Γ(Spec (CommRingCat.of (↑Γ(X, ⊤))), ⊤) ⟶
          CommRingCat.of (↑Γ(X, ⊤) ⧸ K) => g.hom ((X.isoSpec.inv.appTop).hom z))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at hnatval
    -- hnatval : ΓSpecIsoS.hom (SpecMapMk.appTop (isoSpecInv.appTop z)) =
    --           mk (ΓSpecIsoR.hom (isoSpecInv.appTop z))
    have hdecomp : ((ιX).appTop).hom z =
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop).hom
          ((X.isoSpec.inv.appTop).hom z) := rfl
    rw [hdecomp] at hzero
    rw [hzero, map_zero] at hnatval
    rw [hround z] at hnatval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hnatval.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hcomp : ((Limits.pullback.fst f I.subschemeι) ≫ f).appTop.hom x =
        ((Limits.pullback.snd f I.subschemeι) ≫ I.subschemeι).appTop.hom x := by
      rw [Limits.pullback.condition]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hcomp
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hcomp
    have hz : (I.subschemeι.appTop).hom x = 0 := by
      have happ := Scheme.IdealSheafData.subschemeι_app I ⟨⊤, isAffineOpen_top Y⟩
      have hval := congrArg (fun g => CommRingCat.Hom.hom g x) happ
      refine Eq.trans (rfl :
        (Scheme.Hom.appTop I.subschemeι).hom x =
        (Scheme.Hom.app I.subschemeι
          ↑(⟨⊤, isAffineOpen_top Y⟩ : Y.affineOpens)).hom x) ?_
      refine hval.trans ?_
      show (I.subschemeObjIso ⟨⊤, isAffineOpen_top Y⟩).inv.hom
        (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top Y⟩) x) = 0
      rw [show Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top Y⟩) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact map_zero _
    rw [hz, map_zero] at hcomp
    exact hcomp

end AlgebraicGeometry.Scheme.IdealSheafData
