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
  · -- the tensor half: the kernel of the pulled-back inclusion is the extension
    sorry
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
