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
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
