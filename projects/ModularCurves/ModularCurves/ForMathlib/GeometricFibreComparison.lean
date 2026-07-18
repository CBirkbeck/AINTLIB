/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelRecord

/-!
# [T-B6′-IFACE] — the geometric-fibre point comparison (scheme ↔ affine), as a group iso

The **geometric-fibre point comparison** for the KM 2.3 box **T-B6**, consumed by
* STREAM-Y1's atlas leaves **ii** (order ⟹ unit) and **vi** (`P₀` nowhere order ≤ 3), and
* the **BB-DIFF** étale cascade's leaf **L-B** (`E[N]_{k̄} ≅ (ℤ/N)²`) — recorded v10.38 as
  `BB-DIFF ⟸ T-B6′`.

**T-B6 board spec** (verbatim, `decomposition-km2.3-b5d.md` §L-B, KM 2.3.1 proof p. 74):
> "the scheme fibre `E_{k̄}` ↔ HasseWeil `WeierstrassCurve k̄` comparison (template:
> `WeilPairing/GaloisEquivariance.lean`'s `E.Point t ↔ W.toAffine.Point` identification), which
> must be built **non-circularly** (the current T-B6 routes through `Torsionπ.etale`)."
and (`decomposition-2026-07-05-phase1.md`, B4): "fibre comparison `E[N] ×_S Spec k̄ ≅ (ℤ/N)²`".

The **set** bijection `projModelPointsEquiv : SpecPoints (projModel W) (projModelπ W) K ≃
(W.baseChange K).toAffine.Point` is proven (T-W7.0f), and the `E.Point ↔ SpecPoints` bridge
(`pointSpecPointsEquiv`) is ungated geometry. As of the v10.123-CASCADE the remaining T-B6
content — the fibrewise group-law intertwining `map_add'` — is **proven** too (the zero pin makes
`E`'s geometry the model record's, rigidity forces the two additions to agree on `k`-points, and
the C6 dictionary `mulModelHom_specPoints` computes the model addition as mathlib's affine
`Point.add`). So `geomFibrePointAddEquiv` is a genuine, **axiom-clean** group isomorphism onto
mathlib's affine `Point` group — the `[T-B6′]` pin is **discharged** (no `sorry`; axioms
`{propext, Classical.choice, Quot.sound}`).

## Main declarations

* `EllipticCurve.pointSpecPointsEquiv` — the ungated `E.Point (geomPoint) ≃ SpecPoints` bridge.
* `EllipticCurve.geomFibrePointAddEquiv` — **[T-B6′-IFACE]** the scheme-fibre ↔ affine group `≃+`,
  fully proven (axiom-clean).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

/-- The tautological geometric point `Spec k ⟶ Spec B` (the structure map of the `B`-algebra
`k`); every geometric point of `Spec B` over a field is of this form. -/
noncomputable def geomPoint (B : Type u) [CommRing B] (k : Type u) [Field k] [Algebra B k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B k))

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) [W.IsElliptic]
  (E : EllipticCurve (Spec (CommRingCat.of B))) (hE : E.E = projModel W)
  (hπ : E.π = eqToHom hE ≫ projModelπ W)
  (hz : E.zero ≫ eqToHom hE = projModelZero W)
  (k : Type u) [Field k] [Algebra B k] [DecidableEq k] [(W.baseChange k).IsElliptic]

/-- Ungated geometry: `E`-points over the tautological geometric point are exactly the
`k`-points of the projective model `projModel W`, by transporting the total space along `hE`. -/
noncomputable def pointSpecPointsEquiv :
    E.Point (geomPoint B k) ≃ SpecPoints (projModel W) (projModelπ W) k where
  toFun P := ⟨P.1 ≫ eqToHom hE, by
    rw [Category.assoc, ← hπ]; exact P.2⟩
  invFun g := ⟨g.1 ≫ eqToHom hE.symm, by
    have hπ' : eqToHom hE.symm ≫ E.π = projModelπ W := by rw [hπ, ← Category.assoc]; simp
    rw [Category.assoc, hπ']; exact g.2⟩
  left_inv P := by
    apply Subtype.ext
    show (P.1 ≫ eqToHom hE) ≫ eqToHom hE.symm = P.1
    simp [Category.assoc]
  right_inv g := by
    apply Subtype.ext
    show (g.1 ≫ eqToHom hE.symm) ≫ eqToHom hE = g.1
    simp [Category.assoc]

/-- **[T-B6′-IFACE, FILLED]** The geometric-fibre point comparison as a **group**
isomorphism: the scheme fibre points `E.Point (geomPoint)` are `≃+` to the affine
Weierstrass points `(W.baseChange k).toAffine.Point`. The underlying bijection is the proven
`pointSpecPointsEquiv ≫ projModelPointsEquiv`.

`map_add'` (the fibrewise group-law intertwining, the T-B6 content) is by the
v10.123-CASCADE route: the zero pin `hz` (B2 EVENT #3) makes `E`'s geometry equal to that of
the mulOver-based model record `modelEllipticCurve W` (T-G4 laws, `ModelRecord.lean`), the
rigidity driver `point_add_val_of_geom_eq` (through `Point.baseChangeEquiv` +
`abelEnrichment_unique_of_isLocallyNoetherian` over the locally noetherian `Spec k`) forces
the two additions to agree on `k`-points, and the C6 dictionary `mulModelHom_specPoints`
computes the model addition as mathlib's affine `Point.add`. -/
noncomputable def geomFibrePointAddEquiv :
    E.Point (geomPoint B k) ≃+ (W.baseChange k).toAffine.Point where
  toEquiv := (pointSpecPointsEquiv W E hE hπ k).trans (projModelPointsEquiv W k)
  map_add' P Q := by
    have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
    -- the geometry of `E` is the model geometry: hE/hπ/hz pin every data field
    have hgeom : E.toEllipticCurveGeom = (modelEllipticCurve W).toEllipticCurveGeom :=
      EllipticCurveGeom.ext_of_eqToHom hE hπ hz
    -- the model-record images of `P` and `Q`
    refine Eq.trans (congrArg (projModelPointsEquiv W k) (Subtype.ext ?_))
      (mulModelHom_specPoints W k
        (pointSpecPointsEquiv W E hE hπ k P) (pointSpecPointsEquiv W E hE hπ k Q))
    show (P + Q).1 ≫ eqToHom hE = _
    exact (point_add_val_of_geom_eq hgeom P Q
        ⟨P.1 ≫ eqToHom hE,
          (Category.assoc _ _ _).trans ((congrArg (P.1 ≫ ·) hπ.symm).trans P.2)⟩
        ⟨Q.1 ≫ eqToHom hE,
          (Category.assoc _ _ _).trans ((congrArg (Q.1 ≫ ·) hπ.symm).trans Q.2)⟩
        hE rfl rfl).trans
      (modelEllipticCurve_point_add_val W _ _)

omit [(W.baseChange k).IsElliptic] in
@[simp] lemma geomFibrePointAddEquiv_apply (P : E.Point (geomPoint B k)) :
    geomFibrePointAddEquiv W E hE hπ hz k P =
      projModelPointsEquiv W k (pointSpecPointsEquiv W E hE hπ k P) := rfl

end EllipticCurve

/-- On a Tate-normal-form curve over a field (`a₄ = 0`, `a₂` and `a₃` units) the marked affine
point `(0, 0)` is nowhere of order `1`, `2`, or `3`: every `a • (0, 0)` with `1 ≤ a ≤ 3` is a
genuine affine point, never the identity. (`ψ₂(0,0) = a₃`, `ψ₃(0,0) = b₈ = a₂a₃²`; `(0,0)` fails to
be 2-torsion since `0 ≠ negY(0,0) = -a₃`, and `3•(0,0)` has distinct `x`-coordinate `-a₂ ≠ 0`.) This
is the affine core of the atlas leaf `NowhereGeomOrderLEThree (tateMarkedPoint)` (Y1-vi),
transferred to fibres through `EllipticCurve.geomFibrePointAddEquiv`. -/
lemma affine_origin_order_gt_three {k : Type u} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic] (h4 : W.a₄ = 0)
    (hB2 : IsUnit W.a₂) (hB3 : IsUnit W.a₃)
    (hns : W.toAffine.Nonsingular 0 0) (a : ℕ) (ha0 : 0 < a) (ha3 : a ≤ 3) :
    (a : ℤ) • (WeierstrassCurve.Affine.Point.some 0 0 hns) ≠ 0 := by
  have hne : ¬((0 : k) = 0 ∧ (0 : k) = W.toAffine.negY 0 0) := by
    rintro ⟨-, h⟩
    apply hB3.ne_zero
    rw [WeierstrassCurve.Affine.negY, show W.toAffine.a₃ = W.a₃ from rfl,
      show W.toAffine.a₁ = W.a₁ from rfl] at h
    linear_combination h
  interval_cases a
  · show (1 : ℤ) • _ ≠ 0
    rw [one_zsmul]
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns
  · show (2 : ℤ) • _ ≠ 0
    rw [two_zsmul, WeierstrassCurve.Affine.Point.add_some hne]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · have hℓ : W.toAffine.slope 0 0 0 0 = 0 := by
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (fun h ↦ hne ⟨rfl, h⟩)]
      simp [h4]
    have hx2 : W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = -W.a₂ := by
      rw [hℓ, WeierstrassCurve.Affine.addX]; ring
    show (3 : ℤ) • _ ≠ 0
    rw [show (3 : ℤ) = 2 + 1 by ring, add_zsmul, two_zsmul, one_zsmul,
      WeierstrassCurve.Affine.Point.add_some hne]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by rw [hx2]; simpa using hB2.ne_zero)]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _

end ModularCurves