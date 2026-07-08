import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.LevelStructure.ExactOrder

/-!
# [T-B6′-IFACE] — the geometric-fibre point comparison (scheme ↔ affine), as a group iso

**Shared sorried pin** for the two consumers of the KM 2.3 fibre-comparison box **T-B6**:
* STREAM-Y1's atlas leaves **ii** (order ⟹ unit) and **vi** (`P₀` nowhere order ≤ 3), and
* the parked **BB-DIFF** étale cascade's leaf **L-B** (`E[N]_{k̄} ≅ (ℤ/N)²`) — recorded v10.38 as
  `BB-DIFF ⟸ T-B6′`.

**T-B6 board spec** (verbatim, `decomposition-km2.3-b5d.md` §L-B, KM 2.3.1 proof p. 74):
> "the scheme fibre `E_{k̄}` ↔ HasseWeil `WeierstrassCurve k̄` comparison (template:
> `WeilPairing/GaloisEquivariance.lean`'s `E.Point t ↔ W.toAffine.Point` identification), which
> must be built **non-circularly** (the current T-B6 routes through `torsionπ_etale`)."
and (`decomposition-2026-07-05-phase1.md`, B4): "fibre comparison `E[N] ×_S Spec k̄ ≅ (ℤ/N)²`".

The **set** bijection `projModelPointsEquiv : SpecPoints (projModel W) (projModelπ W) K ≃
(W.baseChange K).toAffine.Point` is already proven (T-W7.0f). The T-B6 content that remains is the
single fact that it is a **group** homomorphism — the fibrewise group-law intertwining. Here the
underlying `Equiv` is built honestly (`pointSpecPointsEquiv`, the `E.Point ↔ SpecPoints` bridge, is
ungated geometry — axiom-clean), and **only `map_add'` carries the `sorry`** — the exact `[T-B6′]`
pin. It discharges when stream-B lands T-B6 (post-T-W7.36); until then every consumer's use carries
a tracked `sorryAx` (not a defect — the same class as `abelEnrichment_exists`).

## Main declarations

* `EllipticCurve.pointSpecPointsEquiv` — the ungated `E.Point (geomPoint) ≃ SpecPoints` bridge.
* `EllipticCurve.geomFibrePointAddEquiv` — **[T-B6′-IFACE]** the scheme-fibre ↔ affine group `≃+`;
  `map_add'` sorried.
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

/-- **[T-B6′-IFACE]** The geometric-fibre point comparison as a **group** isomorphism: the scheme
fibre points `E.Point (geomPoint)` are `≃+` to the affine Weierstrass points
`(W.baseChange k).toAffine.Point`. The underlying bijection is the proven
`pointSpecPointsEquiv ≫ projModelPointsEquiv`; **only `map_add'` is the sorried T-B6 pin** (the
fibrewise group-law intertwining, stream-B, discharged post-T-W7.36). -/
noncomputable def geomFibrePointAddEquiv :
    E.Point (geomPoint B k) ≃+ (W.baseChange k).toAffine.Point where
  toEquiv := (pointSpecPointsEquiv W E hE hπ k).trans (projModelPointsEquiv W k)
  map_add' := sorry

omit [(W.baseChange k).IsElliptic] in
@[simp] lemma geomFibrePointAddEquiv_apply (P : E.Point (geomPoint B k)) :
    geomFibrePointAddEquiv W E hE hπ k P =
      projModelPointsEquiv W k (pointSpecPointsEquiv W E hE hπ k P) := rfl

end EllipticCurve

end ModularCurves
