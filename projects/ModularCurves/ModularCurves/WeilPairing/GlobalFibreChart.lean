/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FibreGalois
import ModularCurves.EllipticCurve.GlobalChartOverField
import ModularCurves.Moduli.KeystoneGeometricPoint

/-!
# The Galois fibre chart over a field (DS4 M1c, node F′)

`WeilPairing/FibreGalois.lean` builds the field-level DS4 Weil pairing from a
`GaloisFibreChart` — a Weierstrass model of `E` **over `k` itself**, together with the
Galois-equivariant point dictionary at the geometric point. This file constructs one.

The two things to transport are exactly the ones the plan flagged:

* the chart supplied by `LocalPresentation` lives over `Γ(Spec k, ⊤)`, not over `k`, so the
  model is pushed forward along `Scheme.ΓSpecIso`, and `L` is given the induced
  `Γ(Spec k, ⊤)`-algebra structure (chosen so that the two base changes of the model are
  *definitionally* the same curve);
* the chart's structure map `chartρ ⊤` is `Spec` of `ΓSpecIso.inv`
  (`IsAffineOpen.fromSpec_top`), so the chart's geometric point is the canonical one.

Everything is split into single steps; the `Opens`/`ΓSpecIso` coercions in this file are
exactly where a monolithic proof would stall.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

open LocalPresentation

section GlobalChart

variable (k : Type u) [Field k]

/-- The whole of `Spec k` as an affine open. -/
noncomputable abbrev topAffineOpen : (Spec (CommRingCat.of k)).affineOpens := ⟨⊤, isAffineOpen_top _⟩

/-- **(F1)** Over an affine scheme the structure map of the `⊤`-chart is `Spec` of the
inverse of `ΓSpecIso`. -/
theorem chartρ_topAffineOpen :
    chartρ (topAffineOpen k) = Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
  (IsAffineOpen.fromSpec_top (X := Spec (CommRingCat.of k))).trans
    (Scheme.isoSpec_Spec_inv _)

variable (L : Type u) [Field L] [Algebra k L]

/-- The `Γ(Spec k, ⊤)`-algebra structure on `L` induced by `ΓSpecIso`. Defined as the
composite ring hom so that `(Pr.W.map ΓSpecIso.hom).baseChange L` and
`Pr.W.baseChange L` are the *same* Weierstrass curve. -/
@[reducible] noncomputable def gammaTopAlgebra : Algebra Γ(Spec (CommRingCat.of k), ⊤) L :=
  ((algebraMap k L).comp (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom).toAlgebra

/-- **(F2)** With that structure, the chart's geometric point is the canonical one. -/
theorem geomPt_eq_chart :
    letI := gammaTopAlgebra k L
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Spec (CommRingCat.of k), ⊤) L)) ≫
        chartρ (topAffineOpen k) = geomPt k L := by
  letI := gammaTopAlgebra k L
  rw [chartρ_topAffineOpen, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  show (algebraMap k L).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) = algebraMap k L c
  rw [RingHom.comp_apply]
  congr 1
  exact congrFun (congrArg (fun t : CommRingCat.of k ⟶ CommRingCat.of k =>
    (CommRingCat.Hom.hom t : k → k)) (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id) c

variable [DecidableEq L] [IsAlgClosed L]
  (E : EllipticCurve (Spec (CommRingCat.of k)))

/-- A `k`-algebra automorphism of `L` is a `Γ(Spec k, ⊤)`-algebra automorphism, since the
`Γ(Spec k, ⊤)`-structure factors through `k`. -/
noncomputable def gammaTopAlgEquiv (σ : L ≃ₐ[k] L) :
    letI := gammaTopAlgebra k L
    L ≃ₐ[Γ(Spec (CommRingCat.of k), ⊤)] L :=
  letI := gammaTopAlgebra k L
  AlgEquiv.ofRingEquiv (f := (σ : L ≃+* L)) fun c => σ.commutes _

/-- **(F′ ★)** The Galois fibre chart of an elliptic curve over a field: the global
Weierstrass presentation (`GlobalChartOverField`) pushed forward along
`Γ(Spec k, ⊤) ≅ k`, with node D as its equivariance. -/
noncomputable def globalGaloisFibreChart : GaloisFibreChart k E L :=
  letI := gammaTopAlgebra k L
  letI Pr := localPresentationTop E.toEllipticCurveGeom
  letI := Pr.elliptic
  { W := Pr.W.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    elliptic := inferInstanceAs ((Pr.W.baseChange L).toAffine.IsElliptic)
    dict := (EllipticCurve.pointCongr E (geomPt_eq_chart k L).symm).trans
      (chartAffinePointEquiv Pr L)
    equivariant := fun σ P Q hQ => by
      refine Eq.trans (chartAffinePointEquiv_of_coe_eq Pr L (gammaTopAlgEquiv k L σ)
        (EllipticCurve.pointCongr E (geomPt_eq_chart k L).symm P)
        (EllipticCurve.pointCongr E (geomPt_eq_chart k L).symm Q) hQ) ?_
      -- the two `Point.map`s differ only through the `AlgHom`'s base ring; their
      -- underlying functions are both `σ`, so a case split on the point closes it
      have key : ∀ Z : (Pr.W.baseChange L).toAffine.Point,
          WeierstrassCurve.Affine.Point.map (W' := Pr.W) (F := L) (K := L)
              ((gammaTopAlgEquiv k L σ) :
                L →ₐ[Γ(Spec (CommRingCat.of k), ⊤)] L) Z =
            galoisPointEquiv
              (Pr.W.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom) σ Z := by
        intro Z
        cases Z with
        | zero => rfl
        | some x y h => rfl
      exact key _ }

end GlobalChart

/-! ## The unconditional field-level DS4 Weil pairing -/

/-- **(DS4 M1c ★★★★ — unconditional)** For an elliptic curve over a **perfect** field `k`
with `N` invertible in `k`, the Weil pairing exists as a morphism of finite étale
`k`-algebras

`μ_N ⟶ 𝒪(E[N]) ⊗_k 𝒪(E[N])`,

equivalently a morphism of `k`-schemes `E[N] ×_{Spec k} E[N] ⟶ μ_{N, Spec k}`, inducing
the Weil pairing of Silverman AEC III.8 on geometric fibres.

Chain: `weilPairing_galois` (the pairing is `Gal(k̄/k)`-equivariant) → nodes A–D (the chart
dictionaries are Galois-natural) → `globalGaloisFibreChart` (every elliptic curve over a
field has a global `k`-rational chart, since `Spec k` is a point) →
`exists_pairingAlgebraHom_of_galoisEquivariant` (fullness of the fibre functor of the
Galois category of finite étale `k`-algebras). -/
theorem exists_weilPairingHom_of_field (k : Type u) [Field k] [PerfectField k]
    [DecidableEq (AlgebraicClosure k)]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] (hk : (N : k) ≠ 0) :
    ∃ w : muNAlgebra k N hk ⟶ EllipticCurve.torsionPairAlgebra k E N hk,
      ∀ f : ((EllipticCurve.torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k),
        f.comp w.hom.hom =
          weilPairingFibreMap k N hk E (globalGaloisFibreChart k (AlgebraicClosure k) E)
            (EllipticCurve.torsionPairAlgebraPointsEquiv k E N hk f) :=
  exists_weilPairingHom_of_galoisFibreChart k N hk E
    (globalGaloisFibreChart k (AlgebraicClosure k) E)

end ModularCurves
