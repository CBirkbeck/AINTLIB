/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FibrePointDict
import ModularCurves.WeilPairing.GaloisFieldPairing
import ModularCurves.Moduli.ChartPointsGalois
import ModularCurves.WeilPairing.GaloisFibre

/-!
# Galois equivariance at a geometric fibre (DS4 M1c, nodes D–E)

Node D assembles the two chart naturality statements of `Moduli/ChartPointsGalois.lean`
into naturality of `chartAffinePointEquiv`, and node E transports
`fieldWeilPairing_galois` along it, giving `σ`-equivariance of `fibreWeilPairing` — the
pairing on *scheme* points that the étale-descent engine consumes.

As throughout this stream, hypotheses are stated on **underlying morphisms**: the
scheme-level Galois action is `P ↦ Spec σ ≫ P`, and `Spec σ ≫ t = t` only
propositionally, so carrying it in a dependent type is what makes these arguments
expensive.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

/-! ## Node D — `chartAffinePointEquiv` -/

section ChartAffine

open LocalPresentation

variable {S : Scheme.{u}} {E : EllipticCurve S} {V : S.affineOpens}
  (Pr : LocalPresentation E.toEllipticCurveGeom V)
  (K : Type u) [Field K] [DecidableEq K] [Algebra Γ(S, V.1) K]

/-- **(D ★)** The geometric-fibre point dictionary carries the scheme-level Galois action
`P ↦ Spec σ ≫ P` to mathlib's coordinatewise `Affine.Point.map σ`. -/
theorem chartAffinePointEquiv_of_coe_eq (σ : K ≃ₐ[Γ(S, V.1)] K)
    (P Q : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hQ : (Q.1 : Spec (CommRingCat.of K) ⟶ E.E) =
      Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ (P.1 : Spec (CommRingCat.of K) ⟶ E.E)) :
    letI := Pr.elliptic
    chartAffinePointEquiv Pr K Q =
      WeierstrassCurve.Affine.Point.map (W' := Pr.W) (F := K) (K := K)
        (σ : K →ₐ[Γ(S, V.1)] K) (chartAffinePointEquiv Pr K P) := by
  letI := Pr.elliptic
  -- `Spec σ` fixes the geometric point
  have hσt : Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c => σ.commutes c)
  -- the same point, read over the moved base
  refine modelPointAddEquiv_of_coe_eq Pr.W σ (chartPointsEquiv Pr _ P)
    (chartPointsEquiv Pr _ Q) ?_
  refine Eq.trans (chartPointsEquiv_congr_base Pr hσt.symm Q
    (⟨Q.1, by rw [hσt]; exact Q.2⟩ :
      E.Point ((Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K))) ≫ chartρ V)) rfl) ?_
  exact chartPointsEquiv_restrict_coe Pr _ _ P ⟨Q.1, by rw [hσt]; exact Q.2⟩ hQ

end ChartAffine

/-! ## The chart as labelled data, and node E′ -/

section FibrePairing

variable (k : Type u) [Field k] (E : EllipticCurve (Spec (CommRingCat.of k)))
  (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L]

/-- The geometric point of `E` at the algebraically closed extension `L`.

Named `geomFieldPt`, not `geomPt`: `ModularCurve/RhoSections.lean` already has a
`ModularCurves.geomPt`, the geometric point of a *scheme* at a point of its space (215 uses
against this one's six), and the two collided when the orphan modules were wired into the
root import. -/
noncomputable abbrev geomFieldPt : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- **(DS4 M1c, labelled data)** A `k`-rational Weierstrass chart for `E` at the geometric
point, together with its Galois equivariance.

The `equivariant` field is exactly `chartAffinePointEquiv_of_coe_eq` (node D) once the
chart is transported from `Γ(Spec k, ⊤)` to `k`; it is packaged as data so that the
pairing construction below does not have to wait on that transport. -/
structure GaloisFibreChart where
  /-- A Weierstrass model of `E` over `k` itself. -/
  W : WeierstrassCurve k
  /-- Its base change to `L` is elliptic. -/
  elliptic : (W.baseChange L).toAffine.IsElliptic
  /-- The point dictionary at the geometric point. -/
  dict : E.Point (geomFieldPt k L) ≃+ (W.baseChange L).toAffine.Point
  /-- The dictionary carries the scheme-level Galois action `P ↦ Spec σ ≫ P` to mathlib's
  coordinatewise action. -/
  equivariant : ∀ (σ : L ≃ₐ[k] L) (P Q : E.Point (geomFieldPt k L)),
    (Q.1 : Spec (CommRingCat.of L) ⟶ E.E) =
        Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫
          (P.1 : Spec (CommRingCat.of L) ⟶ E.E) →
      letI := elliptic
      dict Q = galoisPointEquiv W σ (dict P)

variable {k E L}

/-- The Weil pairing on the scheme points of `E` at the geometric point, computed through
a `GaloisFibreChart`. -/
noncomputable def GaloisFibreChart.pairing (C : GaloisFibreChart k E L) (N : ℕ)
    (hN : (N : L) ≠ 0) (P Q : E.Point (geomFieldPt k L))
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) : { u : L // u ^ N = 1 } :=
  letI := C.elliptic
  fieldWeilPairing (C.W.baseChange L) N hN (C.dict P) (C.dict Q)
    (by rw [← map_zsmul, hP, map_zero]) (by rw [← map_zsmul, hQ, map_zero])

/-- **(E′ ★)** The pairing on scheme points is `Gal(L/k)`-equivariant: the transport of
`fieldWeilPairing_galois` along the chart. -/
theorem GaloisFibreChart.pairing_galois (C : GaloisFibreChart k E L) (σ : L ≃ₐ[k] L)
    (N : ℕ) (hN : (N : L) ≠ 0) (P Q P' Q' : E.Point (geomFieldPt k L))
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (hP' : (N : ℤ) • P' = 0) (hQ' : (N : ℤ) • Q' = 0)
    (hPP' : (P'.1 : Spec (CommRingCat.of L) ⟶ E.E) =
      Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (P.1 : _ ⟶ E.E))
    (hQQ' : (Q'.1 : Spec (CommRingCat.of L) ⟶ E.E) =
      Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (Q.1 : _ ⟶ E.E)) :
    (C.pairing N hN P' Q' hP' hQ' : L) = σ (C.pairing N hN P Q hP hQ : L) := by
  letI := C.elliptic
  have hdP : C.dict P' = galoisPointEquiv C.W σ (C.dict P) := C.equivariant σ P P' hPP'
  have hdQ : C.dict Q' = galoisPointEquiv C.W σ (C.dict Q) := C.equivariant σ Q Q' hQQ'
  have hsP : (N : ℤ) • C.dict P = 0 := by rw [← map_zsmul, hP, map_zero]
  have hsQ : (N : ℤ) • C.dict Q = 0 := by rw [← map_zsmul, hQ, map_zero]
  have hsP' : (N : ℤ) • C.dict P' = 0 := by rw [← map_zsmul, hP', map_zero]
  have hsQ' : (N : ℤ) • C.dict Q' = 0 := by rw [← map_zsmul, hQ', map_zero]
  have hgP : (N : ℤ) • galoisPointEquiv C.W σ (C.dict P) = 0 :=
    zsmul_galoisPointEquiv_eq_zero C.W σ (N : ℤ) hsP
  have hgQ : (N : ℤ) • galoisPointEquiv C.W σ (C.dict Q) = 0 :=
    zsmul_galoisPointEquiv_eq_zero C.W σ (N : ℤ) hsQ
  refine Eq.trans (fieldWeilPairing_congr (C.W.baseChange L) N hN hsP' hsQ' hgP hgQ hdP hdQ) ?_
  exact fieldWeilPairing_galois C.W σ N hN (C.dict P) (C.dict Q) hsP hsQ hgP hgQ

/- **(WP-D3d step 4, move 2) — IN PROGRESS, two gaps localised.** The chart-level determinant law,
stated with the `σ`-action scheme-theoretically (as `pairing_galois` is, because `C.pairing` hides
`IsElliptic` in a `letI`):

  `σ (C.pairing N hN P Q hP hQ) = (C.pairing N hN P Q hP hQ) ^ (g 0 0 * g 1 1 - g 0 1 * g 1 0).val`

given `hPP'`/`hQQ'` as in `pairing_galois` plus `hgP : P' = (g 0 0).val • P + (g 0 1).val • Q` and
`hgQ` likewise. Skeleton: `letI := C.elliptic`; `pairing_galois … |>.symm.trans`; transport `hgP`/`hgQ`
through `C.dict`; `fieldWeilPairing_congr`; `fieldWeilPairing_gl2_zmod`.

Two gaps found on the first attempt, both concrete:

* `fieldWeilPairing_congr`'s **torsion arguments cannot be `_`** — the two *primed* ones are the torsion
  proofs of the `g`-combination, which nothing determines. Supply all four explicitly:
  `hsP : (N : ℤ) • C.dict P = 0` (from `hP` by `← map_zsmul`), similarly `hsQ`, and
  `hsP' : (N : ℤ) • ((g 0 0).val • C.dict P + (g 0 1).val • C.dict Q) = 0`
  (by `rw [← hdP, ← map_zsmul, hP', map_zero]`), similarly `hsQ'`. Mind the direction: `hdP` reads
  `C.dict P' = comb`, so in `congr`'s vocabulary the *source* is `C.dict P'` and the *target* is `comb`.
* `hdP : C.dict P' = (g 0 0).val • C.dict P + (g 0 1).val • C.dict Q` is **not** closed by
  `rw [hgP, map_add, map_nsmul, map_nsmul]` — that leaves goals. The coefficients are `ZMod.val`s
  (`ℕ`), while `C.dict` is an **`AddEquiv`** (field type confirmed: `E.Point (geomFieldPt k L) ≃+
  (W.baseChange L).toAffine.Point`). `map_add` does fire; the `nsmul` steps are what remain, so try
  `AddEquiv.map_nsmul`, or `map_nsmul (C.dict : _ →+ _)` with the hom coercion made explicit, or
  `simp only [map_add, map_nsmul]` instead of a `rw` chain — a `rw` cannot fire the same `map_nsmul`
  pattern at two different coefficient positions in one list, which is the likely cause of the leftover
  goals (the same trap as `pullback.lift_fst_assoc` in `fullLevelSqIso_inv_baseChange`).

Everything else in step 4 is proved: `algebraMap_fieldPairingValue_eq_pairing` (move 1) and
`algebraMap_factorRootOfUnityDescend` (move 3's descent). -/

end FibrePairing

/-! ## Node G′ — the field-level DS4 pairing as a morphism of finite étale algebras -/

section Descent

variable (k : Type u) [Field k] [DecidableEq (AlgebraicClosure k)] (N : ℕ) [NeZero N]
  (hk : (N : k) ≠ 0)

include hk in
/-- `N` stays invertible in any `k`-algebra that is a field. -/
theorem natCast_ne_zero_of_algebra {R : Type u} [CommRing R] [Nontrivial R] [Algebra k R]
    [FaithfulSMul k R] : (N : R) ≠ 0 := by
  intro h
  refine hk (FaithfulSMul.algebraMap_injective k R ?_)
  rw [map_natCast, map_zero]
  exact h

/-- Applying `σ` to an `N`-th root of unity, on the `μ_N`-algebra side. -/
theorem muNAlgebraFibreEquiv_symm_algEquiv (R : Type u) [CommRing R] [Algebra k R]
    (σ : R ≃ₐ[k] R) (u : { a : R // a ^ N = 1 }) (hu : (σ u.1) ^ N = 1) :
    (muNAlgebraFibreEquiv k N hk R).symm ⟨σ u.1, hu⟩ =
      (σ : R →ₐ[k] R).comp ((muNAlgebraFibreEquiv k N hk R).symm u) := by
  refine (Equiv.symm_apply_eq _).mpr (Subtype.ext ?_)
  rw [muNAlgebraFibreEquiv_comp_algEquiv, Equiv.apply_symm_apply]

variable (E : EllipticCurve (Spec (CommRingCat.of k)))

/-- The section represented by a fibre-functor value of `torsionAlgebra`, as a point of
`E` at the geometric point. -/
noncomputable abbrev torsionFibrePoint
    (f : (EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) :
    E.Point (geomFieldPt k (AlgebraicClosure k)) :=
  (EllipticCurve.torsionAlgebraFibreEquiv k E N hk (AlgebraicClosure k) f : _)

include hk in
theorem torsionFibrePoint_torsion
    (f : (EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) :
    (N : ℤ) • torsionFibrePoint k N hk E f = 0 :=
  (Submodule.mem_torsionBy_iff _ _).mp
    (EllipticCurve.torsionAlgebraFibreEquiv k E N hk (AlgebraicClosure k) f).2

/-- **(G′, the fibre map)** The Weil pairing as a map on fibre-functor values, valued in
the fibre of `μ_N`. -/
noncomputable def weilPairingFibreMap (C : GaloisFibreChart k E (AlgebraicClosure k)) :
    ((EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
        ((EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) →
      ((muNAlgebra k N hk).obj →ₐ[k] AlgebraicClosure k) :=
  fun x => (muNAlgebraFibreEquiv k N hk (AlgebraicClosure k)).symm
    (C.pairing N (natCast_ne_zero_of_algebra k N hk)
      (torsionFibrePoint k N hk E x.1) (torsionFibrePoint k N hk E x.2)
      (torsionFibrePoint_torsion k N hk E x.1) (torsionFibrePoint_torsion k N hk E x.2))

/-- **(G′ ★)** The fibre map is `Gal(k̄/k)`-equivariant — the hypothesis the finite-étale
descent engine consumes. -/
theorem weilPairingFibreMap_galoisEquivariant
    (C : GaloisFibreChart k E (AlgebraicClosure k))
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (x : ((EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
      ((EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k)) :
    weilPairingFibreMap k N hk E C
        ((σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).comp x.1,
          (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).comp x.2) =
      (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).comp
        (weilPairingFibreMap k N hk E C x) := by
  set x₁ : (EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k :=
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).comp x.1 with hx₁
  set x₂ : (EllipticCurve.torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k :=
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).comp x.2 with hx₂
  have hsec₁ := EllipticCurve.torsionAlgebraFibreEquiv_comp_algEquiv k E N hk
    (AlgebraicClosure k) σ x.1
  have hsec₂ := EllipticCurve.torsionAlgebraFibreEquiv_comp_algEquiv k E N hk
    (AlgebraicClosure k) σ x.2
  have hgal := C.pairing_galois σ N (natCast_ne_zero_of_algebra k N hk)
    (torsionFibrePoint k N hk E x.1) (torsionFibrePoint k N hk E x.2)
    (torsionFibrePoint k N hk E x₁) (torsionFibrePoint k N hk E x₂)
    (torsionFibrePoint_torsion k N hk E x.1) (torsionFibrePoint_torsion k N hk E x.2)
    (torsionFibrePoint_torsion k N hk E x₁) (torsionFibrePoint_torsion k N hk E x₂)
    hsec₁ hsec₂
  refine Eq.trans ?_ (muNAlgebraFibreEquiv_symm_algEquiv k N hk (AlgebraicClosure k) σ _
    (by rw [← hgal]; exact (C.pairing N (natCast_ne_zero_of_algebra k N hk) _ _ _ _).2))
  exact congrArg (muNAlgebraFibreEquiv k N hk (AlgebraicClosure k)).symm (Subtype.ext hgal)

/-- **(DS4 M1c ★★★ — the field-level Weil pairing as a scheme morphism)** Over a **perfect**
field, given a Galois-equivariant Weierstrass chart at the geometric point,
the Weil pairing descends to an honest morphism of finite étale `k`-algebras

`μ_N ⟶ E[N] ⊗ E[N]`,

i.e. to a morphism of `k`-schemes `E[N] ×_{Spec k} E[N] ⟶ μ_{N, Spec k}`, inducing the
Weil pairing on geometric fibres.

The descent is `exists_pairingAlgebraHom_of_galoisEquivariant` (fullness of the fibre
functor of the Galois category of finite étale `k`-algebras); the equivariance it consumes
is `weilPairingFibreMap_galoisEquivariant`, which is `weilPairing_galois` transported
along the chart. -/
theorem exists_weilPairingHom_of_galoisFibreChart [PerfectField k]
    (C : GaloisFibreChart k E (AlgebraicClosure k)) :
    ∃ w : muNAlgebra k N hk ⟶ EllipticCurve.torsionPairAlgebra k E N hk,
      ∀ f : ((EllipticCurve.torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k),
        f.comp w.hom.hom = weilPairingFibreMap k N hk E C
          (EllipticCurve.torsionPairAlgebraPointsEquiv k E N hk f) :=
  EllipticCurve.exists_pairingAlgebraHom_of_galoisEquivariant k E N hk
    (weilPairingFibreMap k N hk E C)
    (weilPairingFibreMap_galoisEquivariant k N hk E C)

end Descent

end ModularCurves
