/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.Basic
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.EllipticCurve.TorsionUnramifiedFibre
import ModularCurves.ForMathlib.FiniteEtaleGalois
import ModularCurves.ForMathlib.FiniteEtaleFundamentalGroup
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The char-0 étale-descent Weil pairing (T-C0)

The review's first milestone (expert review 2026-07-05, Q5): over characteristic-zero
bases the `N`-torsion is finite étale, so the Weil pairing can be constructed by
Galois descent of the classical field-level pairing (HasseWeil, Silverman III.8),
through the Galois-category machinery of `ForMathlib/FiniteEtaleGalois.lean`
(AG-GG): a morphism of finite étale `k`-algebras is exactly a Galois-equivariant map
of fibre-functor values.

Chain (board ticket T-C0, decomposition v6):
* `torsionAlgebra` (T-C0a): `E[N]` over `Spec k` as an object of
  `CommAlgCat.FiniteEtale k` — `E[N]` is finite over the affine base (hence affine),
  étale for `N` invertible (T-B5 boxes), and `Γ`-transports to a finite étale
  `k`-algebra.
* `torsionAlgebraPointsEquiv` (T-C0b): the fibre-functor value of `torsionAlgebra`
  is `E.Point`-torsion over `k̄`, Galois-equivariantly (bridges to
  `torsion_geometricFibre_rank_two`).
* `weilPairing_galois_equivariant` (T-C0c): the HasseWeil field-level pairing is
  `Gal(k̄/k)`-equivariant (`σ e(P,Q) = e(σP, σQ)`; Silverman convention per review
  Q6 — determinant of the mod-`N` representation is the cyclotomic character).
* **the T-C0d-i transport layer (this file, gate-free)**: `muNAlgebra` packages
  `μ_N/Spec k` as a finite étale `k`-algebra (no boxes — `muNπ_isFinite` and
  `muNπ_etale_iff` are proven in `GroupScheme/MuN.lean`), with fibre pin
  `muNAlgebraPointsEquiv` (`N`-th roots of unity of `k̄`, via `muNPointsEquiv` and the
  generic affine correspondence `algHomEquivSpecOver`); `torsionPairAlgebra` packages
  `torsionAlgebra ⊗[k] torsionAlgebra` with fibre pin `torsionPairAlgebraPointsEquiv`
  (via `tensorAlgHomPairEquiv`); and `exists_finiteEtaleHom_of_galoisEquivariant` is
  the descent heart — a `Gal(k^sep/k)`-equivariant map of fibre-functor values
  descends to a morphism of finite étale algebras, by fullness of mathlib's
  `PreGaloisCategory.functorToContAction` against the `IsFundamentalGroup` instance
  of `ForMathlib/FiniteEtaleFundamentalGroup.lean`. The packaging theorem
  `exists_pairingAlgebraHom_of_galoisEquivariant` instantiates it: any
  `Gal(k̄/k)`-equivariant pairing on `k̄`-fibres is induced by a morphism
  `muNAlgebra ⟶ torsionPairAlgebra` (an algebra hom *into* the tensor = a scheme
  morphism `E[N] ×_{Spec k} E[N] ⟶ μ_N`).
* `weilPairingEtale` (T-C0d): the pairing as a morphism
  `torsionAlgebra ⊗ torsionAlgebra ⟶ muNAlgebra` in `CommAlgCat.FiniteEtale k`,
  transported through the Galois equivalence from T-C0b/T-C0c — the remaining input
  is the equivariant fibre-level pairing (T-C0b/T-C0c), fed to
  `exists_pairingAlgebraHom_of_galoisEquivariant`.
The **field-valued-points** pairing of record is `exists_pairingAlgebraHom_of_galoisEquivariant`
above: over a char-0 field `k`, it descends a `Gal(k̄/k)`-equivariant pairing on `k̄`-points to a
finite-étale algebra hom `μ_N ⟶ E[N] ⊗ E[N]` — equivalently a scheme morphism on the geometric
fibre. Per the v9 expert review (2026-07-07, §"Weil pairing"), **this field case is NOT the pairing
the moduli functor needs**: `Y(ρ̄)` classifies elliptic curves over arbitrary `ℚ`-schemes `T`, not
just fields, so the DS4 target is the **`T`-relative morphism**
`weilPairingCharZero : E[N] ×_T E[N] ⟶ μ_{N,T}` over `Spec ℚ`-schemes, built étale-locally on `T`
(where the finite-étale `E[N]` trivialises to a constant `(ℤ/N)²`) then descended (mathlib
`AlgebraicGeometry.Morphisms.FlatDescent`), with Silverman/determinant normalisation and the
symplectic pin `e_N(aP+bQ, cP+dQ) = e_N(P,Q)^{ad−bc}`. That construction is board ticket **T-C0e**
(re-cut v9.4) — its concrete point identification funnels into **T-W7** (group law from Weierstrass
charts, A-lane), the documented convergence point for the remaining H/C frontier. The earlier
scheme-level field statement `exists_weilPairingSpecField` was **removed** (2026-07-07): its
constraint `w ≫ muNπ = fst ≫ torsionπ` pins only "a morphism over the base", which a trivial
section satisfies — it was neither the field-valued-points theorem (that is the descent heart
above) nor the moduli pairing (that is `weilPairingCharZero`).

The torsion side consumes the registered T-B4/T-B5 finiteness/étaleness boxes
(`torsionπ_isFinite`/`Torsionπ.etale`); axiom profiles record `sorryAx` through
those gates until the boxes are discharged. The T-C0d-i transport layer itself is
gate-free: `finiteEtaleOfπ`, `muNAlgebra`, `muNAlgebraPointsEquiv`, `algHomEquivSpecOver`,
`tensorAlgHomPairEquiv` and `exists_finiteEtaleHom_of_galoisEquivariant` are
axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only); `sorryAx` enters
`torsionPairAlgebra`/`torsionPairAlgebraPointsEquiv`/
`exists_pairingAlgebraHom_of_galoisEquivariant` only through `torsionAlgebra`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open AlgebraicGeometry CategoryTheory Limits

open scoped TensorProduct

universe u

namespace ModularCurves

/-- Package a finite étale morphism to an affine base as a finite étale algebra: if
`π : X ⟶ Spec k` is finite (hence `X` affine) and étale, then `Γ(X, ⊤)` is a finite étale
`k`-algebra for the structure map induced by `π`. Both `torsionAlgebra` (T-C0a) and
`muNAlgebra` (T-C0d-i) are instances; the only difference between them is which
finiteness/étaleness inputs discharge the two hypotheses. -/
noncomputable def finiteEtaleOfπ {k : Type u} [Field k] {X : Scheme.{u}}
    (π : X ⟶ Spec (CommRingCat.of k)) (hfin : IsFinite π) (het : Etale π) :
    CommAlgCat.FiniteEtale.{u} k := by
  haveI : IsFinite π := hfin
  haveI : IsAffine X := isAffine_of_isAffineHom π
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop).hom.toAlgebra
  haveI : Module.Finite k Γ(X, ⊤) := by
    have h : RingHom.Finite
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop).hom := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr
        (π.finite_app ⊤ (isAffineOpen_top _))
    exact h
  haveI : Algebra.Etale k Γ(X, ⊤) := by
    have h : RingHom.Etale
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop).hom := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).mpr
        ((HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).mp het)
    exact h
  exact CommAlgCat.FiniteEtale.of k Γ(X, ⊤)

section AffineFibre

/-- The affine `Γ ⊣ Spec` fibre correspondence over `Spec k`: for an affine scheme `X`
over `Spec k` whose global sections carry the induced `k`-algebra structure, `k`-algebra
homomorphisms `Γ(X, ⊤) →ₐ[k] R` are exactly the `Spec R`-points of `X` over `Spec k`.
Both fibre pins are instances of it: `torsionAlgebraPointsEquiv` (T-C0b) composes it
with `torsionPointsEquiv`, and `muNAlgebraPointsEquiv` with `muNPointsEquiv`. -/
noncomputable def algHomEquivSpecOver {k : Type u} [Field k] (R : Type u) [CommRing R]
    [Algebra k R] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of k))
    [Algebra k Γ(X, ⊤)]
    (halg : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop) :
    (Γ(X, ⊤) →ₐ[k] R) ≃
      { h : Spec (CommRingCat.of R) ⟶ X //
        h ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k R)) } := by
  refine
    { toFun := fun f =>
        ⟨Spec.map (CommRingCat.ofHom f.toRingHom :
            Γ(X, ⊤) ⟶ CommRingCat.of R) ≫ X.isoSpec.inv, ?_⟩
      invFun := fun h =>
        ⟨(h.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom,
          fun c => ?_⟩
      left_inv := fun f => ?_
      right_inv := fun h => ?_ }
  · -- the transported morphism lies over `Spec k`
    have hcomp : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) ≫
        (CommRingCat.ofHom f.toRingHom : Γ(X, ⊤) ⟶ CommRingCat.of R) =
        CommRingCat.ofHom (algebraMap k R) :=
      CommRingCat.hom_ext (RingHom.ext fun c => f.commutes c)
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, ← Spec.map_comp, ← halg, hcomp]
  · -- the global-sections map of a morphism over `Spec k` is a `k`-algebra map
    have key : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) ≫
        (h.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
        CommRingCat.ofHom (algebraMap k R) := by
      rw [halg, Category.assoc, ← Scheme.Hom.comp_appTop_assoc, h.2,
        Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom key) c
  · -- left inverse: global sections of the `Spec`-transport recovers the algebra map
    have key : (Spec.map (CommRingCat.ofHom f.toRingHom :
          Γ(X, ⊤) ⟶ CommRingCat.of R) ≫ X.isoSpec.inv).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
        CommRingCat.ofHom f.toRingHom := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop_assoc, Scheme.toSpecΓ_isoSpec_inv,
        Scheme.Hom.id_appTop, Category.id_comp]
    ext x
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom key) x
  · -- right inverse: `Spec`-transport of the global-sections map recovers the morphism
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom
        ((h.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom)) ≫
        X.isoSpec.inv = h.1
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]

end AffineFibre

namespace EllipticCurve

/-- **(T-C0a)** The `N`-torsion of an elliptic curve over a field, as a finite étale
`k`-algebra: `E[N] → Spec k` is finite (T-B4 box) hence affine, and étale when `N` is
invertible (T-B5 box); its global sections carry the corresponding
`CommAlgCat.FiniteEtale k` structure. -/
noncomputable def torsionAlgebra (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
  -- `E[N] → Spec k` is finite (T-B4 box) and étale for `N` invertible (T-B5 box).
  finiteEtaleOfπ (E.torsionπ N) (E.torsionπ_isFinite N)
    (E.torsionπ_etale N ((nIsInvertible_spec_iff k N).mpr hk))

/-- **(T-C0b)** The `k̄`-points of the torsion algebra are the `N`-torsion of the
geometric point group: the fibre functor applied to `torsionAlgebra` is
`Submodule.torsionBy ℤ (E.Point t) N`, compatibly with the `Gal(k̄/k)`-actions
(the algebra side acts through the fibre functor, the point side through
composition with `Spec`-maps of field automorphisms). -/
theorem torsionAlgebraPointsEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    Nonempty (((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      Submodule.torsionBy ℤ
        (E.Point (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
        (N : ℤ)) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  letI : Algebra k Γ(E.torsion N, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom.toAlgebra
  -- Compose the affine `Γ ⊣ Spec` correspondence (`algHomEquivSpecOver`) with the kernel
  -- universal property of `E.torsion N` (`torsionPointsEquiv`).
  refine ⟨Equiv.trans ?_ (E.torsionPointsEquiv N _)⟩
  -- The carrier of `torsionAlgebra` is (definitionally) `Γ(E.torsion N, ⊤)`.
  show (Γ(E.torsion N, ⊤) →ₐ[k] AlgebraicClosure k) ≃ _
  exact algHomEquivSpecOver (AlgebraicClosure k) (E.torsionπ N) rfl

end EllipticCurve

/-! ### The T-C0d-i transport layer: `μ_N`, the torsion pair, and Galois descent

Gate-free infrastructure for T-C0d: `μ_N` and the torsion tensor square as objects of
`CommAlgCat.FiniteEtale k` with pinned fibre-functor values, and the descent theorem
turning a Galois-equivariant map of fibre values into an algebra morphism (fullness of
`PreGaloisCategory.functorToContAction` for the fibre functor at `SeparableClosure k`,
bridged to `AlgebraicClosure k`-fibres in characteristic zero). -/

section MuNAlgebra

/-- **(T-C0d-i, μ side)** `μ_N` over `Spec k` as a finite étale `k`-algebra, for `N`
invertible in `k`: `μ_N → Spec k` is finite (`muNπ_isFinite`) hence affine, and étale
exactly when `N` is invertible (`muNπ_etale_iff`, i.e. `X^N − 1` separable); its global
sections carry the corresponding `CommAlgCat.FiniteEtale k` structure. Unlike
`torsionAlgebra`, this consumes no boxes — both inputs are proven in
`GroupScheme/MuN.lean`. Source: KM 1.12. -/
noncomputable def muNAlgebra (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
  finiteEtaleOfπ (muNπ (Spec (CommRingCat.of k)) N) (muNπ_isFinite _ N)
    ((muNπ_etale_iff (Spec (CommRingCat.of k)) N).mpr ((nIsInvertible_spec_iff k N).mpr hk))

/-- **(T-C0d-i, μ side, fibre pin)** The `k̄`-points of the `μ_N`-algebra are the `N`-th
roots of unity of `k̄`: the fibre-functor value of `muNAlgebra` is
`{a : k̄ // a ^ N = 1}`, through the affine correspondence `algHomEquivSpecOver` and the
registered points description `muNPointsEquiv` (KM 1.12). -/
theorem muNAlgebraPointsEquiv (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    Nonempty (((muNAlgebra k N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      { a : AlgebraicClosure k // a ^ N = 1 }) := by
  haveI : IsFinite (muNπ (Spec (CommRingCat.of k)) N) := muNπ_isFinite _ N
  haveI : IsAffine (muN (Spec (CommRingCat.of k)) N) :=
    isAffine_of_isAffineHom (muNπ (Spec (CommRingCat.of k)) N)
  letI : Algebra k Γ(muN (Spec (CommRingCat.of k)) N, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (muNπ (Spec (CommRingCat.of k)) N).appTop).hom.toAlgebra
  refine ⟨Equiv.trans (Equiv.trans ?_ (muNPointsEquiv (Spec (CommRingCat.of k)) N
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) ?_⟩
  · -- the carrier of `muNAlgebra` is (definitionally) `Γ(μ_N, ⊤)`
    show (Γ(muN (Spec (CommRingCat.of k)) N, ⊤) →ₐ[k] AlgebraicClosure k) ≃ _
    exact algHomEquivSpecOver (AlgebraicClosure k)
      (muNπ (Spec (CommRingCat.of k)) N) rfl
  · -- transport `N`-th roots of unity along `Γ(Spec k̄, ⊤) ≅ k̄`
    exact
      { toFun := fun a =>
          ⟨(Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).hom a.1,
            by rw [← map_pow, a.2, map_one]⟩
        invFun := fun a =>
          ⟨(Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv a.1,
            by rw [← map_pow, a.2, map_one]⟩
        left_inv := fun a => Subtype.ext (by simp)
        right_inv := fun a => Subtype.ext (by simp) }

end MuNAlgebra

section TensorFibre

/-- Splitting the fibre of a tensor product: `k`-algebra homomorphisms out of
`A ⊗[k] B` into a commutative `k`-algebra are pairs of homomorphisms on the factors
(the binary case of the pushout universal property of the tensor product, unbundled to
an `Equiv` via `Algebra.TensorProduct.productMap`). -/
noncomputable def tensorAlgHomPairEquiv (k A B Ω : Type u) [CommRing k] [CommRing A]
    [CommRing B] [CommRing Ω] [Algebra k A] [Algebra k B] [Algebra k Ω] :
    ((A ⊗[k] B) →ₐ[k] Ω) ≃ (A →ₐ[k] Ω) × (B →ₐ[k] Ω) where
  toFun ψ := (ψ.comp Algebra.TensorProduct.includeLeft,
    ψ.comp Algebra.TensorProduct.includeRight)
  invFun fg := Algebra.TensorProduct.productMap fg.1 fg.2
  left_inv ψ := AlgHom.ext fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ψ (a ⊗ₜ[k] 1) * ψ (1 ⊗ₜ[k] b) = ψ (a ⊗ₜ[k] b)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv fg := Prod.ext (Algebra.TensorProduct.productMap_left fg.1 fg.2)
    (Algebra.TensorProduct.productMap_right fg.1 fg.2)

end TensorFibre

section GaloisTransport

/-- **(T-C0d-i, descent heart)** Fullness of the Galois correspondence, unbundled: a
`Gal(k^sep/k)`-equivariant map between the fibre-functor values of two finite étale
`k`-algebras descends to a morphism of algebras inducing it by precomposition.
Equivariance is for postcomposition with automorphisms of the separable closure — the
natural action of `FiniteEtaleFundamentalGroup.fiberMulAction`. The proof packages the
map as a morphism of continuous `Aut F`-actions (`Aut F`-equivariance follows from
`Gal`-equivariance via surjectivity of `PreGaloisCategory.toAut`, i.e. the
`IsFundamentalGroup` instance) and takes a `Functor.map_surjective` preimage along the
full functor `PreGaloisCategory.functorToContAction`. -/
theorem exists_finiteEtaleHom_of_galoisEquivariant {k : Type u} [Field k]
    (A B : CommAlgCat.FiniteEtale.{u} k)
    (q : ((B : Type u) →ₐ[k] SeparableClosure k) →
      ((A : Type u) →ₐ[k] SeparableClosure k))
    (hq : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
        (x : (B : Type u) →ₐ[k] SeparableClosure k),
      q (σ.toAlgHom.comp x) = σ.toAlgHom.comp (q x)) :
    ∃ w : A ⟶ B, ∀ x : (B : Type u) →ₐ[k] SeparableClosure k,
      q x = x.comp w.hom.hom := by
  classical
  -- `Aut F`-equivariance of `q`, from `Gal`-equivariance via surjectivity of `toAut`
  -- (the `Aut F`- and `Gal`-actions agree definitionally through `toAut_hom_app_apply`
  -- and `fiber_smul_def`).
  have hAut : ∀ (g : Aut (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
        (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}))
      (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj (Opposite.op B)),
      q (g.hom.app (Opposite.op B) x) = g.hom.app (Opposite.op A) (q x) := by
    intro g x
    obtain ⟨σ, rfl⟩ := (PreGaloisCategory.toAut_bijective
      (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
        (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u})
      (SeparableClosure k ≃ₐ[k] SeparableClosure k)).surjective g
    exact hq σ x
  -- package `q` as a morphism of the associated continuous `Aut F`-actions and take a
  -- preimage along the full functor `functorToContAction`
  obtain ⟨ψ, hψ⟩ := (PreGaloisCategory.functorToContAction
      (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
        (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u})).map_surjective
    (X := Opposite.op B) (Y := Opposite.op A)
    (ObjectProperty.homMk
      { hom := FintypeCat.homMk q
        comm := fun g => FintypeCat.hom_ext _ _ fun x => hAut g x })
  refine ⟨ψ.unop, fun x => ?_⟩
  exact (congrArg (fun t => t.hom.hom x) hψ).symm

end GaloisTransport

namespace EllipticCurve

/-- **(T-C0d-i, pair side)** `E[N] ×_{Spec k} E[N]` as a finite étale `k`-algebra: the
tensor product `torsionAlgebra ⊗[k] torsionAlgebra` (the pushout in
`CommAlgCat.FiniteEtale k`, i.e. the fibre product of schemes), finite étale by
`FiniteEtaleGalois.etale_tensorProduct`/`finite_tensorProduct`. -/
noncomputable def torsionPairAlgebra (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
  haveI : Algebra.Etale k
      (↑(torsionAlgebra k E N hk).obj ⊗[k] ↑(torsionAlgebra k E N hk).obj) :=
    FiniteEtaleGalois.etale_tensorProduct (k := k) k
      (torsionAlgebra k E N hk).obj (torsionAlgebra k E N hk).obj
  haveI : Module.Finite k
      (↑(torsionAlgebra k E N hk).obj ⊗[k] ↑(torsionAlgebra k E N hk).obj) :=
    FiniteEtaleGalois.finite_tensorProduct (k := k) k
      (torsionAlgebra k E N hk).obj (torsionAlgebra k E N hk).obj
  CommAlgCat.FiniteEtale.of k
    (↑(torsionAlgebra k E N hk).obj ⊗[k] ↑(torsionAlgebra k E N hk).obj)

/-- **(T-C0d-i, pair side, fibre pin)** The fibre-functor value of the pair algebra
splits as the product of two copies of the fibre of `torsionAlgebra` (geometric points
of a fibre product are pairs of points). -/
noncomputable def torsionPairAlgebraPointsEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    ((torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
        ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) :=
  tensorAlgHomPairEquiv k ((torsionAlgebra k E N hk).obj : Type u)
    ((torsionAlgebra k E N hk).obj : Type u) (AlgebraicClosure k)

/-- **(T-C0d-i, packaging)** The gate-free Galois-descent transport for the Weil
pairing: any map `p` from pairs of `k̄`-points of `E[N]` to `k̄`-points of `μ_N` that is
equivariant for the natural `Gal(k̄/k)`-actions (postcomposition on each side) is
induced, under the fibre identification `torsionPairAlgebraPointsEquiv`, by an actual
morphism `w : muNAlgebra ⟶ torsionPairAlgebra` of finite étale `k`-algebras — i.e. by a
scheme morphism `E[N] ×_{Spec k} E[N] ⟶ μ_N` over `Spec k`. Over a **perfect** field the
algebraic closure is a separable closure (`IsSepClosure.of_isAlgClosure_of_perfectField`),
so the `AlgebraicClosure k`-fibres transport to the `SeparableClosure k`-fibre functor of
the Galois machinery along `IsSepClosure.equiv`; T-C0d feeds the equivariant field-level
Weil pairing (T-C0b/T-C0c) into this.

(Perfectness is used *only* for that transport. The statement is true over any field —
one would compare `Hom_k(A, k^sep)` with `Hom_k(A, k̄)` fibrewise instead of identifying
the two closures — but it genuinely fails when `char k ∣ N`, where `μ_N` has
infinitesimal structure invisible on geometric points.) -/
theorem exists_pairingAlgebraHom_of_galoisEquivariant (k : Type u) [Field k]
    [PerfectField k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0)
    (p : ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
          ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) →
        ((muNAlgebra k N hk).obj →ₐ[k] AlgebraicClosure k))
    (hp : ∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (x : ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
          ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k)),
      p (σ.toAlgHom.comp x.1, σ.toAlgHom.comp x.2) = σ.toAlgHom.comp (p x)) :
    ∃ w : muNAlgebra k N hk ⟶ torsionPairAlgebra k E N hk,
      ∀ f : ((torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k),
        f.comp w.hom.hom = p (torsionPairAlgebraPointsEquiv k E N hk f) := by
  -- comparison of the two geometric points (char 0: `k̄` is a separable closure)
  let e : SeparableClosure k ≃ₐ[k] AlgebraicClosure k :=
    IsSepClosure.equiv k (SeparableClosure k) (AlgebraicClosure k)
  -- transport `p` to the separable-closure fibres and descend it there
  obtain ⟨w, hw⟩ := exists_finiteEtaleHom_of_galoisEquivariant
    (muNAlgebra k N hk) (torsionPairAlgebra k E N hk)
    (fun x => e.symm.toAlgHom.comp
      (p (torsionPairAlgebraPointsEquiv k E N hk (e.toAlgHom.comp x))))
    (fun σ x => by
      -- conjugate `σ : Gal(k^sep/k)` to `σ̄ = e ∘ σ ∘ e⁻¹ : Gal(k̄/k)` and use `hp`
      have key : e.toAlgHom.comp (σ.toAlgHom.comp x) =
          ((e.symm.trans σ).trans e).toAlgHom.comp (e.toAlgHom.comp x) :=
        AlgHom.ext fun a => congrArg (fun t => e (σ t)) (e.symm_apply_apply (x a)).symm
      rw [key]
      have h2 := hp ((e.symm.trans σ).trans e)
        (torsionPairAlgebraPointsEquiv k E N hk (e.toAlgHom.comp x))
      -- the fibre splitting commutes with postcomposition (definitionally)
      have h3 : torsionPairAlgebraPointsEquiv k E N hk
          (((e.symm.trans σ).trans e).toAlgHom.comp (e.toAlgHom.comp x)) =
          (((e.symm.trans σ).trans e).toAlgHom.comp
            (torsionPairAlgebraPointsEquiv k E N hk (e.toAlgHom.comp x)).1,
          ((e.symm.trans σ).trans e).toAlgHom.comp
            (torsionPairAlgebraPointsEquiv k E N hk (e.toAlgHom.comp x)).2) := rfl
      rw [h3, h2]
      exact AlgHom.ext fun a => e.symm_apply_apply _)
  refine ⟨w, fun f => ?_⟩
  -- specialise the fibre equation at `e⁻¹ ∘ f` and cancel the comparison `e`
  have hx := hw (e.symm.toAlgHom.comp f)
  have h1 : e.toAlgHom.comp (e.symm.toAlgHom.comp f) = f :=
    AlgHom.ext fun a => e.apply_symm_apply (f a)
  rw [h1] at hx
  have h2 : (e.symm.toAlgHom.comp f).comp w.hom.hom =
      e.symm.toAlgHom.comp (f.comp w.hom.hom) := rfl
  rw [h2] at hx
  exact AlgHom.ext fun a => (e.symm.injective (AlgHom.congr_fun hx a)).symm

-- **(T-C0e, re-cut v9.4 — see the module docstring)** The DS4 Weil pairing of record is the
-- `T`-relative morphism `weilPairingCharZero : E[N] ×_T E[N] ⟶ μ_{N,T}` over `Spec ℚ`-schemes,
-- NOT a field-base statement. The earlier placeholder `exists_weilPairingSpecField` was removed:
-- its "morphism over the base" constraint was satisfiable by a trivial section, so it captured
-- neither the field-valued-points pairing (that is `exists_pairingAlgebraHom_of_galoisEquivariant`,
-- proven above) nor the moduli pairing. The `T`-relative construction (étale-local trivialisation
-- of `E[N]` + finite-flat descent of the morphism) funnels through T-W7 and is board ticket T-C0e.

end EllipticCurve

end ModularCurves
