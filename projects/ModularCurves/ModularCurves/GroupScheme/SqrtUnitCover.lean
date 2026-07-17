/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The square-root cover of a unit (the `u² = d` finite étale double cover)

The pure-geometry layer of the `±ω` scale-torsor (CHARTER-G, (G1)): for a unit `d` of
a ring `A`, the standard étale pair `(X² − d, 2d)` presents the double cover
`A[u]/(u² − d)` (the `2d`-localization is trivial once `2` and `d` are invertible).
Mathlib's `StandardEtalePair` machinery gives étaleness and the universal property
(`homEquiv`) for free; here we add finiteness (rank 2, via `AdjoinRoot` freeness) and
the `x² = d` form of the point spec.

* `sqrtPair d` — the standard étale pair `(X² − C d, C (2d))`.
* `sqrtPair_hasMap_iff` — mapping `X ↦ x` exists iff `x² = d` (once `2` is a unit in
  the target).
* `sqrtPairCongr` — the twist `X ↦ c⁻¹X` identifying the `d`-cover with the
  `c²d`-cover: the gluing ingredient for the twisted (line-bundle-valued) case.
-/

open Polynomial

noncomputable section

namespace ModularCurves

variable {A : Type*} [CommRing A]

/-- The standard étale pair `(X² − d, 2d)` of a unit `d`: the presentation of the
square-root double cover. The pair condition is the identity
`(2X)·X + (X² − d)·(−2) = 2d`. -/
def sqrtPair (d : Aˣ) : StandardEtalePair A where
  f := X ^ 2 - C (d : A)
  monic_f := (monic_X_pow_sub_C (d : A) two_ne_zero)
  g := C ((2 : A) * d)
  cond := by
    refine ⟨X, -2, 1, ?_⟩
    have hder : derivative (X ^ 2 - C (d : A)) = 2 * X := by
      simp [derivative_sub]
      ring
    rw [hder, C_mul, map_ofNat]
    ring

/-- Mapping the coordinate to `x : S` is possible iff `x² = d` — the `2d`-invertibility
conjunct is automatic when `2` is a unit in `S` (the image of the unit `d` always is). -/
theorem sqrtPair_hasMap_iff {S : Type*} [CommRing S] [Algebra A S]
    (d : Aˣ) (h2 : IsUnit (2 : S)) (x : S) :
    (sqrtPair d).HasMap x ↔ x ^ 2 = algebraMap A S (d : A) := by
  constructor
  · rintro ⟨h1, -⟩
    have := h1
    rw [show (sqrtPair d).f = X ^ 2 - C (d : A) from rfl] at this
    simpa [sub_eq_zero] using this
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [show (sqrtPair d).f = X ^ 2 - C (d : A) from rfl]
      simpa [sub_eq_zero] using hx
    · rw [show (sqrtPair d).g = C ((2 : A) * d) from rfl]
      rw [aeval_C, map_mul]
      refine IsUnit.mul ?_ (d.isUnit.map (algebraMap A S))
      rw [map_ofNat]
      exact h2

/-! ### Finiteness of the square-root cover -/

/-- The localization element of the `sqrtPair` presentation is a unit of
`AdjoinRoot (X² − d)` once `2` is a unit of `A`. -/
theorem sqrtPair_mk_g_isUnit (d : Aˣ) (h2 : IsUnit (2 : A)) :
    IsUnit (AdjoinRoot.mk (sqrtPair d).f (sqrtPair d).g) := by
  rw [show (sqrtPair d).g = C ((2 : A) * d) from rfl, AdjoinRoot.mk_C, map_mul]
  exact (h2.map _).mul (d.isUnit.map _)

/-- The square-root algebra is module-finite over the base once `2` is a unit:
through `equivAwayAdjoinRoot` it is the trivial localization of the rank-2 free
`AdjoinRoot (X² − d)`. -/
noncomputable def sqrtPairAdjoinRootEquiv (d : Aˣ) (h2 : IsUnit (2 : A)) :
    (sqrtPair d).Ring ≃ₐ[A] AdjoinRoot (sqrtPair d).f := by
  haveI hloc : IsLocalization
      (Submonoid.powers (AdjoinRoot.mk (sqrtPair d).f (sqrtPair d).g))
      (AdjoinRoot (sqrtPair d).f) :=
    IsLocalization.away_of_isUnit_of_bijective _ (sqrtPair_mk_g_isUnit d h2)
      Function.bijective_id
  exact (sqrtPair d).equivAwayAdjoinRoot.trans
    ((IsLocalization.algEquiv
      (Submonoid.powers (AdjoinRoot.mk (sqrtPair d).f (sqrtPair d).g))
      (AdjoinRoot (sqrtPair d).f)
      (Localization.Away (AdjoinRoot.mk (sqrtPair d).f (sqrtPair d).g))).restrictScalars
        A).symm

theorem sqrtPair_finite (d : Aˣ) (h2 : IsUnit (2 : A)) :
    Module.Finite A (sqrtPair d).Ring := by
  haveI hfin : Module.Finite A (AdjoinRoot (sqrtPair d).f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' (sqrtPair d).monic_f).basis
  exact Module.Finite.equiv (sqrtPairAdjoinRootEquiv d h2).symm.toLinearEquiv

/-! ### The scheme-level cover -/

section SchemeLevel

open AlgebraicGeometry CategoryTheory

universe u

/-- Morphisms of affine schemes over a common affine base are algebra
homomorphisms (the over-`Spec` form of `Spec`-full-faithfulness). -/
noncomputable def overSpecEquivAlgHom (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] :
    { s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B) //
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))
        = Spec.map (CommRingCat.ofHom (algebraMap A C)) } ≃ (B →ₐ[A] C) where
  toFun s :=
    { toRingHom := (Spec.preimage s.1).hom
      commutes' := fun a => by
        have hcomp : Spec.map (CommRingCat.ofHom
            ((Spec.preimage s.1).hom.comp (algebraMap A B)))
            = Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
          exact s.2
        have h := Spec.map_injective hcomp
        exact congrArg (fun (ψ : CommRingCat.of A ⟶ CommRingCat.of C) => ψ.hom a) h }
  invFun χ := ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact χ.commutes a⟩
  left_inv s := Subtype.ext (Spec.map_preimage s.1)
  right_inv χ := by
    ext b
    show (Spec.preimage (Spec.map (CommRingCat.ofHom χ.toRingHom))).hom b = χ b
    rw [Spec.preimage_map]
    rfl

variable {A : Type u} [CommRing A]

/-- The square-root cover as a morphism of affine schemes. -/
noncomputable def sqrtCoverπ (d : Aˣ) :
    Spec (CommRingCat.of (sqrtPair d).Ring) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (sqrtPair d).Ring))

/-- The square-root cover is étale (unconditionally — the ramified fibres are cut
out by the `2d`-localization inside the standard étale presentation). -/
theorem sqrtCoverπ_etale (d : Aˣ) : AlgebraicGeometry.Etale (sqrtCoverπ d) := by
  rw [sqrtCoverπ, HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  show RingHom.Etale (algebraMap A (sqrtPair d).Ring)
  rw [RingHom.etale_algebraMap]
  infer_instance

/-- The square-root cover is finite once `2` is a unit on the base. -/
theorem sqrtCoverπ_isFinite (d : Aˣ) (h2 : IsUnit (2 : A)) :
    AlgebraicGeometry.IsFinite (sqrtCoverπ d) := by
  rw [sqrtCoverπ, AlgebraicGeometry.IsFinite.SpecMap_iff]
  show RingHom.Finite (algebraMap A (sqrtPair d).Ring)
  haveI := sqrtPair_finite d h2
  rw [RingHom.finite_algebraMap]
  infer_instance

/-- **The point spec of the square-root cover**: sections over an `A`-algebra point
are the square roots of (the image of) `d`. -/
noncomputable def sqrtCoverSectionsEquiv (d : Aˣ) {C : Type u} [CommRing C]
    [Algebra A C] (h2C : IsUnit (2 : C)) :
    { s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (sqrtPair d).Ring) //
      s ≫ sqrtCoverπ d = Spec.map (CommRingCat.ofHom (algebraMap A C)) } ≃
      { x : C // x ^ 2 = algebraMap A C (d : A) } :=
  (overSpecEquivAlgHom A (sqrtPair d).Ring C).trans
    ((sqrtPair d).homEquiv.trans
      (Equiv.subtypeEquivRight (fun x => sqrtPair_hasMap_iff d h2C x)))

end SchemeLevel

end ModularCurves
