/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.EtaleDescent

/-!
# The Galois action on geometric fibres of an affine scheme over a field (DS4 M1c step 2)

`algHomEquivSpecOver` (`WeilPairing/EtaleDescent.lean`) identifies the fibre-functor value
`Γ(X, ⊤) →ₐ[k] R` of an affine `k`-scheme with its `Spec R`-points over `Spec k`. The DS4
descent input `exists_pairingAlgebraHom_of_galoisEquivariant` asks for equivariance of a
pairing for the `Gal(k̄/k)`-action on the *algebra* side, i.e. **postcomposition**
`f ↦ σ ∘ f`; the geometric side sees this as **precomposition** with `Spec σ`:

    algHomEquivSpecOver (σ ∘ f) = Spec.map σ ≫ algHomEquivSpecOver f.

That is the content of this file — a one-line consequence of the contravariance of `Spec`,
recorded because every later comparison (torsion points, `μ_N`-points, the Weil pairing)
factors through it.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

/-- **(DS4 M1c step 2 ★)** The `Gal(R/k)`-action on the fibre `Γ(X, ⊤) →ₐ[k] R`, which is
postcomposition by `σ`, becomes **precomposition with `Spec σ`** on the `Spec R`-points. -/
theorem algHomEquivSpecOver_comp_algEquiv {k : Type u} [Field k] (R : Type u) [CommRing R]
    [Algebra k R] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of k))
    [Algebra k Γ(X, ⊤)]
    (halg : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop)
    (σ : R ≃ₐ[k] R) (f : Γ(X, ⊤) →ₐ[k] R) :
    ((algHomEquivSpecOver R π halg (σ.toAlgHom.comp f)).1 :
        Spec (CommRingCat.of R) ⟶ X) =
      Spec.map (CommRingCat.ofHom (σ : R →+* R)) ≫
        ((algHomEquivSpecOver R π halg f).1 : Spec (CommRingCat.of R) ⟶ X) := by
  show Spec.map (CommRingCat.ofHom ((σ.toAlgHom.comp f).toRingHom) :
      Γ(X, ⊤) ⟶ CommRingCat.of R) ≫ X.isoSpec.inv = _
  rw [show (CommRingCat.ofHom ((σ.toAlgHom.comp f).toRingHom) :
        Γ(X, ⊤) ⟶ CommRingCat.of R) =
      (CommRingCat.ofHom (f.toRingHom) : Γ(X, ⊤) ⟶ CommRingCat.of R) ≫
        CommRingCat.ofHom (σ : R →+* R) from rfl,
    Spec.map_comp, Category.assoc]
  rfl

namespace EllipticCurve

/-- **(DS4 M1c step 1 ★)** The fibre-functor value of `torsionAlgebra` as a **named**
equivalence (the existing `torsionAlgebraPointsEquiv` is only `Nonempty`-valued, so no
equivariance statement can be made about it), and for an arbitrary field-extension target
`R`: `R`-points of `E[N]` are the `N`-torsion of `E(R)`. -/
noncomputable def torsionAlgebraFibreEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) (R : Type u) [CommRing R] [Algebra k R] :
    ((torsionAlgebra k E N hk).obj →ₐ[k] R) ≃
      Submodule.torsionBy ℤ
        (E.Point (Spec.map (CommRingCat.ofHom (algebraMap k R)))) (N : ℤ) :=
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  letI : Algebra k Γ(E.torsion N, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom.toAlgebra
  (algHomEquivSpecOver (k := k) R (E.torsionπ N) rfl).trans
    (E.torsionPointsEquiv N (Spec.map (CommRingCat.ofHom (algebraMap k R))))

/-- The underlying section of `torsionAlgebraFibreEquiv f` is, on the nose, the composite of
the `Spec`-transport of `f` with the torsion inclusion. -/
theorem torsionAlgebraFibreEquiv_coe (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) (R : Type u) [CommRing R] [Algebra k R]
    (f : (torsionAlgebra k E N hk).obj →ₐ[k] R) :
    letI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
    letI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
    letI : Algebra k Γ(E.torsion N, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom.toAlgebra
    (((torsionAlgebraFibreEquiv k E N hk R f : Submodule.torsionBy ℤ _ (N : ℤ)) :
        E.Point (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
      Spec (CommRingCat.of R) ⟶ E.E) =
      ((algHomEquivSpecOver (k := k) R (E.torsionπ N) rfl f).1 :
        Spec (CommRingCat.of R) ⟶ E.torsion N) ≫ E.torsionι N := rfl

/-- **(DS4 M1c step 3 ★)** Galois equivariance of the torsion fibre dictionary: the
algebra-side action `f ↦ σ ∘ f` corresponds to precomposition with `Spec σ` on the
represented section. -/
theorem torsionAlgebraFibreEquiv_comp_algEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) (R : Type u) [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R)
    (f : (torsionAlgebra k E N hk).obj →ₐ[k] R) :
    (((torsionAlgebraFibreEquiv k E N hk R (σ.toAlgHom.comp f) :
          Submodule.torsionBy ℤ _ (N : ℤ)) :
        E.Point (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
      Spec (CommRingCat.of R) ⟶ E.E) =
      Spec.map (CommRingCat.ofHom (σ : R →+* R)) ≫
        (((torsionAlgebraFibreEquiv k E N hk R f : Submodule.torsionBy ℤ _ (N : ℤ)) :
            E.Point (Spec.map (CommRingCat.ofHom (algebraMap k R)))) :
          Spec (CommRingCat.of R) ⟶ E.E) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  letI : Algebra k Γ(E.torsion N, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom.toAlgebra
  show ((algHomEquivSpecOver (k := k) R (E.torsionπ N) rfl (σ.toAlgHom.comp f)).1 :
      Spec (CommRingCat.of R) ⟶ E.torsion N) ≫ E.torsionι N = _
  rw [algHomEquivSpecOver_comp_algEquiv R (E.torsionπ N) rfl σ f, Category.assoc]
  rfl

end EllipticCurve

end ModularCurves
