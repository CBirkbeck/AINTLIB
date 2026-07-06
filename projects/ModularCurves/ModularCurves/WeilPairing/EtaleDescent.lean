import ModularCurves.WeilPairing.Basic
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.FiniteEtaleGalois

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
* `weilPairingEtale` (T-C0d): the pairing as a morphism
  `torsionAlgebra ⊗ torsionAlgebra ⟶ muNAlgebra` in `CommAlgCat.FiniteEtale k`,
  transported through the Galois equivalence from T-C0b/T-C0c.
* `weilPairingSpecField` (T-C0e): the scheme-level pairing
  `E[N] ×_S E[N] ⟶ μ_N` over `S = Spec k`, `k` a char-0 field — the field-base
  discharge of the DS4 data. The general ℚ-scheme discharge additionally needs the
  étale-trivialisation tower (T-H4-adjacent); that edge is recorded on the board,
  and the `YRho` consumer (over `AlgebraicClosure ℚ`) is served by the field case.

Everything here consumes the registered T-B4/T-B5 finiteness/étaleness boxes
(`torsionπ_isFinite`/`torsionπ_etale`); axiom profiles record `sorryAx` through
those gates until the boxes are discharged.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

/-- **(T-C0a)** The `N`-torsion of an elliptic curve over a field, as a finite étale
`k`-algebra: `E[N] → Spec k` is finite (T-B4 box) hence affine, and étale when `N` is
invertible (T-B5 box); its global sections carry the corresponding
`CommAlgCat.FiniteEtale k` structure. -/
noncomputable def torsionAlgebra (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k := by
  -- `E[N] → Spec k` is finite (T-B4 box), hence an affine morphism with affine source.
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  -- Global sections of `E[N]` as a `k`-algebra, through `k ≅ Γ(Spec k, ⊤)`.
  letI : Algebra k Γ(E.torsion N, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom.toAlgebra
  -- Finiteness of the algebra, from finiteness of `torsionπ`.
  haveI : Module.Finite k Γ(E.torsion N, ⊤) := by
    have h : RingHom.Finite
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr
        ((E.torsionπ N).finite_app ⊤ (isAffineOpen_top _))
    exact h
  -- Étaleness of the algebra, from étaleness of `torsionπ` (T-B5 box, `N` invertible).
  haveI : Algebra.Etale k Γ(E.torsion N, ⊤) := by
    have het : Etale (E.torsionπ N) :=
      E.torsionπ_etale N ((nIsInvertible_spec_iff k N).mpr hk)
    have h : RingHom.Etale
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).mpr
        ((HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).mp het)
    exact h
  exact CommAlgCat.FiniteEtale.of k Γ(E.torsion N, ⊤)

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
  sorry

/-- **(T-C0e)** The étale-descent Weil pairing over a characteristic-zero field base:
the scheme-level pairing morphism with the same API as the DS4 register entry
(`weilPairing`), constructed by Galois descent of the HasseWeil field-level pairing.
Field-base discharge of DS4; the general ℚ-scheme case is the recorded follow-up. -/
theorem exists_weilPairingSpecField (k : Type u) [Field k] [CharZero k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] :
    ∃ w : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN (Spec (CommRingCat.of k)) N,
      w ≫ muNπ _ N = pullback.fst _ _ ≫ E.torsionπ N := by sorry

end EllipticCurve

end ModularCurves
