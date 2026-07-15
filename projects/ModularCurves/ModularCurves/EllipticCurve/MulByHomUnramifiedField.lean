/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.MulByHomFlatFibre
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# BB-DIFF fibre leg: `[N]` on the model over a field is formally unramified

The exact `FormallyUnramified` mirror of the BB-FLAT fibre leg (`MulByHomFlatFibre`):

* `modelMulByHom_formallyUnramified_of_field` — **the single mathematical leaf of
  BB-DIFF** (Loeffler 3.4.2(2) over a field, = Silverman III.5.4 separability of `[N]`
  when `(N : k) ≠ 0`, geometrised). Currently `sorry`; everything else in the BB-DIFF
  chain (`formallyUnramified_torsionπ` → `mulByHom_formallyUnramified` → `mulBy_etale` /
  `torsionπ_etale`) is discharged from it.
* `formallyUnramified_mulByHom_of_isMonHom_iso` — transport across a pointed group-object
  iso (verbatim mirror of `flat_mulByHom_of_isMonHom_iso`).
* `formallyUnramified_mulByHom_baseChange_residueField` — the fibre input at residue
  points of an arbitrary base, from the leaf via `fibrewiseElliptic`/`fibreModelIsoAsOver`
  (verbatim mirror of `flat_mulByHom_baseChange_residueField`, with the `N`-invertibility
  hypothesis threaded through the residue field).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve WeierstrassCurve

section FieldLevelUnramified

variable {k : Type u} [Field k]

/-- **(BB-DIFF field leaf, geometric case — THE residual)** Over an algebraically
closed field `κ` in which `N` is invertible, `[N]` on the projective model is formally
unramified. Route of record: `[N]` is separable (HasseWeil `mulByInt_isSeparable`, `[N]`
multiplies the invariant differential by `N ≠ 0`), so it is unramified at the generic
point; the unramified locus is open and stable under translation by `E(κ)`, which acts
transitively on closed points, so it is everything. -/
theorem modelMulByHom_formallyUnramified_of_isAlgClosed {κ : Type u} [Field κ]
    [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : (N : κ) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
  sorry

end FieldLevelUnramified

section UnramifiedIsoTransport

variable {S : Scheme.{u}}

/-- **(Unramified transport across a group-object iso)** If `φ : E ≅ F` as group objects
over `S` (`IsMonHom`), formal unramifiedness of `[n]` transports from `F` to `E`:
`[n]_E` is the conjugate `φ ≫ [n]_F ≫ φ⁻¹`. -/
theorem formallyUnramified_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    (hF : FormallyUnramified (F.mulByHom n)) : FormallyUnramified (E.mulByHom n) := by
  -- ascribe the underlying scheme morphisms to the `.E`-types (defeq)
  let ψ : E.E ⟶ F.E := φ.hom.left
  let ψ' : F.E ⟶ E.E := φ.inv.left
  have hc : E.mulByHom n ≫ ψ = ψ ≫ F.mulByHom n :=
    mulByHom_comp_left_of_isMonHom E F φ.hom n
  have hinv : ψ ≫ ψ' = 𝟙 E.E := by
    show φ.hom.left ≫ φ.inv.left = 𝟙 _
    rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
  have hinv' : ψ' ≫ ψ = 𝟙 F.E := by
    show φ.inv.left ≫ φ.hom.left = 𝟙 _
    rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  let eIso : E.E ≅ F.E := ⟨ψ, ψ', hinv, hinv'⟩
  exact (MorphismProperty.arrow_mk_iso_iff (P := @FormallyUnramified)
    (Arrow.isoMk eIso eIso hc.symm)).mpr hF

end UnramifiedIsoTransport

section FieldLevelKbarWiring

variable {k : Type u} [Field k]

/-- **(BB-DIFF fibre leg — the field-level leaf, T-B5 = Loeffler 3.4.2(2) over a field)**
Over ANY field `k` in which `N` is invertible, multiplication by `N` on the projective
model of an elliptic Weierstrass curve is **formally unramified**: base-change to the
algebraic closure `κ̄` (the geometric case), transport across the pointed group-object
iso `modelBaseChangeIsoAsOver`, and fppf-descend along `Spec κ̄ → Spec k` using the
mathlib `DescendsAlong @FormallyUnramified` instance on the `[N]` base-change square —
the exact `@LocallyQuasiFinite` κ̄-wiring of `modelMulByHom_locallyQuasiFinite_of_field`. -/
theorem modelMulByHom_formallyUnramified_of_field (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
  set κ := AlgebraicClosure k
  set fc : CommRingCat.of k ⟶ CommRingCat.of κ := CommRingCat.ofHom (algebraMap k κ)
    with hfc
  have hNκ : (N : κ) ≠ 0 := by
    intro h0
    apply hN
    have : algebraMap k κ (N : k) = 0 := by rw [map_natCast, h0]
    exact (map_eq_zero _).mp this
  -- (1) the geometric case over the algebraic closure
  haveI h1 : FormallyUnramified
      ((modelEllipticCurve (W.map (algebraMap k κ))).mulByHom (N : ℤ)) :=
    modelMulByHom_formallyUnramified_of_isAlgClosed (W.map (algebraMap k κ)) N hNκ
  -- (2) transport across the pointed group-object iso to the base-changed record
  obtain ⟨φ, hφ⟩ := modelBaseChangeIsoAsOver W κ
  haveI := hφ
  haveI h2 : FormallyUnramified
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ)) :=
    formallyUnramified_mulByHom_of_isMonHom_iso φ (N : ℤ) h1
  -- (3) the `[N]` base-change square, by cancelling the π-square off the big rectangle
  have hcomm : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ) ≫
        pullback.fst (modelEllipticCurve W).π (Spec.map fc)
      = pullback.fst (modelEllipticCurve W).π (Spec.map fc) ≫
        (modelEllipticCurve W).mulByHom (N : ℤ) :=
    mulByHom_baseChange_fst (modelEllipticCurve W) (Spec.map fc) (N : ℤ)
  have hsq : IsPullback
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ))
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
    refine IsPullback.of_right ?_ hcomm
      ((IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip)
    have e1 : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ) ≫
          pullback.snd (modelEllipticCurve W).π (Spec.map fc)
        = pullback.snd (modelEllipticCurve W).π (Spec.map fc) :=
      mulByHom_π ((modelEllipticCurve W).baseChange (Spec.map fc)) (N : ℤ)
    have e2 : (modelEllipticCurve W).mulByHom (N : ℤ) ≫ (modelEllipticCurve W).π
        = (modelEllipticCurve W).π :=
      mulByHom_π (modelEllipticCurve W) (N : ℤ)
    rw [e1, e2]
    exact (IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip
  -- (4) the descent leg `Spec κ̄ → Spec k` is fppf
  haveI hSurjSpec : Surjective (Spec.map fc) := by
    refine ⟨fun y => ?_⟩
    haveI hsing : Subsingleton (↥(Spec (CommRingCat.of k))) :=
      ⟨fun a b => PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
        (Ideal.eq_bot_of_prime _).symm)⟩
    obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of κ)) := inferInstance
    exact ⟨x, Subsingleton.elim _ _⟩
  haveI hFlatSpec : Flat (Spec.map fc) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap k κ).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  haveI hQCSpec : QuasiCompact (Spec.map fc) := inferInstance
  -- (5) descend
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq
    ⟨⟨MorphismProperty.pullback_fst _ _ hSurjSpec,
      MorphismProperty.pullback_fst _ _ hFlatSpec⟩,
      MorphismProperty.pullback_fst _ _ hQCSpec⟩ h2

end FieldLevelKbarWiring

section UnramifiedTransport

variable {S : Scheme.{u}}

/-- **(BB-DIFF fibre input at residue points)** `[N]` on the fibre curve
`E ×_S Spec κ(s)` is formally unramified when `N ≠ 0` in `κ(s)`: the fibre is
pointed-isomorphic to a projective Weierstrass model over `κ(s)`
(`fibreModelIsoAsOver`), whose `[N]` is formally unramified by the field-level leaf. -/
theorem formallyUnramified_mulByHom_baseChange_residueField (E : EllipticCurve S)
    (N : ℕ) [NeZero N] (s : S) (hN : (N : S.residueField s) ≠ 0) :
    FormallyUnramified ((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) := by
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  exact formallyUnramified_mulByHom_of_isMonHom_iso φ (N : ℤ)
    (modelMulByHom_formallyUnramified_of_field W N hN)

end UnramifiedTransport

end ModularCurves
