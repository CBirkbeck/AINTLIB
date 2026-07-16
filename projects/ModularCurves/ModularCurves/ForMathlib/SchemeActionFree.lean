/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.InvariantTorsor
import ModularCurves.ForMathlib.SchemeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Geometric freeness ⟹ algebraic freeness (the T-Q2 bridge)

`ForMathlib/InvariantTorsor.lean` proves the Katz–Mazur A7.1.1 package (finite, unramified,
étale, torsor, base change) from `IsFreeAlgebraAction G R A` — KM's *"for any non-zero
`R`-algebra `R'`, and any `g ≠ 1`, `g` operates without fixed points on
`Hom_{R-alg}(A, R')`"*.

`ForMathlib/SchemeQuotient.lean` proves the quotient `X/G` from a *geometric* freeness
statement: no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`.

This file is the bridge: on a `G`-stable **affine** open, geometric freeness gives
`IsFreeAlgebraAction` on the section ring. It is the input that turns the local quotient
`V ⟶ Spec Γ(X,V)ᴳ` into a finite étale `G`-torsor.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

namespace SchemeAction

variable {G : Type*} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

/-- **(T-Q2 bridge)** If no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`, then on every
`G`-stable affine open `U` the induced action on the section ring `Γ(X, U)` is free in the sense
of Katz–Mazur A7.1.1 (`IsFreeAlgebraAction`).

Given a ring point `φ : Γ(X, U) →ₐ[ℤ] R'` with `R'` nontrivial and
`φ ∘ (γ • ·) = φ`, the morphism `t : Spec R' ⟶ Spec Γ(X, U) ≅ U ↪ X` is `γ`-fixed
(`specSMul_isoSpec_inv` is exactly the statement that `Spec` of the ring action *is* the
restricted geometric action), so `Spec R'` is empty — impossible, since a nontrivial ring
has a prime ideal. -/
theorem isFreeAlgebraAction_of_free {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    IsFreeAlgebraAction G ℤ ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  intro γ hγ R' _ _ _ φ
  by_contra hcon
  push Not at hcon
  -- `φ` is `γ`-invariant, hence `Spec φ` equalises the action
  have hring : (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom φ.toRingHom := by
    ext a
    exact hcon a
  have hspec : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specSMul γ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) = _
    rw [← Spec.map_comp, hring]
  -- the resulting point of `X` is `γ`-fixed
  set t : Spec (CommRingCat.of R') ⟶ X :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hUa.isoSpec.inv ≫ U.ι with ht
  have h1 : U.ι ≫ σ.hom γ = (σ.hom γ).resLE U U (hU.le_preimage γ) ≫ U.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have h2 : hUa.isoSpec.inv ≫ (σ.hom γ).resLE U U (hU.le_preimage γ) =
      specSMul γ ≫ hUa.isoSpec.inv := (specSMul_isoSpec_inv σ hU hUa γ).symm
  have hfix : t ≫ σ.hom γ = t := by
    rw [ht]
    simp only [Category.assoc]
    rw [h1, ← Category.assoc hUa.isoSpec.inv, h2, Category.assoc,
      ← Category.assoc (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specSMul γ), hspec]
  -- but `Spec R'` is nonempty
  haveI hE : IsEmpty (Spec (CommRingCat.of R')) := hfree γ hγ _ t hfix
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
  exact hE.false p

/-- **(T-Q2 on a chart)** On a `G`-stable affine open of a scheme with a free `G`-action, the
section ring is a finite module over its invariants (KM A7.1.1, finiteness part). -/
theorem finite_gamma_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  exact Module.Finite.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)

/-- **(T-Q2 on a chart)** The torsor identity `Γ(X,U) ⊗_{Γ(X,U)ᴳ} Γ(X,U) ≅ ∏_G Γ(X,U)`
(KM A7.1.1, torsor part; SGA III Exp. V 4.1 (iv)) holds on every `G`-stable affine open of a
scheme with a free `G`-action. Geometrically: `U ⟶ U/G` is a `G`-torsor. -/
theorem torsorMul_bijective_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Function.Bijective (MulSemiringAction.torsorMul G ℤ (↑Γ(X, U))) := by
  letI := σ.gammaMulSemiringAction hU
  exact torsorMul_bijective_of_isFreeAlgebraAction G ℤ _
    (σ.isFreeAlgebraAction_of_free hU hUa hfree)

section Quotient

variable [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
    t ≫ σ.hom γ = t → IsEmpty T)

include hfree in
set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-Q2, geometric)** For a **free** action, the quotient projection `X ⟶ X/G` is a **finite**
morphism.

`IsFinite` is Zariski-local at the target, the quotient charts cover `X/G`, and over the `x`-th
chart the projection *is* `V x ⟶ Spec Γ(X, V x)ᴳ` (`morphismRestrict_quotientπ`), i.e. `Spec`
of `Γ(X,V x)ᴳ ↪ Γ(X,V x)`, which is module-finite by `finite_gamma_of_free` (KM A7.1.1). -/
theorem isFinite_quotientπ : IsFinite (σ.quotientπ V hVs hVa hVmem) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) (σ.quotientChart V hVs hVa)
    (σ.iSup_quotientChart_eq_top V hVs hVa) fun x => ?_
  rw [morphismRestrict_quotientπ σ V hVs hVa hVmem x,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite),
    localQuotientπ_eq σ (hVs x) (hVa x),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)]
  letI := σ.gammaMulSemiringAction (hVs x)
  haveI := σ.finite_gamma_of_free (hVs x) (hVa x) hfree
  rw [invariantsπ, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

include hfree in
set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-Q2, geometric)** For a **free** action, the quotient projection `X ⟶ X/G` is **étale**.

Same local-to-global argument, with `Algebra.Etale.of_isFreeAlgebraAction` (KM A7.1.1, general
base — the [A711-FP] gap having been closed) at the chart level. -/
theorem etale_quotientπ : Etale (σ.quotientπ V hVs hVa hVmem) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) (σ.quotientChart V hVs hVa)
    (σ.iSup_quotientChart_eq_top V hVs hVa) fun x => ?_
  rw [morphismRestrict_quotientπ σ V hVs hVa hVmem x,
    MorphismProperty.cancel_left_of_respectsIso (P := @Etale),
    MorphismProperty.cancel_right_of_respectsIso (P := @Etale),
    localQuotientπ_eq σ (hVs x) (hVa x),
    MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]
  letI := σ.gammaMulSemiringAction (hVs x)
  haveI : Algebra.Etale (FixedPoints.subalgebra ℤ (↑Γ(X, V x)) G) ↑Γ(X, V x) :=
    Algebra.Etale.of_isFreeAlgebraAction G ℤ _
      (σ.isFreeAlgebraAction_of_free (hVs x) (hVa x) hfree)
  rw [invariantsπ, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

omit [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- **(T-Q2, geometric)** For a **free** action, `localQuotientπ : ↥U ⟶ Spec Γ(X,U)ᴳ` is an
**epimorphism** — it is an fppf cover (finite étale surjection = flat + surjective). Used to
cancel `localQuotientπ` when identifying the descended structure map with the invariant quotient
map on a chart (`[a3-ii]`). -/
theorem epi_localQuotientπ {U : X.Opens} (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    Epi (σ.localQuotientπ hU hUa) := by
  letI := σ.gammaMulSemiringAction hU
  haveI : Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Finite.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)
  haveI : Module.Projective (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Projective.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)
  haveI : Module.Flat (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Flat.of_projective
  haveI : Flat (invariantsπ G (↑Γ(X, U)) ℤ) := by
    rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  haveI : Surjective (invariantsπ G (↑Γ(X, U)) ℤ) := ⟨invariantsπ_surjective G _ ℤ⟩
  haveI : Epi (invariantsπ G (↑Γ(X, U)) ℤ) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  rw [SchemeAction.localQuotientπ_eq]
  infer_instance

end Quotient

end SchemeAction

variable {G : Type u} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]

/-- **The invariants morphism of a free action is an fppf cover**: `Spec B ⟶ Spec Bᴳ` is
surjective, flat and quasi-compact (indeed finite locally free). Abstracts the body of
`epi_localQuotientπ` for reuse in the `[a5-P-fppf]` comparison
(`isIso_of_isPullback_of_fppf`). -/
theorem fppf_invariantsπ [Finite G] (hfree : IsFreeAlgebraAction G ℤ B) :
    Surjective (invariantsπ G B ℤ) ∧ Flat (invariantsπ G B ℤ)
      ∧ QuasiCompact (invariantsπ G B ℤ) := by
  haveI : Module.Finite (FixedPoints.subalgebra ℤ B G) B :=
    Module.Finite.of_isFreeAlgebraAction G ℤ _ hfree
  haveI : Module.Projective (FixedPoints.subalgebra ℤ B G) B :=
    Module.Projective.of_isFreeAlgebraAction G ℤ _ hfree
  haveI : Module.Flat (FixedPoints.subalgebra ℤ B G) B := Module.Flat.of_projective
  refine ⟨⟨invariantsπ_surjective G B ℤ⟩, ?_, ?_⟩
  · rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [invariantsπ]
    infer_instance

end AlgebraicGeometry
