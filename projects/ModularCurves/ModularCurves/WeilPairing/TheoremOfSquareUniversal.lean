/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FibreWeierstrassPresentation
import ModularCurves.ForMathlib.SeesawGlobalBase

/-!
# The theorem of the square through the seesaw (B3-steps 2–4)

`WeilPairing/FibreWeierstrassPresentation.lean` proved the seesaw's fibrewise-triviality
binder for the theorem-of-the-square **discrepancy module**

  `Δ = (I(D_R) ⊗ I(D_Z)) ⊗ N`,     `N` a `⊗`-inverse of `I(D_P) ⊗ I(D_Q)`

with no hypotheses (`nonempty_pullback_discrepancy_iso_unitObj_projModel`). This file runs that
input through the seesaw and reads the output off along the zero section.

## Contents

* `HasHighCechExactness` / `HasHighCechExactnessOpens` — names for the seesaw's positive-degree
  ordered-base-Čech exactness binder, in its affine-base and arbitrary-base shapes.
* `isInvertible_discrepancy` — `Δ` is invertible, from
  `RelEffCartierDiv.sectionDivisor_isOfficial` and stability of `IsInvertible` under `⊗`.
* **(step 2)** `exists_pullback_iso_discrepancy` — the seesaw over an **arbitrary** reduced
  Noetherian base (`exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover`), which
  is the shape the universal pair of points needs: `C ×_S C` is integral but not affine;
  `exists_pullback_iso_discrepancy_of_isAffine` is the affine-base variant, whose `hhigh` binder
  is the simpler one.
* **(step 3)** `nonempty_discrepancy_iso_pullback_pullback_zero` — `Δ ≅ f^*(0^*Δ)`, i.e. the
  *rigidified* discrepancy is trivial (`Ker(0^*) ∩ Im(f^*) = 1`), and
  `nonempty_discrepancy_iso_unitObj` — `Δ` itself is trivial once `0^*Δ` is.
* `exists_invertible_tensor_idealModule_add_of_hfib` — the **consumer shape**
  `I(D_P) ⊗ I(D_Q) ≅ (I(D_R) ⊗ I(D_Z)) ⊗ f^*N₀`, i.e. the relative theorem of the square as
  `Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add` states it.
* `exists_pullback_iso_discrepancy_projModel`,
  `exists_invertible_tensor_idealModule_add_projModel` — the same two conclusions for the
  projective model `projModelπ W₀ : projModel W₀ ⟶ Spec A` of an elliptic Weierstrass curve over
  a **reduced Noetherian** ring, with `hfib` discharged; only `hhigh` remains.

## What is *not* here

`hhigh` (step 4) is left as a hypothesis throughout. It is exactness of the ordered base-Čech
complex in positive degrees, which for a relative curve should come from
`subsingleton_H_add_two_of_two_affine_open_cover` fed through
`HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology`
as in `kernel_data_of_hasDegreeOneFibreCohomology`. Note that the arbitrary-base seesaw quantifies
its `hhigh` over **all opens of the base**, including non-affine ones, while that machinery needs
an affine base — so the arbitrary-base form is not a direct instance of it. See the report on
ticket B3-steps2to4.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-! ### The positive-degree Čech exactness binders -/

/-- **The seesaw's `hhigh` over an affine base**: exactness of the ordered base-Čech complex of
`M` at every position `1 ≤ q < #ι`, for every finite affine open cover of the total space. The
cover is produced inside the seesaw's proof, so the hypothesis has to be uniform in it. -/
abbrev HasHighCechExactness {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules) : Prop :=
  ∀ {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → C.Opens), IsOpenCover U →
    (∀ i, IsAffineOpen (U i)) → ∀ q, 1 ≤ q → q < Fintype.card ι →
      Function.Exact ((orderedBaseCechComplex π M U).d q (q + 1)).hom
        ((orderedBaseCechComplex π M U).d (q + 1) (q + 2)).hom

/-- **The seesaw's `hhigh` over an arbitrary base**: `HasHighCechExactness` for the restriction
of the family to every open of the base. The base's own affine cover is likewise produced inside
the proof of `exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover`. -/
abbrev HasHighCechExactnessOpens {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules) : Prop :=
  ∀ W : S.Opens, HasHighCechExactness (π ∣_ W) (M.restrict (π ⁻¹ᵁ W).ι)

/-! ### `Ker(0^*) ∩ Im(f^*) = 1` -/

/-- Pulling a module back from the base and then restricting along a section returns the module:
`0^* f^* N ≅ N`, since `0 ≫ f = 𝟙`. -/
theorem nonempty_pullback_section_pullback_iso {C S : Scheme.{u}} {π : C ⟶ S} {Z : S ⟶ C}
    (hZ : Z ≫ π = 𝟙 S) (N : S.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback Z).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) ≅ N) :=
  ⟨(AlgebraicGeometry.Scheme.Modules.pullbackComp Z π).app N ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hZ).app N ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackId S).app N⟩

/-! ### The discrepancy module -/

/-- The theorem-of-the-square **discrepancy module** of a pair of sections `R`, `Z` twisted by
`N`: `Δ = (I(D_R) ⊗ I(D_Z)) ⊗ N`. In the intended application `R = P + Q`, `Z` is the zero
section and `N` is a `⊗`-inverse of `I(D_P) ⊗ I(D_Q)`, so `Δ` measures the failure of the
theorem of the square. -/
noncomputable abbrev discrepancy {C S : Scheme.{u}} (R Z : S ⟶ C) (N : C.Modules) : C.Modules :=
  tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
    (Scheme.Modules.idealModule (Scheme.Hom.ker Z))) N

/-- The discrepancy module of two sections of a separated smooth relative curve, twisted by an
invertible module, is invertible: each section divisor is an official relative Cartier divisor
(`RelEffCartierDiv.sectionDivisor_isOfficial`), hence its ideal module is invertible, and
`IsInvertible` is stable under `⊗`. -/
theorem isInvertible_discrepancy {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S)
    {N : C.Modules} (hN : IsInvertible N) : IsInvertible (discrepancy R Z N) :=
  ((AlgebraicGeometry.Scheme.Modules.isInvertible_idealModule _
      (RelEffCartierDiv.sectionDivisor_isOfficial hsm R hR).locallyPrincipal).tensorObj
    (AlgebraicGeometry.Scheme.Modules.isInvertible_idealModule _
      (RelEffCartierDiv.sectionDivisor_isOfficial hsm Z hZ).locallyPrincipal)).tensorObj hN

/-- A `⊗`-factor of the unit is invertible: this is how the seesaw's `IsInvertible` hypothesis on
the twist `N` is obtained from the trivialisation `(I(D_P) ⊗ I(D_Q)) ⊗ N ≅ 𝒪` alone. -/
theorem isInvertible_of_tensorObj_iso_unitObj {X : Scheme.{u}} {M N : X.Modules}
    (h : Nonempty (tensorObj M N ≅ unitObj X)) : IsInvertible N := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory X
  refine isInvertible_of_isUnit_toSkeleton (isUnit_of_dvd_one ⟨toSkeleton M, ?_⟩)
  rw [mul_comm, ← toSkeleton_tensorObj_eq]
  exact ((toSkeleton_eq_toSkeleton_iff.mpr h).trans toSkeleton_unitObj).symm

/-- Skeleton arithmetic behind the relative theorem of the square: from `A ⊗ N ≅ 𝒪`,
`B ⊗ N ≅ L` and `L ⊗ M ≅ 𝒪` one gets `A ≅ B ⊗ M`.

Pure commutative-monoid computation in the Picard skeleton — no cancellation is used:
`[A] = [A]·([B]·[N]·[M]) = ([A]·[N])·([B]·[M]) = [B]·[M]`. -/
theorem nonempty_iso_tensorObj_of_tensorObj_unitObj {X : Scheme.{u}} {A B N L M : X.Modules}
    (hA : Nonempty (tensorObj A N ≅ unitObj X)) (hB : Nonempty (tensorObj B N ≅ L))
    (hL : Nonempty (tensorObj L M ≅ unitObj X)) : Nonempty (A ≅ tensorObj B M) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory X
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  have ha : toSkeleton A * toSkeleton N = 1 :=
    (toSkeleton_tensorObj_eq A N).symm.trans
      ((toSkeleton_eq_toSkeleton_iff.mpr hA).trans toSkeleton_unitObj)
  have hb : toSkeleton B * toSkeleton N = toSkeleton L :=
    (toSkeleton_tensorObj_eq B N).symm.trans (toSkeleton_eq_toSkeleton_iff.mpr hB)
  have hl : toSkeleton L * toSkeleton M = 1 :=
    (toSkeleton_tensorObj_eq L M).symm.trans
      ((toSkeleton_eq_toSkeleton_iff.mpr hL).trans toSkeleton_unitObj)
  rw [toSkeleton_tensorObj_eq]
  calc toSkeleton A
      = toSkeleton A * (toSkeleton B * toSkeleton N * toSkeleton M) := by rw [hb, hl, mul_one]
    _ = toSkeleton A * toSkeleton N * (toSkeleton B * toSkeleton M) := by
          simp only [mul_assoc, mul_left_comm]
    _ = toSkeleton B * toSkeleton M := by rw [ha, one_mul]

/-- The pullback of a `⊗`-inverse pair is a `⊗`-inverse pair: `f^*M ⊗ f^*N ≅ 𝒪` whenever
`M ⊗ N ≅ 𝒪`. -/
theorem nonempty_pullback_tensorObj_iso_unitObj {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (h : Nonempty (tensorObj M N ≅ unitObj X)) :
    Nonempty (tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) ≅ unitObj Y) :=
  ⟨(nonempty_pullback_tensorObj f M N).some.symm ≪≫ (nonempty_pullback_iso_unitObj f h).some⟩

/-! ### Step 2: the seesaw applied to the discrepancy -/

/-- **[B3-step2] The discrepancy is pulled back from the base — arbitrary base.**

Over a *reduced* Noetherian base, for a proper flat family of finite presentation which is
universally `O`-connected and is a smooth relative curve, the discrepancy module
`Δ = (I(D_R) ⊗ I(D_Z)) ⊗ N` of two sections — trivial on every field-valued fibre (`hfib`) — is
the pullback of an invertible module from the base.

This is `exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover`
(`ForMathlib/SeesawGlobalBase.lean`) with its `IsInvertible` hypothesis supplied by
`isInvertible_discrepancy`. The base is **not** assumed affine, which is what the universal pair
of points needs: `C ×_S C` is integral but not affine. -/
theorem exists_pullback_iso_discrepancy {C S : Scheme.{u}} [IsReduced S] [IsNoetherian S]
    [IsNoetherian C] [C.IsSeparated] {π : C ⟶ S} [LocallyOfFinitePresentation π] [IsProper π]
    [Flat π] (hπ : UniversallyOConnected π) (hsm : SmoothOfRelativeDimension 1 π)
    {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S) {N : C.Modules} (hN : IsInvertible N)
    (hhigh : HasHighCechExactnessOpens π (discrepancy R Z N))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj (discrepancy R Z N) ≅ unitObj (Limits.pullback π x))) :
    ∃ N₀ : S.Modules, IsInvertible N₀ ∧
      Nonempty (discrepancy R Z N ≅
        (AlgebraicGeometry.Scheme.Modules.pullback π).obj N₀) :=
  exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover hπ
    (isInvertible_discrepancy hsm hR hZ hN) hhigh hfib

/-- **[B3-step2] The discrepancy is pulled back from the base — affine base.**

The same conclusion through `exists_pullback_iso_of_fibrewise_trivial_of_isReduced`
(`ForMathlib/Seesaw.lean`), whose `hhigh` binder mentions only the total space; this is the form
in which the positive-degree exactness is actually provable by the Čech-surrogate machinery of
`Picard/`, which needs an affine base. -/
theorem exists_pullback_iso_discrepancy_of_isAffine {C S : Scheme.{u}} [IsAffine S] [IsReduced S]
    [IsNoetherian S] [IsNoetherian C] [C.IsSeparated] {π : C ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π] (hπ : UniversallyOConnected π)
    (hsm : SmoothOfRelativeDimension 1 π) {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S)
    {N : C.Modules} (hN : IsInvertible N)
    (hhigh : HasHighCechExactness π (discrepancy R Z N))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj (discrepancy R Z N) ≅ unitObj (Limits.pullback π x))) :
    ∃ N₀ : S.Modules, IsInvertible N₀ ∧
      Nonempty (discrepancy R Z N ≅
        (AlgebraicGeometry.Scheme.Modules.pullback π).obj N₀) :=
  exists_pullback_iso_of_fibrewise_trivial_of_isReduced hπ
    (isInvertible_discrepancy hsm hR hZ hN) hhigh hfib

/-! ### Step 3: rigidification along the zero section -/

/-- **[B3-step3] The discrepancy is pulled back from its own restriction along the zero
section.**

`Ker(0^*) ∩ Im(f^*) = 1`: step 2 gives `Δ ≅ f^*N₀`, and restricting along a section `Z` of `f`
identifies `N₀` with `0^*Δ`, because `0^*f^* = (f ∘ 0)^* = id`. So the *rigidified* discrepancy
`Δ ⊗ f^*(0^*Δ)⁻¹` is trivial, and `Δ` itself is trivial as soon as `0^*Δ` is. -/
theorem nonempty_discrepancy_iso_pullback_pullback_zero {C S : Scheme.{u}} [IsReduced S]
    [IsNoetherian S] [IsNoetherian C] [C.IsSeparated] {π : C ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π] (hπ : UniversallyOConnected π)
    (hsm : SmoothOfRelativeDimension 1 π) {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S)
    {N : C.Modules} (hN : IsInvertible N)
    (hhigh : HasHighCechExactnessOpens π (discrepancy R Z N))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj (discrepancy R Z N) ≅ unitObj (Limits.pullback π x))) :
    Nonempty (discrepancy R Z N ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Z).obj (discrepancy R Z N))) := by
  obtain ⟨N₀, -, ⟨e⟩⟩ := exists_pullback_iso_discrepancy hπ hsm hR hZ hN hhigh hfib
  obtain ⟨e₀⟩ := nonempty_pullback_section_pullback_iso hZ N₀
  exact ⟨e ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback π).mapIso
    (((AlgebraicGeometry.Scheme.Modules.pullback Z).mapIso e ≪≫ e₀).symm)⟩

/-- **[B3-step3, trivial form]** If the restriction of the discrepancy along the zero section is
trivial, so is the discrepancy itself — the statement "`Δ` is trivial" in the shape a consumer of
the relative theorem of the square uses. -/
theorem nonempty_discrepancy_iso_unitObj {C S : Scheme.{u}} [IsReduced S] [IsNoetherian S]
    [IsNoetherian C] [C.IsSeparated] {π : C ⟶ S} [LocallyOfFinitePresentation π] [IsProper π]
    [Flat π] (hπ : UniversallyOConnected π) (hsm : SmoothOfRelativeDimension 1 π)
    {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S) {N : C.Modules} (hN : IsInvertible N)
    (hhigh : HasHighCechExactnessOpens π (discrepancy R Z N))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj (discrepancy R Z N) ≅ unitObj (Limits.pullback π x)))
    (hrig : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback Z).obj (discrepancy R Z N) ≅
      unitObj S)) :
    Nonempty (discrepancy R Z N ≅ unitObj C) := by
  obtain ⟨e⟩ := nonempty_discrepancy_iso_pullback_pullback_zero hπ hsm hR hZ hN hhigh hfib
  exact ⟨e ≪≫ (nonempty_pullback_iso_unitObj π hrig).some⟩

/-! ### The consumer shape -/

/-- **[B3-steps 2–3, consumer shape] The relative theorem of the square.**

`I(D_P) ⊗ I(D_Q) ≅ (I(D_R) ⊗ I(D_Z)) ⊗ f^*N₀` for an invertible `N₀` on the base — this is
exactly `Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add`, with `R = P + Q`
and `Z` the zero section.

`hN` — the `⊗`-inverse datum that the fibrewise input
`nonempty_pullback_discrepancy_iso_unitObj_projModel` already carries — does double duty: it also
supplies `IsInvertible N` through `isInvertible_of_tensorObj_iso_unitObj`. The base-level inverse
of the seesaw's output is the sheaf dual (`nonempty_eval_iso`), pulled back by
`nonempty_pullback_tensorObj_iso_unitObj`. -/
theorem exists_invertible_tensor_idealModule_add_of_hfib {C S : Scheme.{u}} [IsReduced S]
    [IsNoetherian S] [IsNoetherian C] [C.IsSeparated] {π : C ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π] (hπ : UniversallyOConnected π)
    (hsm : SmoothOfRelativeDimension 1 π) {P Q R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S)
    (hZ : Z ≫ π = 𝟙 S) {N : C.Modules}
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj C))
    (hhigh : HasHighCechExactnessOpens π (discrepancy R Z N))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj (discrepancy R Z N) ≅ unitObj (Limits.pullback π x))) :
    ∃ N₀ : S.Modules, IsInvertible N₀ ∧
      Nonempty (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Q)) ≅
        tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
            (Scheme.Modules.idealModule (Scheme.Hom.ker Z)))
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N₀)) := by
  obtain ⟨N₀, hN₀, e⟩ := exists_pullback_iso_discrepancy hπ hsm hR hZ
    (isInvertible_of_tensorObj_iso_unitObj hN) hhigh hfib
  refine ⟨dualObj N₀, hN₀.dual, nonempty_iso_tensorObj_of_tensorObj_unitObj hN e ?_⟩
  exact nonempty_pullback_tensorObj_iso_unitObj π (nonempty_eval_iso hN₀)

/-! ### The projective model of a Weierstrass curve -/

/-- The projective model of a Weierstrass curve over a Noetherian ring is a Noetherian scheme:
it is locally of finite type over the base, hence locally Noetherian, and proper over a
quasi-compact base, hence quasi-compact. -/
theorem isNoetherian_projModel {A : Type u} [CommRing A] [IsNoetherianRing A]
    (W₀ : WeierstrassCurve A) : IsNoetherian (projModel W₀) :=
  haveI : IsLocallyNoetherian (projModel W₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (projModelπ W₀)
  haveI : CompactSpace (projModel W₀) :=
    QuasiCompact.compactSpace_of_compactSpace (projModelπ W₀)
  ⟨⟩

/-- The projective model of an elliptic Weierstrass curve is flat over the base — it is smooth of
relative dimension one. -/
theorem flat_projModelπ {A : Type u} [CommRing A] (W₀ : WeierstrassCurve A) [W₀.IsElliptic] :
    Flat (projModelπ W₀) :=
  haveI : SmoothOfRelativeDimension 1 (projModelπ W₀) := projModel_smooth W₀
  haveI : Smooth (projModelπ W₀) := SmoothOfRelativeDimension.smooth 1 (projModelπ W₀)
  inferInstance

/-- **[B3-steps 2–3, tautological family] The discrepancy of the projective model is pulled back
from the base.**

For the projective model `projModelπ W₀ : projModel W₀ ⟶ Spec A` of an elliptic Weierstrass curve
over a **reduced Noetherian** ring, with sections `P`, `Q`, their `mulModelHom`-sum `Rs`, the zero
section, and a `⊗`-inverse `N` of `I(D_P) ⊗ I(D_Q)`, the discrepancy `(I(D_Rs) ⊗ I(D_0)) ⊗ N` is
the pullback of an invertible module from `Spec A`.

Everything the seesaw asks for is discharged here except `hhigh`: the fibrewise triviality is
`nonempty_pullback_discrepancy_iso_unitObj_projModel` (`WeilPairing/FibreWeierstrassPresentation`),
`UniversallyOConnected` is the locally-Weierstrass global-sections theorem through
`modelEllipticCurve`, and properness/flatness/finite presentation/Noetherianness are the
`WeierstrassModel` instances plus `isNoetherian_projModel` and `flat_projModelπ`. -/
theorem exists_pullback_iso_discrepancy_projModel {A : Type u} [CommRing A] [IsReduced A]
    [IsNoetherianRing A] {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = Limits.pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀)
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj (projModel W₀)))
    (hhigh : HasHighCechExactness (projModelπ W₀) (discrepancy Rs (projModelZero W₀) N)) :
    ∃ N₀ : (Spec (CommRingCat.of A)).Modules, IsInvertible N₀ ∧
      Nonempty (discrepancy Rs (projModelZero W₀) N ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (projModelπ W₀)).obj N₀) := by
  haveI : IsNoetherian (projModel W₀) := isNoetherian_projModel W₀
  haveI : Flat (projModelπ W₀) := flat_projModelπ W₀
  haveI : LocallyOfFinitePresentation (projModelπ W₀) := projModelπ_lfp W₀
  have hOC : UniversallyOConnected (projModelπ W₀) :=
    (modelEllipticCurve W₀).toEllipticCurveGeom.universallyOConnected
  exact exists_pullback_iso_discrepancy_of_isAffine hOC (projModel_smooth W₀) hR
    (projModelZero_projModelπ W₀) (isInvertible_of_tensorObj_iso_unitObj hN) hhigh
    fun {_} _ x => nonempty_pullback_discrepancy_iso_unitObj_projModel hP hQ hR hRs N hN x

/-- **[B3-steps 2–3, tautological family, consumer shape] The relative theorem of the square for
the projective model**: `I(D_P) ⊗ I(D_Q) ≅ (I(D_{P+Q}) ⊗ I(D_0)) ⊗ f^*N₀`, modulo `hhigh`.

This is `Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add` for the
Weierstrass-model family. -/
theorem exists_invertible_tensor_idealModule_add_projModel {A : Type u} [CommRing A]
    [IsReduced A] [IsNoetherianRing A] {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = Limits.pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀)
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj (projModel W₀)))
    (hhigh : HasHighCechExactness (projModelπ W₀) (discrepancy Rs (projModelZero W₀) N)) :
    ∃ N₀ : (Spec (CommRingCat.of A)).Modules, IsInvertible N₀ ∧
      Nonempty (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Q)) ≅
        tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker Rs))
            (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W₀))))
          ((AlgebraicGeometry.Scheme.Modules.pullback (projModelπ W₀)).obj N₀)) := by
  obtain ⟨N₀, hN₀, e⟩ := exists_pullback_iso_discrepancy_projModel hP hQ hR hRs N hN hhigh
  refine ⟨dualObj N₀, hN₀.dual, nonempty_iso_tensorObj_of_tensorObj_unitObj hN e ?_⟩
  exact nonempty_pullback_tensorObj_iso_unitObj (projModelπ W₀) (nonempty_eval_iso hN₀)

end ModularCurves
