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
* **(step 4)** `hasHighCechExactness_of_two_affine_open_cover` — `hhigh` for any separated total
  space covered by **two** affine opens, and `hasHighCechExactness_projModel`, its instance for
  the projective Weierstrass model.
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
* `isNoetherian_of_isProper` / `isSeparated_of_isSeparated_hom` and the universal-pair instances
  `isNoetherian_pairBase`, `isNoetherian_pairCurve`, `isSeparated_pairCurve` — the three
  hypotheses of the seesaw that instance search does **not** find for
  `WeilPairing/TautologicalPair.lean`'s `pairBase`/`pairCurve` (everything else it does find).
* `exists_pullback_iso_discrepancy_projModel`,
  `exists_invertible_tensor_idealModule_add_projModel` — the same two conclusions for the
  projective model `projModelπ W₀ : projModel W₀ ⟶ Spec A` of an elliptic Weierstrass curve over
  a **reduced Noetherian** ring, with `hfib` discharged; `hhigh` a hypothesis.
* `exists_pullback_iso_discrepancy_projModel'`,
  `exists_invertible_tensor_idealModule_add_projModel'` — the same two conclusions with **no**
  `hhigh`, discharged by `hasHighCechExactness_projModel`. The hypothesised forms are kept for
  consumers carrying their own exactness input.

## How `hhigh` is discharged (step 4)

`hhigh` is exactness of the ordered base-Čech complex at the positions `≥ 2`, i.e. `H^{≥2}` of
the **total space** — not of the fibres. The projective Weierstrass model is a `Proj`, hence
separated, and is covered by the *two* affine charts `projModelZChart` and
`projModelSectionNeighborhood`; Mayer–Vietoris
(`subsingleton_H_add_two_of_two_affine_open_cover`) then kills `H^{≥2}` for every quasicoherent
module, and `orderedBaseCechComplex_exactAt_succ_iff_subsingleton_H_of_affine_openCover` converts
that into ordered base-Čech exactness for *every* finite affine cover — the uniformity the seesaw
needs, since it builds its cover internally. No fibre, no base change, and in particular no `H¹`
claim: that is why `hhigh` is available where the seesaw's `hexact` (position `1` as well, false
on a genus-one fibre) is not.

## What is *not* here

`HasHighCechExactnessOpens` — the arbitrary-base seesaw's `hhigh` — is still only a hypothesis.
It quantifies over **all opens `W` of the base**, including non-affine ones, and the two charts of
the model do not restrict to affine opens of `π ⁻¹ᵁ W`, so
`hasHighCechExactness_of_two_affine_open_cover` does not apply to `π ∣_ W`. Only the affine-base
predicate `HasHighCechExactness` is discharged, which is the one the projective model's theorems
use. See the report on ticket B3-step4.
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

/-- **[B3-step4, generic] Two affine charts on the total space discharge the seesaw's `hhigh`.**

`hhigh` is exactness of the ordered base-Čech complex at the positions `≥ 2`, i.e. the vanishing
of `H^{≥2}` of the **total space** — and a separated scheme covered by *two* affine opens has
`H^{≥2} = 0` for every quasicoherent module, by Mayer–Vietoris
(`subsingleton_H_add_two_of_two_affine_open_cover`). The ordered base-Čech complex of any finite
affine open cover computes that cohomology
(`orderedBaseCechComplex_exactAt_succ_iff_subsingleton_H_of_affine_openCover`), so the conclusion
is uniform in the cover — which is what the seesaw needs, since it builds its cover internally.

Nothing fibrewise, and no base change, is used: in particular no `H¹` of anything is claimed.
That is exactly why `hhigh` is available where the seesaw's `hexact` (which also demands position
`1`, false on a genus-one fibre) is not. -/
theorem hasHighCechExactness_of_two_affine_open_cover {C S : Scheme.{u}} [C.IsSeparated]
    (π : C ⟶ S) (M : C.Modules) [M.IsQuasicoherent] {U V : C.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    HasHighCechExactness π M := by
  intro ι _ _ W hW hWaff q hq _
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hH : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (p + 1 + 1)) :=
    subsingleton_H_add_two_of_two_affine_open_cover M U V hU hV hUV p
  have hex := (orderedBaseCechComplex_exactAt_succ_iff_subsingleton_H_of_affine_openCover
    π M W hW hWaff (p + 1)).mpr hH
  rw [HomologicalComplex.exactAt_iff' _ (p + 1) (p + 2) (p + 3) (by simp) (by simp)] at hex
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex

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

/-- The discrepancy module is quasicoherent — it is invertible (`isInvertible_discrepancy`).
This is the instance the Čech-cohomology reading of `hhigh` needs. -/
theorem isQuasicoherent_discrepancy {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {R Z : S ⟶ C} (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S)
    {N : C.Modules} (hN : IsInvertible N) : (discrepancy R Z N).IsQuasicoherent :=
  (isInvertible_discrepancy hsm hR hZ hN).isQuasicoherent

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

/-! ### Noetherianness and separatedness bridges

The seesaw asks for `IsNoetherian` and `Scheme.IsSeparated` of the *total space*, which for the
families of interest — the projective Weierstrass model, and the universal pair `C ×_S C` with its
base-changed curve — are never found by instance search, because those total spaces are `pullback`
expressions whose structure morphisms are only proper *after* an unfolding step. Both follow from
the corresponding property of the base along a proper (resp. separated) structure morphism. -/

/-- A scheme proper over a Noetherian scheme is Noetherian: locally of finite type gives
`IsLocallyNoetherian`, quasi-compactness over a compact base gives `CompactSpace`. -/
theorem isNoetherian_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian Y] :
    IsNoetherian X :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-- A scheme separated over a separated scheme is separated: `terminal.from X = f ≫ terminal.from
Y`, and separatedness of morphisms is stable under composition. -/
theorem isSeparated_of_isSeparated_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [Y.IsSeparated] : X.IsSeparated := by
  constructor
  rw [← terminal.comp_from f]
  infer_instance

/-! ### The universal pair of points

`WeilPairing/TautologicalPair.lean`'s `pairBase π = C ×_S C` carries the two tautological
sections, and `pairCurve π = C ×_S (C ×_S C)` is the family over it. These are the instances the
seesaw needs there; `IsReduced`, `IsProper`, `Flat`, `LocallyOfFinitePresentation` and
`UniversallyOConnected` are already found by instance search (resp. by
`UniversallyOConnected.baseChange`) for the universal Weierstrass family, but the three below are
not — the `pairCurve` spelling `pullback π (pullback.fst π π ≫ π)` is not literally any of the
fibre-cube spellings recorded in `EllipticCurve/GroupLawAxioms.lean`. -/

/-- The base of the universal pair is Noetherian when the base of the family is and the family is
proper: `pairBaseπ π = pullback.fst π π ≫ π` is then proper. -/
theorem isNoetherian_pairBase {C S : Scheme.{u}} (π : C ⟶ S) [IsProper π] [IsNoetherian S] :
    IsNoetherian (pairBase π) :=
  isNoetherian_of_isProper (pairBaseπ π)

/-- The total space of the universal pair family is Noetherian. -/
theorem isNoetherian_pairCurve {C S : Scheme.{u}} (π : C ⟶ S) [IsProper π] [IsNoetherian S] :
    IsNoetherian (pairCurve π) :=
  haveI := isNoetherian_pairBase π
  isNoetherian_of_isProper (pairCurveπ π)

/-- The total space of the universal pair family is a separated scheme. -/
theorem isSeparated_pairCurve {C S : Scheme.{u}} (π : C ⟶ S) [IsProper π] [S.IsSeparated] :
    (pairCurve π).IsSeparated :=
  haveI : (pairBase π).IsSeparated := isSeparated_of_isSeparated_hom (pairBaseπ π)
  isSeparated_of_isSeparated_hom (pairCurveπ π)

/-! ### The projective model of a Weierstrass curve -/

/-- The projective model of a Weierstrass curve over a Noetherian ring is a Noetherian scheme. -/
theorem isNoetherian_projModel {A : Type u} [CommRing A] [IsNoetherianRing A]
    (W₀ : WeierstrassCurve A) : IsNoetherian (projModel W₀) :=
  isNoetherian_of_isProper (projModelπ W₀)

/-- The projective model of an elliptic Weierstrass curve is flat over the base — it is smooth of
relative dimension one. -/
theorem flat_projModelπ {A : Type u} [CommRing A] (W₀ : WeierstrassCurve A) [W₀.IsElliptic] :
    Flat (projModelπ W₀) :=
  haveI : SmoothOfRelativeDimension 1 (projModelπ W₀) := projModel_smooth W₀
  haveI : Smooth (projModelπ W₀) := SmoothOfRelativeDimension.smooth 1 (projModelπ W₀)
  inferInstance

/-- **[B3-step4] The seesaw's `hhigh` for the projective Weierstrass model.**

The projective model is separated (`isSeparated_projModel`, it is a `Proj`) and is covered by the
*two* affine charts `projModelZChart` and `projModelSectionNeighborhood`
(`projModelZChart_sup_sectionNeighborhood_eq_top`), so
`hasHighCechExactness_of_two_affine_open_cover` applies: every quasicoherent module on it has
`H^{≥2} = 0`, hence positive-degree ordered base-Čech exactness for every finite affine cover.

No ellipticity, no reducedness and no Noetherian hypothesis: the two-chart cover exists for every
Weierstrass curve over every commutative ring. -/
theorem hasHighCechExactness_projModel {A : Type u} [CommRing A] (W₀ : WeierstrassCurve A)
    (M : (projModel W₀).Modules) [M.IsQuasicoherent] :
    HasHighCechExactness (projModelπ W₀) M :=
  hasHighCechExactness_of_two_affine_open_cover _ M (projModelZChart W₀).2
    (projModelSectionNeighborhood W₀).2 (projModelZChart_sup_sectionNeighborhood_eq_top W₀)

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

/-! ### The projective model, unconditionally

`hhigh` is now discharged by `hasHighCechExactness_projModel`, so the two conclusions above hold
with no hypothesis beyond the sections and the `⊗`-inverse datum. The hypothesised forms are kept
for consumers that carry their own exactness input. -/

/-- **[B3-steps 2–4, tautological family] The discrepancy of the projective model is pulled back
from the base — no hypotheses beyond the section data.**

`exists_pullback_iso_discrepancy_projModel` with its `hhigh` supplied by
`hasHighCechExactness_projModel`; the discrepancy is quasicoherent by
`isQuasicoherent_discrepancy`. -/
theorem exists_pullback_iso_discrepancy_projModel' {A : Type u} [CommRing A] [IsReduced A]
    [IsNoetherianRing A] {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = Limits.pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀)
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj (projModel W₀))) :
    ∃ N₀ : (Spec (CommRingCat.of A)).Modules, IsInvertible N₀ ∧
      Nonempty (discrepancy Rs (projModelZero W₀) N ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (projModelπ W₀)).obj N₀) :=
  haveI := isQuasicoherent_discrepancy (projModel_smooth W₀) hR (projModelZero_projModelπ W₀)
    (isInvertible_of_tensorObj_iso_unitObj hN)
  exists_pullback_iso_discrepancy_projModel hP hQ hR hRs N hN
    (hasHighCechExactness_projModel W₀ _)

/-- **[B3-steps 2–4, tautological family, consumer shape] The relative theorem of the square for
the projective model, unconditionally**:
`I(D_P) ⊗ I(D_Q) ≅ (I(D_{P+Q}) ⊗ I(D_0)) ⊗ f^*N₀` for an invertible `N₀` on `Spec A`, for an
elliptic Weierstrass curve over a reduced Noetherian ring — the hypothesis-free form of
`exists_invertible_tensor_idealModule_add_projModel`, i.e. `Picard/SelfAdjointN.lean`'s
`exists_invertible_tensor_idealModule_add` for the Weierstrass-model family. -/
theorem exists_invertible_tensor_idealModule_add_projModel' {A : Type u} [CommRing A]
    [IsReduced A] [IsNoetherianRing A] {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = Limits.pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀)
    (N : (projModel W₀).Modules)
    (hN : Nonempty (tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))) N ≅ unitObj (projModel W₀))) :
    ∃ N₀ : (Spec (CommRingCat.of A)).Modules, IsInvertible N₀ ∧
      Nonempty (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Q)) ≅
        tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker Rs))
            (Scheme.Modules.idealModule (Scheme.Hom.ker (projModelZero W₀))))
          ((AlgebraicGeometry.Scheme.Modules.pullback (projModelπ W₀)).obj N₀)) :=
  haveI := isQuasicoherent_discrepancy (projModel_smooth W₀) hR (projModelZero_projModelπ W₀)
    (isInvertible_of_tensorObj_iso_unitObj hN)
  exists_invertible_tensor_idealModule_add_projModel hP hQ hR hRs N hN
    (hasHighCechExactness_projModel W₀ _)

end ModularCurves
