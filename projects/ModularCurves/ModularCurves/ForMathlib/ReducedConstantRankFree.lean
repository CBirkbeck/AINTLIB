/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Constant fibre rank over a reduced ring (Stacks 0FWG)

A finite module over a **reduced** ring whose fibre dimension `p ↦ dim_{κ(p)} (M ⊗ κ(p))` is
locally constant is finite locally free.

## Why this file exists

This is the *only* new commutative algebra the rank-one seesaw (`ForMathlib/Seesaw.lean`) needs,
and it is **not in mathlib** (searched 2026-08-08: `leansearch` on the statement,
`local_search "rankAtStalk"`, and `grep IsReduced` in `RingTheory/Spectrum/Prime/FreeLocus.lean`,
`RingTheory/Flat/Rank.lean`, `RingTheory/LocalProperties/Projective.lean` — all empty). It
replaces cohomology-and-base-change / Grauert, which mathlib also lacks: the seesaw applies it to
the **cokernel** of the tree's finite-projective replacement differential, whose fibre dimension
*is* locally constant by right-exactness of `⊗`, and reads off local freeness of the kernel from
the two resulting splittings.

## Source

Stacks Project, tag [0FWG]:

> "Let `R` be a reduced ring and let `M` be a finite `R`-module such that
> `p ↦ dim_{κ(p)} M ⊗_R κ(p)` is locally constant on `Spec(R)`. Then `M` is finite locally free."

## The proof, and where reducedness enters

Everything happens over the local ring `R_p`; note that every prime `q ⊆ p` lies in *every*
Zariski neighbourhood of `p` (if `g ∉ p` and `q ⊆ p` then `g ∉ q`), so local constancy at `p`
becomes **constancy on all of `Spec R_p`**. Then:

1. Nakayama (`IsLocalRing.map_tensorProduct_mk_eq_top`) lifts a `κ(𝔪)`-basis of the fibre to a
   surjection `g : R^n ↠ M`.
2. For every prime `q`, the induced `κ(q)^n → M ⊗ κ(q)` is surjective between spaces of the same
   dimension `n`, hence **bijective**.
3. So for `x ∈ ker g`, the image of `x` in `κ(q)^n` is zero, i.e. every coordinate `x i` lies
   in `q`.
4. Intersecting over all primes puts each `x i` in the nilradical — which is `0` because `R` is
   **reduced**. Hence `ker g = ⊥` and `g` is an isomorphism.

Note (external review, 2026-08-08): step 3 asserts that the *composite* `K → R^n → κ(q)^n`
vanishes, i.e. `K_q ⊆ q R_q^n`. It does **not** assert `K ⊗ κ(q) = 0`, which does not follow.
The Noetherian hypothesis is not needed anywhere; `Module.Finite R M` suffices.
-/

universe u

open Module
open scoped TensorProduct

namespace ModularCurves

/-- Step 3 of the argument, for a single prime: if `g : Rⁿ → M` is surjective and the fibre of `M`
at a residue field `κ` has dimension at least `n`, then every element of `ker g` has all of its
coordinates killed by `R → κ`.

Indeed `κ ⊗ g : κⁿ → κ ⊗ M` is surjective by right-exactness, so `dim_κ (κ ⊗ M) ≤ n`; combined
with `hκ` this is an equality, so `κ ⊗ g` is a surjection between `κ`-spaces of the same finite
dimension, hence injective. As `(κ ⊗ g) (1 ⊗ c) = 1 ⊗ g c = 0`, we get `1 ⊗ c = 0` in
`κ ⊗ Rⁿ ≃ κⁿ`, i.e. each coordinate of `c` maps to `0` in `κ`.

Stated for an arbitrary `R`-algebra field `κ` (rather than for `κ(p)` directly) so that the
`Ideal.ResidueField` instance arguments never have to be manipulated inside the proof. -/
private lemma algebraMap_eq_zero_of_mem_ker
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {n : ℕ} {g : (Fin n → R) →ₗ[R] M} (hg : Function.Surjective g)
    (κ : Type u) [Field κ] [Algebra R κ] (hκ : n ≤ Module.finrank κ (κ ⊗[R] M))
    {c : Fin n → R} (hc : g c = 0) (i : Fin n) : algebraMap R κ (c i) = 0 := by
  classical
  let e : κ ⊗[R] (Fin n → R) ≃ₗ[κ] (Fin n → κ) := TensorProduct.piScalarRight R κ κ (Fin n)
  have hrank : Module.finrank κ (κ ⊗[R] (Fin n → R)) = n := by
    rw [e.finrank_eq]; simp
  have hGsurj : Function.Surjective (LinearMap.baseChange κ g) :=
    LinearMap.baseChange_surjective κ hg
  have hle : Module.finrank κ (κ ⊗[R] M) ≤ n := by
    rw [← hrank]; exact LinearMap.finrank_le_finrank_of_surjective hGsurj
  have heq : Module.finrank κ (κ ⊗[R] (Fin n → R)) = Module.finrank κ (κ ⊗[R] M) := by
    rw [hrank]; omega
  have hGinj : Function.Injective (LinearMap.baseChange κ g) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hGsurj
  have h0 : (1 : κ) ⊗ₜ[R] c = 0 := by
    apply hGinj
    rw [LinearMap.baseChange_tmul, hc, TensorProduct.tmul_zero, map_zero]
  have h1 := congrArg e h0
  rw [map_zero] at h1
  have h2 : e ((1 : κ) ⊗ₜ[R] c) = fun j => c j • (1 : κ) := by
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rw [h2] at h1
  have hi : c i • (1 : κ) = 0 := congrFun h1 i
  rwa [← Algebra.algebraMap_eq_smul_one] at hi

/-- **(Stacks 0FWG, local form)** A finite module over a reduced local ring whose fibre dimension
is at least `n` at every prime, and exactly `n` at the closed point, is free.

The `n`-at-the-closed-point hypothesis is what Nakayama consumes; the `≥ n` at the other primes is
what upgrades "surjective" to "bijective" on each fibre. Both are supplied by local constancy of
the fibre dimension, since every prime of a local ring is a generization of the closed point. -/
theorem free_of_isReduced_of_forall_le_finrank_fiber
    {R : Type u} [CommRing R] [IsLocalRing R] [IsReduced R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ)
    (hclosed : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = n)
    (hmin : ∀ p : PrimeSpectrum R,
      n ≤ Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Free R M := by
  classical
  let k := IsLocalRing.ResidueField R
  -- 1. A `k`-basis of the closed fibre, of size `n` by `hclosed`.
  let b : Basis (Fin n) k (k ⊗[R] M) := Module.finBasisOfFinrankEq k (k ⊗[R] M) hclosed
  -- 2. Lift it to `M`: `m ↦ 1 ⊗ m` is surjective because `R → k` is.
  have hmksurj : Function.Surjective ((TensorProduct.mk R k M) 1) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  choose x hx using fun i : Fin n => hmksurj (b i)
  -- 3. Nakayama: the lifts span `M`.
  have hspan : Submodule.span R (Set.range x) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis x b hx
  -- 4. The resulting surjection `g : Rⁿ ↠ M`.
  set g : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R x with hgdef
  have hgsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, hgdef, Fintype.range_linearCombination, hspan]
  -- 5. `g` is injective: each coordinate of an element of `ker g` lies in every prime, hence in
  -- the nilradical, which vanishes since `R` is reduced.
  have hker : LinearMap.ker g = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    rw [Submodule.mem_bot]
    funext i
    show c i = 0
    have key : ∀ J : Ideal R, J.IsPrime → c i ∈ J := by
      intro J hJ
      haveI := hJ
      exact Ideal.algebraMap_residueField_eq_zero.mp
        (algebraMap_eq_zero_of_mem_ker hgsurj J.ResidueField (hmin ⟨J, hJ⟩) hc i)
    have hnil : c i ∈ nilradical R := by
      rw [nilradical_eq_sInf]
      exact Submodule.mem_sInf.mpr fun J hJ => key J hJ
    rw [nilradical_eq_zero] at hnil
    simpa using hnil
  -- 6. So `g` is an isomorphism `Rⁿ ≃ₗ M`.
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨LinearMap.ker_eq_bot.mp hker, hgsurj⟩)

/-! ### From the local form to the global form

Passing from `free_of_isReduced_of_forall_le_finrank_fiber` to Stacks 0FWG needs, besides
`Module.projective_of_localization_maximal`, only the identification of the fibres of the localized
module `M_I` with the fibres of `M`. That splits into a base-change cancellation (the module side)
and the fact that a localization does not change residue fields (the field side). -/

/-- **Base change for a localized module.** For any algebra `κ` over `S⁻¹R`, the fibre of `S⁻¹M`
over `κ` is the fibre of `M`: this is `LocalizedModule.equivTensorProduct` followed by the
cancellation `κ ⊗[S⁻¹R] (S⁻¹R ⊗[R] M) ≃ κ ⊗[R] M`. -/
private noncomputable def tensorLocalizedModuleEquiv {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] (κ : Type u) [CommRing κ]
    [Algebra (Localization S) κ] [Algebra R κ] [IsScalarTower R (Localization S) κ] :
    κ ⊗[Localization S] (LocalizedModule S M) ≃ₗ[κ] κ ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ)
      (LocalizedModule.equivTensorProduct S M)) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) κ κ M

/-- The dimension of the fibre of `S⁻¹M` over an `S⁻¹R`-algebra `κ` is that of the fibre of `M`. -/
private lemma finrank_tensor_localizedModule {R : Type u} [CommRing R] (S : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] (κ : Type u) [CommRing κ]
    [Algebra (Localization S) κ] [Algebra R κ] [IsScalarTower R (Localization S) κ] :
    Module.finrank κ (κ ⊗[Localization S] (LocalizedModule S M)) =
      Module.finrank κ (κ ⊗[R] M) :=
  (tensorLocalizedModuleEquiv S M κ).finrank_eq

/-- If `algebraMap R S` is surjective on stalks — the case of interest being a localization — then
for every prime `q` of `S` the canonical map `κ(q ∩ R) → κ(q)` is an isomorphism of
`R`-algebras. -/
private noncomputable def residueFieldAlgEquivOfSurjectiveOnStalks {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (H : (algebraMap R S).SurjectiveOnStalks) (q : Ideal S)
    [q.IsPrime] : (q.comap (algebraMap R S)).ResidueField ≃ₐ[R] q.ResidueField :=
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ (q.comap (algebraMap R S)) q (Algebra.ofId R S) rfl)
    (H.residueFieldMap_bijective _ q rfl)

/-- The fibre dimension of `M` at a field depends on that field only through its `R`-algebra
isomorphism class: base change along `K ≃ₐ[R] L` is `Module.finrank_baseChange`. -/
private lemma finrank_tensor_eq_of_algEquiv {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
    (φ : K ≃ₐ[R] L) : Module.finrank L (L ⊗[R] M) = Module.finrank K (K ⊗[R] M) := by
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R K L := .of_algebraMap_eq fun r => (φ.commutes r).symm
  let e : L ⊗[K] (K ⊗[R] M) ≃ₗ[L] L ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- The fibre of the localized module `M_I` at a prime `q` of `R_I` is the fibre of `M` at the
contraction of `q` to `R`. -/
private lemma finrank_fiber_localizedModule {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] (q : PrimeSpectrum (Localization.AtPrime I)) :
    Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[Localization.AtPrime I] LocalizedModule I.primeCompl M) =
      Module.finrank (q.asIdeal.comap (algebraMap R (Localization.AtPrime I))).ResidueField
        ((q.asIdeal.comap (algebraMap R (Localization.AtPrime I))).ResidueField ⊗[R] M) := by
  rw [finrank_tensor_localizedModule]
  exact finrank_tensor_eq_of_algEquiv (residueFieldAlgEquivOfSurjectiveOnStalks
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _) q.asIdeal)

/-- **(Stacks 0FWG)** A finite module over a reduced Noetherian ring whose fibre dimension
`p ↦ dim_{κ(p)} (M ⊗ κ(p))` is locally constant on `Spec R` is projective — equivalently, finite
locally free.

Projectivity is checked one maximal ideal `I` at a time
(`Module.projective_of_localization_maximal`, which is the only place the Noetherian hypothesis is
spent — it supplies `Module.FinitePresentation R M`). Over `R_I` the local form
`free_of_isReduced_of_forall_le_finrank_fiber` applies: the primes of `R_I` are the primes `p ≤ I`
of `R`, with the same residue fields and hence the same fibres, and every such `p` lies in *every*
neighbourhood of `I`, so local constancy pins the fibre dimension to the single value
`dim_{κ(I)} (M ⊗ κ(I))` on all of `Spec R_I`. -/
theorem projective_of_isReduced_of_isLocallyConstant_finrank_fiber
    {R : Type u} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  refine Module.projective_of_localization_maximal fun I hI => ?_
  haveI := hI
  haveI : Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M) := by
    refine free_of_isReduced_of_forall_le_finrank_fiber
      (Module.finrank I.ResidueField (I.ResidueField ⊗[R] M)) ?_ ?_
    · -- The closed fibre of `M_I` is the fibre of `M` at `I`.
      exact finrank_tensor_localizedModule I.primeCompl M I.ResidueField
    · -- Every prime of `R_I` contracts to a prime `p ≤ I`, and `p` lies in every neighbourhood
      -- of `I`, so local constancy forces the two fibre dimensions to agree.
      intro q
      rw [finrank_fiber_localizedModule I M q]
      set p : Ideal R := q.asIdeal.comap (algebraMap R (Localization.AtPrime I))
      have hple : p ≤ I := by
        intro x hx
        by_contra hxI
        exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
          (IsLocalization.map_units (Localization.AtPrime I) (⟨x, hxI⟩ : I.primeCompl)))
      have hspec : (⟨p, inferInstance⟩ : PrimeSpectrum R) ⤳ ⟨I, hI.isPrime⟩ :=
        (PrimeSpectrum.le_iff_specializes _ _).mp ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple)
      exact (hspec.mem_open (h.isOpen_fiber _)
        (rfl : Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) = _)).ge
  infer_instance

end ModularCurves
