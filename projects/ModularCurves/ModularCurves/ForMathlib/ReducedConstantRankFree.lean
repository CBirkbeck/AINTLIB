/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalProperties.Projective

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

end ModularCurves
