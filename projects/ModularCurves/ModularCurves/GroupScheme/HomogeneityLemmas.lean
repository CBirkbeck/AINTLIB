/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves stream D
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Ring-theoretic leaves of the KM 6.2/6.3 homogeneity block ([KM-62-63-HOMOG])

The Katz–Mazur proof of Main Theorem 6.1.1 (cyclicity: `D = G^×`) verifies condition (3)
of the Axiomatic Isomorphism Theorem 6.2.1 by an explicit complete-local-ring computation
(KM §6.3, print pp. 157–162). This file isolates the *ring-theoretic cores* of that
computation, decoupled from the (Ell)-moduli-problem frame (the [HOMOG-FRAME] gate — see
`.mathlib-quality/decomposition-km-62-63.md`):

* `ModularCurves.Homogeneity.isUnit_add_of_mem_maximalIdeal`,
  `ModularCurves.Homogeneity.factor_unit_or_maximal` — KM Lemma 6.3.6's dichotomy
  `[a](P) = P·(unit)` / `P·(elt of max)`, in factored form.
* `ModularCurves.Homogeneity.root_mul_injective` — KM Lemma 6.3.4, determinant-free:
  multiplication by the root is injective on `AdjoinRoot (∏ (X - C bᵢ))` whenever `∏ bᵢ`
  is a nonzerodivisor (KM's regular-parameter input `∏ [b](P) ≠ 0` provides this over the
  domain `A`).
* `ModularCurves.Homogeneity.esymm_add_eq_unit_mul_pow` — KM Lemma 6.3.5's coefficient
  computation: the `card u`-th elementary symmetric function of `u + v` with `u` made of
  units and `v` of maximal-ideal elements is a unit; combined with the `pow_smul_esymm`
  homogeneity this is KM's "`(unit) × P^{φ(pⁿ)}`".
* `ModularCurves.Homogeneity.ker_eq_bot_of_smul_regular` — KM 6.3.2–6.3.3's
  serpent/Nakayama assembly in module form: a linear map with finitely generated kernel,
  whose target has no `q`-torsion and whose `q`-reduction is injective on preimages, has
  zero kernel (for `q` in the Jacobson radical).
-/

open Multiset Polynomial

namespace ModularCurves.Homogeneity

universe u v

variable {A : Type u} [CommRing A]

/-! ## KM 6.3.6 — the unit/maximal dichotomy (factored form) -/

/-- A unit plus a maximal-ideal element is a unit in a local ring (the "unit" branch of
KM 6.3.6: `a + (elt. in P·A[[P]])` is a unit when `(a, p) = 1`). -/
theorem isUnit_add_of_mem_maximalIdeal [IsLocalRing A] {a x : A} (ha : IsUnit a)
    (hx : x ∈ IsLocalRing.maximalIdeal A) : IsUnit (a + x) := by
  by_contra h
  have hmem : a + x ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have : a ∈ IsLocalRing.maximalIdeal A := by
    simpa using Submodule.sub_mem _ hmem hx
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp this) ha

/-- **(KM Lemma 6.3.6, factored form)** If `[a](P) = P * (a + P * g)` — the shape of a
formal-group multiplication `[a](X) = aX + O(X²)` evaluated at `P ∈ max(A)` — then the
cofactor `a + P * g` is a unit when `a` is one, and lies in `max(A)` when `a` does. -/
theorem factor_unit_or_maximal [IsLocalRing A] {P a g : A}
    (hP : P ∈ IsLocalRing.maximalIdeal A) :
    (IsUnit a → IsUnit (a + P * g)) ∧
      (a ∈ IsLocalRing.maximalIdeal A → a + P * g ∈ IsLocalRing.maximalIdeal A) :=
  ⟨fun ha => isUnit_add_of_mem_maximalIdeal ha (Ideal.mul_mem_right g _ hP),
    fun ha => Submodule.add_mem _ ha (Ideal.mul_mem_right g _ hP)⟩

/-! ## KM 6.3.4 — multiplication by the root is injective (determinant-free) -/

/-- The constant coefficient of `∏ᵢ (X - bᵢ)`, over a multiset `s = {bᵢ}`, is
`(-1) ^ (card s) * ∏ᵢ bᵢ` — evaluate the product of monic linear factors at `0`. -/
theorem coeff_zero_multiset_prod_X_sub_C (s : Multiset A) :
    ((s.map fun b => X - C b).prod).coeff 0 = (-1) ^ Multiset.card s * s.prod := by
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub]
  rw [show (s.map fun b => -b) = s.map Neg.neg from rfl]
  calc (s.map Neg.neg).prod
      = (s.map fun b => -1 * b).prod := by
        exact congrArg _ (Multiset.map_congr rfl fun b _ => by ring)
    _ = (s.map fun _ => (-1 : A)).prod * (s.map fun b => b).prod :=
        Multiset.prod_map_mul
    _ = (-1) ^ Multiset.card s * s.prod := by
        rw [Multiset.map_const', Multiset.prod_replicate, Multiset.map_id']

/-- **(KM Lemma 6.3.4, determinant-free core)** On `A[Q]/(∏ᵢ (Q - bᵢ))`, multiplication
by (the image of) `Q` is injective provided `∏ᵢ bᵢ` is a nonzerodivisor of `A`. KM's
determinant computation `det(Q | A₁) = ± ∏ [b](P) ≠ 0` (over the regular local domain `A`)
is exactly the verification of this hypothesis; the injectivity itself needs only the
nonzerodivisor property, via the constant-term relation
`root · h(root) = - (constant coefficient)` on the `A`-free module `AdjoinRoot`. -/
theorem root_mul_injective (s : Multiset A) (hreg : IsSMulRegular A s.prod) :
    Function.Injective fun z : AdjoinRoot ((s.map fun b => X - C b).prod) =>
      AdjoinRoot.root _ * z := by
  classical
  set f : A[X] := (s.map fun b => X - C b).prod with hf
  have hmonic : f.Monic := monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  -- `f - C (f.coeff 0)` is divisible by `X`
  have hdvd : X ∣ f - C (f.coeff 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, sub_self]
  obtain ⟨h, hh⟩ := hdvd
  -- evaluated at the root: `root * h(root) = - (constant coefficient)`
  have hrel : AdjoinRoot.root f * AdjoinRoot.mk f h =
      - algebraMap A (AdjoinRoot f) (f.coeff 0) := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    calc AdjoinRoot.root f * AdjoinRoot.mk f h
        = AdjoinRoot.mk f (X * h) := by rw [map_mul, AdjoinRoot.mk_X]
      _ = AdjoinRoot.mk f (f - C (f.coeff 0)) := by rw [← hh]
      _ = - AdjoinRoot.mk f (C (f.coeff 0)) := by rw [map_sub, h0, zero_sub]
      _ = - algebraMap A (AdjoinRoot f) (f.coeff 0) := by
          rw [AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  -- the constant coefficient is `(-1)^(card s) * ∏ bᵢ`, a nonzerodivisor of `A`
  have hcoeff : f.coeff 0 = (-1) ^ Multiset.card s * s.prod := by
    rw [hf]; exact coeff_zero_multiset_prod_X_sub_C s
  have hc : IsSMulRegular A (f.coeff 0) := by
    rw [hcoeff]
    exact ((isUnit_one.neg.pow (Multiset.card s)).isSMulRegular A).mul hreg
  -- transport regularity to the `A`-free module `AdjoinRoot f`
  have hcM : Function.Injective fun z : AdjoinRoot f => f.coeff 0 • z := by
    intro x y hxy
    apply (AdjoinRoot.powerBasis' hmonic).basis.repr.injective
    ext i
    have h1 := congrArg (fun w => ((AdjoinRoot.powerBasis' hmonic).basis.repr w) i) hxy
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact hc h1
  -- conclude: multiply `root * z = root * w` by `h(root)` and cancel
  intro z w hzw
  have h4 : ∀ v : AdjoinRoot f, AdjoinRoot.mk f h * (AdjoinRoot.root f * v) =
      - algebraMap A (AdjoinRoot f) (f.coeff 0) * v := by
    intro v
    rw [← mul_assoc, mul_comm (AdjoinRoot.mk f h), hrel]
  have h3 := congrArg (fun v => AdjoinRoot.mk f h * v) hzw
  simp only [h4] at h3
  have h2 : f.coeff 0 • z = f.coeff 0 • w := by
    have h5 : algebraMap A (AdjoinRoot f) (f.coeff 0) * z =
        algebraMap A (AdjoinRoot f) (f.coeff 0) * w := by
      have := neg_injective (by simpa [neg_mul] using h3)
      exact this
    simpa [Algebra.smul_def] using h5
  exact hcM h2

/-! ## KM 6.3.5 — the elementary-symmetric coefficient is a unit times `P^φ` -/

/-- The elementary symmetric function at full cardinality is the product. -/
theorem esymm_card_eq_prod (s : Multiset A) : s.esymm (Multiset.card s) = s.prod := by
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton,
    Multiset.sum_singleton]

/-- Elementary symmetric functions of a multiset of maximal-ideal elements lie in the
maximal ideal (positive degree). -/
theorem esymm_mem_maximalIdeal [IsLocalRing A] {v : Multiset A}
    (hv : ∀ x ∈ v, x ∈ IsLocalRing.maximalIdeal A) {k : ℕ} (hk : 0 < k)
    (_hkv : k ≤ Multiset.card v) :
    v.esymm k ∈ IsLocalRing.maximalIdeal A := by
  rw [Multiset.esymm]
  refine multiset_sum_mem _ fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨htv, htk⟩ := Multiset.mem_powersetCard.mp ht
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp (htk ▸ hk)
  obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hy
  rw [Multiset.prod_cons]
  exact Ideal.mul_mem_right _ _ (hv y (Multiset.mem_of_le htv (Multiset.mem_cons_self y t')))

/-- The coefficients of `∏_{r ∈ w} (X + C r)` are the elementary symmetric functions
(Vieta, coefficient-indexed form). -/
theorem coeff_prod_X_add_C (w : Multiset A) (i : ℕ) :
    ((w.map fun r => X + C r).prod).coeff i =
      if i ≤ Multiset.card w then w.esymm (Multiset.card w - i) else 0 := by
  classical
  rw [Multiset.prod_X_add_C_eq_sum_esymm, Polynomial.finsetSum_coeff]
  by_cases hi : i ≤ Multiset.card w
  · rw [if_pos hi, Finset.sum_eq_single (Multiset.card w - i)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one]
    · intro j hj hne
      have hj' := Finset.mem_range.mp hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by
        intro heq
        exact hne (by omega)), mul_zero]
    · intro habs
      exact absurd (Finset.mem_range.mpr (by omega)) habs
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by
      have := Finset.mem_range.mp hj
      omega), mul_zero]

/-- A product of units is a unit (multiset form). -/
theorem isUnit_multiset_prod {u : Multiset A} (hu : ∀ x ∈ u, IsUnit x) : IsUnit u.prod := by
  induction u using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.prod_cons]
      exact (hu a (Multiset.mem_cons_self a t)).mul
        (ih fun x hx => hu x (Multiset.mem_cons_of_mem hx))

/-- **(KM Lemma 6.3.5, coefficient core)** For `u` a multiset of units and `v` one of
maximal-ideal elements, the `card u`-th elementary symmetric function of `u + v` is a
unit: it is `∏ u` (a unit) plus terms each containing a maximal-ideal factor. Combined
with `Multiset.pow_smul_esymm`, this is KM's statement that the coefficient of
`X^{pⁿ - φ(pⁿ)}` in `∏_{a mod pⁿ} (X - [a](P))` equals `(unit) · P^{φ(pⁿ)}`. -/
theorem esymm_add_eq_unit_mul_pow [IsLocalRing A] {u v : Multiset A}
    (hu : ∀ x ∈ u, IsUnit x) (hv : ∀ x ∈ v, x ∈ IsLocalRing.maximalIdeal A) :
    IsUnit ((u + v).esymm (Multiset.card u)) := by
  classical
  -- read the symmetric function off as the `X^(card v)` coefficient of the product
  have hkey : (u + v).esymm (Multiset.card u) =
      ((u.map fun r => X + C r).prod * (v.map fun r => X + C r).prod).coeff
        (Multiset.card v) := by
    rw [← Multiset.prod_add, ← Multiset.map_add, coeff_prod_X_add_C, Multiset.card_add,
      if_pos (by omega)]
    congr 1
    omega
  have hesymm0 : v.esymm 0 = 1 := by
    simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [hkey, Polynomial.coeff_mul]
  -- split off the `(0, card v)` term, which is `∏ u`; the rest lies in the maximal ideal
  have hmem : ((0 : ℕ), Multiset.card v) ∈ Finset.antidiagonal (Multiset.card v) := by
    simp
  rw [← Finset.add_sum_erase _ _ hmem,
    show ((0 : ℕ), Multiset.card v).1 = 0 from rfl,
    show ((0 : ℕ), Multiset.card v).2 = Multiset.card v from rfl,
    coeff_prod_X_add_C, coeff_prod_X_add_C, if_pos (Nat.zero_le _), if_pos le_rfl,
    Nat.sub_zero, Nat.sub_self, esymm_card_eq_prod, hesymm0, mul_one]
  refine isUnit_add_of_mem_maximalIdeal (isUnit_multiset_prod hu) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  obtain ⟨hp_ne, hp_anti⟩ := Finset.mem_erase.mp hp
  have hsum : p.1 + p.2 = Multiset.card v := Finset.mem_antidiagonal.mp hp_anti
  rw [coeff_prod_X_add_C, coeff_prod_X_add_C]
  by_cases hi : p.1 ≤ Multiset.card u
  · rw [if_pos hi, if_pos (by omega : p.2 ≤ Multiset.card v)]
    refine Ideal.mul_mem_left _ _ (esymm_mem_maximalIdeal hv ?_ (by omega))
    -- `0 < card v - p.2`: otherwise `p = (0, card v)`, which was erased
    rcases Nat.lt_or_ge p.2 (Multiset.card v) with hlt | hge
    · omega
    · exfalso
      apply hp_ne
      have h2 : p.2 = Multiset.card v := le_antisymm (by omega) hge
      have h1 : p.1 = 0 := by omega
      exact Prod.ext h1 h2
  · rw [if_neg hi, zero_mul]
    exact Submodule.zero_mem _

/-! ## KM 6.3.2–6.3.3 — the serpent/Nakayama assembly (module form) -/

/-- **(KM 6.3.2–6.3.3, module form)** Let `q` be an element of the Jacobson radical, and
`f : M →ₗ[B] N` a linear map with finitely generated kernel such that (i) `N` has no
`q`-torsion (KM 6.3.4: multiplication by `Q` injective on `A₁`) and (ii) any preimage of
`q·N` lies in `q·M` (KM 6.3.5: `A₂/QA₂ ≅ A₁/QA₁`, in preimage form). Then `f` is
injective. This is KM's serpent-lemma-plus-Nakayama step, hand-rolled: for `x ∈ ker f`,
`f x = 0 ∈ q·N` gives `x = q·m`, and `0 = f x = q·(f m)` forces `f m = 0`, so
`ker f ≤ q·(ker f)` and Nakayama finishes. -/
theorem ker_eq_bot_of_smul_regular {B : Type u} [CommRing B] {M N : Type v}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (q : B)
    (hq : q ∈ (⊥ : Ideal B).jacobson) (f : M →ₗ[B] N) (hKfg : (LinearMap.ker f).FG)
    (hNreg : ∀ n : N, q • n = 0 → n = 0)
    (hmodq : ∀ m : M, (∃ n : N, f m = q • n) → ∃ m' : M, m = q • m') :
    LinearMap.ker f = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {q}) _ hKfg ?_ ?_
  · intro x hx
    obtain ⟨m, rfl⟩ := hmodq x ⟨0, by rw [LinearMap.mem_ker.mp hx, smul_zero]⟩
    have hfm : f m = 0 := hNreg _ (by rw [← map_smul]; exact LinearMap.mem_ker.mp hx)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self q)
      (LinearMap.mem_ker.mpr hfm)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hq

end ModularCurves.Homogeneity
