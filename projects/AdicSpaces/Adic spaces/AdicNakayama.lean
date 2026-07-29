/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Topological Nakayama: finiteness from a finite adic quotient

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaf 10.)  If `R` is
`I`-adically precomplete, `M` is `I`-adically Hausdorff, and `M/IM` is a
finite `R`-module, then `M` is a finite `R`-module: lift generators of the
quotient, and apply the adic surjectivity criterion
`surjective_of_mkQ_comp_surjective`.

The consumer instantiates `R = 𝒪_K` (`π`-adically complete), `M = B` a
noetherian-domain quotient of the integral Tate algebra (`π`-adically
Hausdorff by Krull intersection), with `B/πB` finite over the residue field.
-/

@[expose] public section

open scoped Classical

section AdicNakayama

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `I • ⊤` on `R` itself is `I`. -/
theorem ideal_smul_top_self {R : Type*} [CommRing R] (I : Ideal R) :
    (I • (⊤ : Submodule R R)) = (I : Submodule R R) := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · simpa [smul_eq_mul] using Ideal.mul_mem_right x _ ha
  · have h1 : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa using h1

/-- `I • ⊤` on a finite power of `R` is the coordinatewise ideal. -/
theorem ideal_smul_top_pi {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (I • (⊤ : Submodule R (ι → R))) =
      Submodule.pi Set.univ (fun _ => (I : Submodule R R)) := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · refine Submodule.mem_pi.mpr fun i _ => ?_
    simpa [smul_eq_mul] using Ideal.mul_mem_right (x i) _ ha
  · rw [Submodule.mem_pi] at hx
    have hxs : x = ∑ i : ι, Pi.single i (x i) :=
      (Finset.univ_sum_single x).symm
    rw [hxs]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : Pi.single i (x i) = (x i) • Pi.single i (1 : R) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [h1]
    exact Submodule.smul_mem_smul (hx i trivial) Submodule.mem_top

/-- Precompleteness passes to finite powers, coordinatewise. -/
theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (ι : Type*) [Finite ι] :
    IsPrecomplete I (ι → R) := by
  classical
  cases nonempty_fintype ι
  constructor
  intro f hf
  have hcomp : ∀ i : ι, ∃ L : R, ∀ n,
      f n i ≡ L [SMOD (I ^ n • (⊤ : Submodule R R))] := by
    intro i
    refine IsPrecomplete.prec ‹IsPrecomplete I R› (fun {m n} hmn => ?_)
    have h1 := hf hmn
    rw [SModEq.sub_mem] at h1 ⊢
    rw [ideal_smul_top_pi] at h1
    rw [ideal_smul_top_self]
    have h2 := Submodule.mem_pi.mp h1 i trivial
    simpa using h2
  choose L hL using hcomp
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, ideal_smul_top_pi]
  refine Submodule.mem_pi.mpr fun i _ => ?_
  have h3 := hL i n
  rw [SModEq.sub_mem, ideal_smul_top_self] at h3
  simpa using h3

/-- **Topological Nakayama**: over an `I`-precomplete base, an `I`-Hausdorff
module with finitely generated reduction mod `I` is finitely generated. -/
theorem Module.Finite.of_finite_quotient_smul_top_of_isPrecomplete
    (I : Ideal R) [IsPrecomplete I R] [IsHausdorff I M]
    (hfin : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose g hg using Submodule.mkQ_surjective (I • (⊤ : Submodule R M))
  set v : s → M := fun i => g i.1 with hv
  set F : (s → R) →ₗ[R] M := Fintype.linearCombination R v with hF
  have hcomp : Function.Surjective
      ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) := by
    intro y
    have hy : y ∈ Submodule.span R (↑s : Set (M ⧸ (I • (⊤ : Submodule R M)))) := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hy
    refine ⟨fun i => c i.1, ?_⟩
    have h1 : ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) (fun i => c i.1) =
        ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i) := by
      rw [LinearMap.comp_apply, hF, Fintype.linearCombination_apply,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    rw [h1]
    have h2 : ∀ i : s, (I • (⊤ : Submodule R M)).mkQ (v i) = i.1 := by
      intro i
      rw [hv]
      exact hg i.1
    calc ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i)
        = ∑ i : s, c i.1 • i.1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [h2 i]
      _ = ∑ a ∈ s, c a • a := Finset.sum_coe_sort s (fun a => c a • a)
      _ = y := hc
  haveI : IsPrecomplete I (s → R) := isPrecomplete_pi I s
  exact Module.Finite.of_surjective F
    (surjective_of_mkQ_comp_surjective hcomp)

section PrincipalAdicDivision

open AdicCompletion

variable {R : Type*} [CommRing R]

/-- **Tower division in a principal adic completion**: an element of the
`(a)`-adic completion whose level-one component vanishes is divisible by `a`,
provided `a` is a nonzerodivisor ([hrw-decomposition] Tate leaf 4 engine:
the kernel of `evalOneₐ` is generated by `a`). -/
theorem AdicCompletion.exists_eq_of_mul_of_component_one_eq_zero
    {a : R} (ha : a ∈ nonZeroDivisors R)
    (x : AdicCompletion (Ideal.span {a}) R)
    (h1 : x.1 1 = 0) :
    ∃ y : AdicCompletion (Ideal.span {a}) R,
      x = AdicCompletion.of (Ideal.span {a}) R a * y := by
  classical
  have hlift : ∀ n : ℕ, ∃ r : R,
      Submodule.Quotient.mk r = x.1 (n + 1) :=
    fun n => Submodule.Quotient.mk_surjective _ (x.1 (n + 1))
  choose r hr using hlift
  have hdiv : ∀ n : ℕ, ∃ s : R, r n = a * s := by
    intro n
    have hcoh := x.2 (show 1 ≤ n + 1 by omega)
    rw [← hr n] at hcoh
    have h3 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show 1 ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ 1 • ⊤ : Submodule R R)) (r n) := rfl
    rw [h3, h1] at hcoh
    have h4 : r n ∈ ((Ideal.span {a}) ^ 1 • ⊤ : Submodule R R) :=
      (Submodule.Quotient.mk_eq_zero _).mp hcoh
    rw [ideal_smul_top_self, pow_one] at h4
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h4
    exact ⟨s, by rw [← hs]; ring⟩
  choose sfun hs using hdiv
  have hscoh : ∀ {m n : ℕ}, m ≤ n →
      Submodule.Quotient.mk
        (p := ((Ideal.span {a}) ^ m • ⊤ : Submodule R R)) (sfun n) =
      Submodule.Quotient.mk (sfun m) := by
    intro m n hmn
    rw [Submodule.Quotient.eq]
    have hcoh := x.2 (show m + 1 ≤ n + 1 by omega)
    rw [← hr n, ← hr m] at hcoh
    have h5 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show m + 1 ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ (m + 1) • ⊤ : Submodule R R))
          (r n) := rfl
    rw [h5] at hcoh
    have h6 : r n - r m ∈
        ((Ideal.span {a}) ^ (m + 1) • ⊤ : Submodule R R) := by
      rw [← Submodule.Quotient.eq]
      exact hcoh
    rw [ideal_smul_top_self, Ideal.span_singleton_pow] at h6
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h6
    have h7 : a * (sfun n - sfun m) = a * (a ^ m * c) := by
      have h8 : a * sfun n - a * sfun m = a ^ (m + 1) * c := by
        rw [← hs n, ← hs m, ← hc]
        ring
      calc a * (sfun n - sfun m) = a * sfun n - a * sfun m := by ring
        _ = a ^ (m + 1) * c := h8
        _ = a * (a ^ m * c) := by ring
    have h9 : sfun n - sfun m = a ^ m * c :=
      (mul_cancel_left_mem_nonZeroDivisors ha).mp h7
    rw [ideal_smul_top_self, Ideal.span_singleton_pow, h9]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  refine ⟨⟨fun n => Submodule.Quotient.mk (sfun n), ?_⟩, ?_⟩
  · intro m n hmn
    have h10 : AdicCompletion.transitionMap (Ideal.span {a}) R hmn
        (Submodule.Quotient.mk (sfun n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ m • ⊤ : Submodule R R))
          (sfun n) := rfl
    rw [h10]
    exact hscoh hmn
  · refine Subtype.ext (funext fun n => ?_)
    show x.1 n = Submodule.Quotient.mk
      (p := ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)) (a * sfun n)
    rw [← hs n]
    have h12 := x.2 (show n ≤ n + 1 by omega)
    rw [← hr n] at h12
    have h13 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show n ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)) (r n) := rfl
    rw [h13] at h12
    exact h12.symm

/-- The level-one quotient map `AdicCompletion (a) R →+* R ⧸ (a)`. -/
noncomputable def AdicCompletion.toQuotientSpan (a : R) :
    AdicCompletion (Ideal.span {a}) R →+* R ⧸ Ideal.span {a} :=
  (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).toRingHom.comp
    (AdicCompletion.evalₐ (Ideal.span {a}) 1).toRingHom

theorem AdicCompletion.toQuotientSpan_surjective (a : R) :
    Function.Surjective (AdicCompletion.toQuotientSpan a) :=
  (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).surjective.comp
    (AdicCompletion.surjective_evalₐ (Ideal.span {a}) 1)

theorem AdicCompletion.toQuotientSpan_of (a r : R) :
    AdicCompletion.toQuotientSpan a
      (AdicCompletion.of (Ideal.span {a}) R r) =
    Ideal.Quotient.mk (Ideal.span {a}) r := by
  rw [AdicCompletion.toQuotientSpan, RingHom.comp_apply]
  have h1 : (AdicCompletion.evalₐ (Ideal.span {a}) 1).toRingHom
      (AdicCompletion.of (Ideal.span {a}) R r) =
      Ideal.Quotient.mk ((Ideal.span {a}) ^ 1) r := rfl
  rw [h1]
  exact Ideal.quotEquivOfEq_mk _ _

/-- **The kernel of the level-one quotient is generated by `a`** (tower
division; [hrw-decomposition] Tate leaf 4). -/
theorem AdicCompletion.ker_toQuotientSpan {a : R}
    (ha : a ∈ nonZeroDivisors R) :
    RingHom.ker (AdicCompletion.toQuotientSpan a) =
      Ideal.span {AdicCompletion.of (Ideal.span {a}) R a} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have h1 : AdicCompletion.evalₐ (Ideal.span {a}) 1 x = 0 := by
      have h2 := congrArg
        (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).symm hx
      rw [_root_.map_zero] at h2
      rw [show (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).symm
          (AdicCompletion.toQuotientSpan a x) =
        AdicCompletion.evalₐ (Ideal.span {a}) 1 x from by
          rw [AdicCompletion.toQuotientSpan]
          exact RingEquiv.symm_apply_apply _ _] at h2
      exact h2
    have h3 : x.1 1 = 0 := by
      refine (Ideal.quotientEquivAlgOfEq R (show
          ((Ideal.span {a}) ^ 1 • ⊤ : Ideal R) = (Ideal.span {a}) ^ 1 from
          by ext y; simp)).injective ?_
      rw [_root_.map_zero]
      exact h1
    obtain ⟨y, hy⟩ :=
      AdicCompletion.exists_eq_of_mul_of_component_one_eq_zero ha x h3
    rw [Ideal.mem_span_singleton']
    exact ⟨y, by rw [hy]; ring⟩
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← hy, map_mul, AdicCompletion.toQuotientSpan_of]
    have h6 : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    rw [h6, mul_zero]

/-- **The principal adic completion modulo its uniformizer** is the base
modulo the uniformizer. -/
noncomputable def AdicCompletion.quotientSpanEquiv {a : R}
    (ha : a ∈ nonZeroDivisors R) :
    (AdicCompletion (Ideal.span {a}) R ⧸
      Ideal.span {AdicCompletion.of (Ideal.span {a}) R a}) ≃+*
    R ⧸ Ideal.span {a} :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_toQuotientSpan ha).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.toQuotientSpan_surjective a))

end PrincipalAdicDivision

end AdicNakayama
