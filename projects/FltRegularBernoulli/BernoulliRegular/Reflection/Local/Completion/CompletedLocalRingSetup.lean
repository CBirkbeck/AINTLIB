module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import BernoulliRegular.Reflection.Local.Graded

/-!
# Completed local principal units

This file starts the REF-10d3b completed endpoint layer.  The localized ring
`Localization.AtPrime` is not complete, so the reverse `p`-power endpoint is
recorded in the adic completion at the cyclotomic maximal ideal.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section Binomial

variable {R : Type*} [CommSemiring R] {u v : R} {q : ℕ}

lemma exists_one_add_mul_pow_prime_eq_of_dvd
    (hq : q.Prime) (hvu : v ∣ u) (hquv : q * u * v ∣ u ^ q) (x : R) :
    ∃ y, (1 + u * x) ^ q = 1 + q * u * (x + v * y) := by
  rw [add_comm, add_pow]
  rw [← Finset.add_sum_erase (a := 0) _ _ (by simp)]
  simp_rw [one_pow, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [← Finset.add_sum_erase (a := 1) _ _ (by simp [hq.pos])]
  rw [← Finset.sum_erase_add (a := q) _ _ (by
      simp only [Finset.mem_erase]
      rw [← and_assoc, and_comm (a := ¬ _), ← Nat.two_le_iff]
      simp [hq.two_le])]
  obtain ⟨a, ha⟩ := hvu
  obtain ⟨b, hb⟩ := hquv
  use a * x ^ 2 * ∑ i ∈ (((Finset.range (q + 1)).erase 0).erase 1).erase q,
    (u * x) ^ (i - 2) * (q.choose i / q : ℕ) + b * x ^ q
  rw [mul_add]
  congr 2
  · rw [Nat.choose_one_right]
    ring
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · congr! 1 with i hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range] at hi
    have hi' : 2 ≤ i := by omega
    calc
      (u * x) ^ i * q.choose i =
          (u * x) ^ (2 + (i - 2)) * q.choose i := by rw [Nat.add_sub_of_le hi']
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * q.choose i := by ring
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * (q * (q.choose i / q) : ℕ) := by
        rw [Nat.mul_div_cancel' (hq.dvd_choose_self hi.2.2.1 (by omega))]
      _ = u ^ 2 * x ^ 2 * (u * x) ^ (i - 2) * q * (q.choose i / q : ℕ) := by
        simp only [Nat.cast_mul]
        ring
      _ = q * u * (v * (a * x ^ 2 * ((u * x) ^ (i - 2) * (q.choose i / q : ℕ)))) := by
        rw [ha]
        ring
  · calc
      (u * x) ^ q * (q.choose q) = u ^ q * x ^ q := by simp [Nat.choose_self, mul_pow]
      _ = q * u * v * b * x ^ q := by rw [hb]
      _ = q * u * (v * (b * x ^ q)) := by ring

end Binomial

section QuotientAux

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem factor_evalₐ_pow_le {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.ofLinearMap_apply]
  have htrans :
      AdicCompletion.transitionMap I R hmn ((AdicCompletion.eval I R n) x) =
        ((AdicCompletion.eval I R m) x) :=
    AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := R) hmn x
  rw [← htrans]
  induction ((AdicCompletion.eval I R n) x) using Quotient.inductionOn' with
  | h r =>
    rfl

private theorem mem_cotangentIdeal_iff_factor_pow_one_eq_zero (q : R ⧸ I ^ 2) :
    q ∈ I.cotangentIdeal ↔
      Ideal.Quotient.factor
        (show I ^ 2 ≤ I ^ 1 by exact Ideal.pow_le_pow_right one_le_two) q = 0 := by
  induction q using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ 2) r ∈ I.cotangentIdeal ↔
      Ideal.Quotient.factor
        (show I ^ 2 ≤ I ^ 1 by exact Ideal.pow_le_pow_right one_le_two)
        (Ideal.Quotient.mk (I ^ 2) r) = 0
    rw [Ideal.mk_mem_cotangentIdeal]
    change r ∈ I ↔ Ideal.Quotient.mk (I ^ 1) r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]

end QuotientAux

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The adic completion of the localized cyclotomic ring at its maximal ideal. -/
abbrev completedLocalCyclotomicRing :=
  AdicCompletion (localCyclotomicMaximalIdeal p K) (localCyclotomicRing p K)

/-- The completed maximal ideal, i.e. the extension of the local maximal ideal to the completion. -/
abbrev completedLocalCyclotomicMaximalIdeal :
    Ideal (completedLocalCyclotomicRing p K) :=
  Ideal.map (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K))
    (localCyclotomicMaximalIdeal p K)

/-- The completed local unit group. -/
abbrev completedLocalCyclotomicUnitGroup := (completedLocalCyclotomicRing p K)ˣ

/-- The local-to-completed map on cyclotomic local units. -/
noncomputable def completedLocalCyclotomicUnitMap :
    localCyclotomicUnitGroup p K →*
      completedLocalCyclotomicUnitGroup p K :=
  Units.map (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K))

/-- The distinguished cyclotomic root of unity in the completed local unit group. -/
noncomputable def completedLocalCyclotomicZetaUnit :
    completedLocalCyclotomicUnitGroup p K :=
  completedLocalCyclotomicUnitMap p K (localCyclotomicZetaUnit p K)

@[simp]
theorem completedLocalCyclotomicZetaUnit_coe :
    ((completedLocalCyclotomicZetaUnit p K : completedLocalCyclotomicUnitGroup p K) :
        completedLocalCyclotomicRing p K) =
      algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K)
        (localCyclotomicZetaUnit p K : localCyclotomicRing p K) :=
  rfl

@[simp]
theorem completedLocalCyclotomicZetaUnit_pow_eq_one :
    completedLocalCyclotomicZetaUnit p K ^ p = 1 := by
  rw [completedLocalCyclotomicZetaUnit, ← map_pow, localCyclotomicZetaUnit_pow_eq_one,
    map_one]

/-- The cyclotomic `p`-power roots of unity inside the completed local unit group. -/
noncomputable def completedLocalCyclotomicMuP :
    Subgroup (completedLocalCyclotomicUnitGroup p K) :=
  Subgroup.zpowers (completedLocalCyclotomicZetaUnit p K)

theorem completedLocalCyclotomicZetaUnit_mem_muP :
    completedLocalCyclotomicZetaUnit p K ∈ completedLocalCyclotomicMuP p K :=
  Subgroup.mem_zpowers _

theorem completedLocalCyclotomicMuP_le_powMonoidHom_ker :
    completedLocalCyclotomicMuP p K ≤
      (powMonoidHom p : completedLocalCyclotomicUnitGroup p K →*
        completedLocalCyclotomicUnitGroup p K).ker := by
  rw [completedLocalCyclotomicMuP]
  exact Subgroup.zpowers_le_of_mem (by
    rw [MonoidHom.mem_ker]
    exact completedLocalCyclotomicZetaUnit_pow_eq_one (p := p) (K := K))

theorem completedLocalCyclotomicMuP_pow_eq_one
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedLocalCyclotomicMuP p K) :
    u ^ p = 1 := by
  have hker := completedLocalCyclotomicMuP_le_powMonoidHom_ker (p := p) (K := K) hu
  rw [MonoidHom.mem_ker] at hker
  exact hker

instance completedLocalCyclotomic_isAdicComplete :
    IsAdicComplete (completedLocalCyclotomicMaximalIdeal p K)
      (completedLocalCyclotomicRing p K) := by
  rw [completedLocalCyclotomicMaximalIdeal, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete
    (localCyclotomicMaximalIdeal_isPrincipal (p := p) (K := K)).fg

instance completedLocalCyclotomic_henselianRing :
    HenselianRing (completedLocalCyclotomicRing p K)
      (completedLocalCyclotomicMaximalIdeal p K) :=
  @IsAdicComplete.henselianRing (completedLocalCyclotomicRing p K) _
    (completedLocalCyclotomicMaximalIdeal p K)
    (completedLocalCyclotomic_isAdicComplete (p := p) (K := K))

/-- The localized cyclotomic uniformizer, mapped to the completed local ring. -/
def completedLocalCyclotomicUniformizer : completedLocalCyclotomicRing p K :=
  algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K)
    (localCyclotomicUniformizer p K)

theorem completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer :
    completedLocalCyclotomicMaximalIdeal p K =
      Ideal.span ({completedLocalCyclotomicUniformizer p K} :
        Set (completedLocalCyclotomicRing p K)) := by
  simp [completedLocalCyclotomicMaximalIdeal, completedLocalCyclotomicUniformizer,
    localCyclotomicMaximalIdeal_eq_span_uniformizer, Ideal.map_span]

theorem localCyclotomicUniformizer_not_mem_maximalIdeal_sq :
    localCyclotomicUniformizer p K ∉ localCyclotomicMaximalIdeal p K ^ 2 := by
  have hnot := localCyclotomicZetaUnit_not_mem_principalUnitSubgroup_two (p := p) (K := K)
  rw [mem_principalUnitSubgroup_iff] at hnot
  simpa [localCyclotomicUniformizer, map_sub, map_one] using hnot

theorem completedLocalCyclotomicMaximalIdeal_eq_ker_evalOne :
    completedLocalCyclotomicMaximalIdeal p K =
      RingHom.ker (AdicCompletion.evalOneₐ (localCyclotomicMaximalIdeal p K)).toRingHom := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  have hfg : M.FG := (localCyclotomicMaximalIdeal_isPrincipal (p := p) (K := K)).fg
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker]
    have hxsmul : x ∈ M ^ 1 • (⊤ : Submodule R S) := by
      rw [pow_one, Ideal.smul_top_eq_map]
      simpa [S, R, M, completedLocalCyclotomicMaximalIdeal] using hx
    have hxker : x ∈ LinearMap.ker (AdicCompletion.eval M R 1) := by
      rw [← AdicCompletion.pow_smul_top_eq_ker_eval (I := M) (M := R) hfg (n := 1)]
      exact hxsmul
    have heval : AdicCompletion.eval M R 1 x = 0 := LinearMap.mem_ker.mp hxker
    change AdicCompletion.evalOneₐ M x = 0
    rw [← AdicCompletion.factorₐ_evalₐ_one (I := M) x]
    have hle : M ^ 1 • (⊤ : Ideal R) ≤ M ^ 1 := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← AdicCompletion.factor_eval_eq_evalₐ (I := M) (R := R) (n := 1) (x := x) hle,
      heval, map_zero, map_zero]
  · intro hx
    rw [RingHom.mem_ker] at hx
    change AdicCompletion.evalOneₐ M x = 0 at hx
    have hevalₐ : AdicCompletion.evalₐ M 1 x = 0 := by
      have hfactor :
          Ideal.Quotient.factor (show M ^ 1 ≤ M by simp) (AdicCompletion.evalₐ M 1 x) =
            0 := by
        rw [AdicCompletion.factorₐ_evalₐ_one (I := M) x]
        exact hx
      have hEq : M ^ 1 = M := by rw [pow_one]
      apply (Ideal.quotEquivOfEq hEq).injective
      simpa [Ideal.quotEquivOfEq_eq_factor hEq] using hfactor
    have heval : AdicCompletion.eval M R 1 x = 0 := by
      have hle : M ^ 1 ≤ M ^ 1 • (⊤ : Ideal R) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      have hfac := AdicCompletion.factor_evalₐ_eq_eval (I := M) (R := R) (n := 1) (x := x) hle
      rw [← hfac, hevalₐ, map_zero]
    have hxker : x ∈ LinearMap.ker (AdicCompletion.eval M R 1) :=
      LinearMap.mem_ker.mpr heval
    have hxsmul : x ∈ M ^ 1 • (⊤ : Submodule R S) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := M) (M := R) hfg (n := 1)]
      exact hxker
    rw [pow_one, Ideal.smul_top_eq_map] at hxsmul
    simpa [S, R, M, completedLocalCyclotomicMaximalIdeal] using hxsmul

theorem completedLocalCyclotomicUniformizer_ne_zero :
    completedLocalCyclotomicUniformizer p K ≠ 0 := by
  intro hzero
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  have heval :
      AdicCompletion.evalₐ M 2 (completedLocalCyclotomicUniformizer p K) = 0 := by
    rw [hzero, map_zero]
  have hmk : Ideal.Quotient.mk (M ^ 2) (localCyclotomicUniformizer p K) = 0 := by
    simpa [R, M, completedLocalCyclotomicUniformizer] using heval
  exact localCyclotomicUniformizer_not_mem_maximalIdeal_sq (p := p) (K := K)
    (Ideal.Quotient.eq_zero_iff_mem.mp hmk)

theorem completedLocalCyclotomicMaximalIdeal_isPrincipal :
    Submodule.IsPrincipal (completedLocalCyclotomicMaximalIdeal p K) := by
  rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer, Submodule.isPrincipal_iff]
  exact ⟨completedLocalCyclotomicUniformizer p K, rfl⟩

theorem completedLocalCyclotomicMaximalIdeal_ne_bot :
    completedLocalCyclotomicMaximalIdeal p K ≠ ⊥ := by
  intro hbot
  have hmem : completedLocalCyclotomicUniformizer p K ∈
      completedLocalCyclotomicMaximalIdeal p K := by
    rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer]
    exact Ideal.mem_span_singleton_self (completedLocalCyclotomicUniformizer p K)
  have hzero : completedLocalCyclotomicUniformizer p K = 0 := by
    simpa [hbot] using hmem
  exact completedLocalCyclotomicUniformizer_ne_zero (p := p) (K := K) hzero

theorem completedLocalCyclotomicMaximalIdeal_pow_le_ker_evalₐ (n : ℕ) :
    completedLocalCyclotomicMaximalIdeal p K ^ n ≤
      RingHom.ker (AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n).toRingHom := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  change (Ideal.map (algebraMap R S) M) ^ n ≤
    RingHom.ker (AdicCompletion.evalₐ M n).toRingHom
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker]
  simpa [R, M] using (Ideal.Quotient.eq_zero_iff_mem.mpr hx :
    Ideal.Quotient.mk (M ^ n) x = 0)

theorem completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    completedLocalCyclotomicMaximalIdeal p K ^ n =
      RingHom.ker (AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n).toRingHom := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  have hfg : M.FG := (localCyclotomicMaximalIdeal_isPrincipal (p := p) (K := K)).fg
  ext x
  constructor
  · intro hx
    exact completedLocalCyclotomicMaximalIdeal_pow_le_ker_evalₐ (p := p) (K := K) n hx
  · intro hx
    rw [RingHom.mem_ker] at hx
    change AdicCompletion.evalₐ M n x = 0 at hx
    have heval : AdicCompletion.eval M R n x = 0 := by
      have hle : M ^ n ≤ M ^ n • (⊤ : Ideal R) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      have hfac := AdicCompletion.factor_evalₐ_eq_eval (I := M) (R := R) (n := n) (x := x) hle
      rw [← hfac, hx, map_zero]
    have hxker : x ∈ LinearMap.ker (AdicCompletion.eval M R n) :=
      LinearMap.mem_ker.mpr heval
    have hxsmul : x ∈ M ^ n • (⊤ : Submodule R S) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := M) (M := R) hfg (n := n)]
      exact hxker
    rw [Ideal.smul_top_eq_map] at hxsmul
    rw [← Ideal.map_pow]
    simpa [S, R, M, completedLocalCyclotomicMaximalIdeal] using hxsmul

/-- The second completed quotient is the original second local quotient, as a plain type
equivalence. -/
noncomputable def completedQuotientSquareEquivLocalQuotientSquare :
    completedLocalCyclotomicRing p K ⧸ completedLocalCyclotomicMaximalIdeal p K ^ 2 ≃
      localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ 2 := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  let f : S → R ⧸ M ^ 2 := AdicCompletion.evalₐ M 2
  let e : S ⧸ Mhat ^ 2 → R ⧸ M ^ 2 :=
    fun q ↦ Quotient.liftOn' q f (by
      intro a b h
      rw [← sub_eq_zero, ← map_sub]
      have hker : a - b ∈ RingHom.ker (AdicCompletion.evalₐ M 2).toRingHom := by
        rw [← completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) 2]
        simpa [Mhat] using ((Submodule.quotientRel_def (p := Mhat ^ 2)).mp h)
      exact RingHom.mem_ker.mp hker)
  refine Equiv.ofBijective e ?_
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      change f a = f b at hxy
      apply Ideal.Quotient.eq.mpr
      rw [completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) 2,
        RingHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hxy
  · intro y
    rcases AdicCompletion.surjective_evalₐ M 2 y with ⟨x, hx⟩
    refine ⟨Quotient.mk'' x, ?_⟩
    change f x = y
    exact hx

@[simp]
theorem completedQuotientSquareEquivLocalQuotientSquare_mk
    (x : completedLocalCyclotomicRing p K) :
    completedQuotientSquareEquivLocalQuotientSquare (p := p) (K := K)
      (Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ 2) x) =
        AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) 2 x := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk]
  rfl

/-- The map on second quotients induced by the local-to-completed algebra map. -/
noncomputable def localQuotientSquareToCompletedQuotientSquare :
    localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ 2 ≃
      completedLocalCyclotomicRing p K ⧸ completedLocalCyclotomicMaximalIdeal p K ^ 2 := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  let g : R ⧸ M ^ 2 → S ⧸ Mhat ^ 2 :=
    fun q ↦ Quotient.liftOn' q
      (fun r ↦ Ideal.Quotient.mk (Mhat ^ 2) (algebraMap R S r))
      (by
        intro a b h
        rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (algebraMap R S)
          ((Submodule.quotientRel_def (p := M ^ 2)).mp h))
  let e := completedQuotientSquareEquivLocalQuotientSquare (p := p) (K := K)
  have hleft : Function.LeftInverse e g := by
    intro q
    induction q using Quotient.inductionOn' with
    | h r =>
      calc
        e ((algebraMap R (S ⧸ Mhat ^ 2)) r) =
            e (Ideal.Quotient.mk (Mhat ^ 2) (algebraMap R S r)) := rfl
        _ = AdicCompletion.evalₐ M 2 (algebraMap R S r) := by
          rw [completedQuotientSquareEquivLocalQuotientSquare_mk]
        _ = Ideal.Quotient.mk (M ^ 2) r := by
          change AdicCompletion.evalₐ M 2 (AdicCompletion.of M R r) =
            Ideal.Quotient.mk (M ^ 2) r
          exact AdicCompletion.evalₐ_of (I := M) 2 r
  refine ⟨g, e, hleft, ?_⟩
  intro q
  exact e.injective (hleft (e q))

@[simp]
theorem localQuotientSquareToCompletedQuotientSquare_mk
    (x : localCyclotomicRing p K) :
    localQuotientSquareToCompletedQuotientSquare (p := p) (K := K)
      (Ideal.Quotient.mk ((localCyclotomicMaximalIdeal p K) ^ 2) x) =
        Ideal.Quotient.mk ((completedLocalCyclotomicMaximalIdeal p K) ^ 2)
          (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K) x) :=
  rfl

theorem completedQuotientSquareEquivLocalQuotientSquare_mem_cotangentIdeal
    {q : completedLocalCyclotomicRing p K ⧸
        completedLocalCyclotomicMaximalIdeal p K ^ 2}
    (hq : q ∈ (completedLocalCyclotomicMaximalIdeal p K).cotangentIdeal) :
    completedQuotientSquareEquivLocalQuotientSquare (p := p) (K := K) q ∈
      (localCyclotomicMaximalIdeal p K).cotangentIdeal := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  rcases hq with ⟨x, hx, rfl⟩
  change completedQuotientSquareEquivLocalQuotientSquare (p := p) (K := K)
      (Ideal.Quotient.mk (Mhat ^ 2) x) ∈ M.cotangentIdeal
  rw [completedQuotientSquareEquivLocalQuotientSquare_mk,
    mem_cotangentIdeal_iff_factor_pow_one_eq_zero, factor_evalₐ_pow_le M one_le_two]
  have hxker : x ∈ RingHom.ker (AdicCompletion.evalₐ M 1).toRingHom := by
    rw [← completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) 1]
    simpa [Mhat] using hx
  rw [RingHom.mem_ker] at hxker
  exact hxker

theorem localQuotientSquareToCompletedQuotientSquare_mem_cotangentIdeal
    {q : localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K ^ 2}
    (hq : q ∈ (localCyclotomicMaximalIdeal p K).cotangentIdeal) :
    localQuotientSquareToCompletedQuotientSquare (p := p) (K := K) q ∈
      (completedLocalCyclotomicMaximalIdeal p K).cotangentIdeal := by
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let Mhat : Ideal S := completedLocalCyclotomicMaximalIdeal p K
  induction q using Quotient.inductionOn' with
  | h r =>
    change localQuotientSquareToCompletedQuotientSquare (p := p) (K := K)
        (Ideal.Quotient.mk (M ^ 2) r) ∈ Mhat.cotangentIdeal
    rw [localQuotientSquareToCompletedQuotientSquare_mk, Ideal.mk_mem_cotangentIdeal]
    have hr : r ∈ M :=
      (Ideal.mk_mem_cotangentIdeal (I := M) (x := r)).mp hq
    exact Ideal.mem_map_of_mem (algebraMap R S) hr

/-- The completed cotangent ideal is the original local cotangent ideal. -/
noncomputable def completedCotangentIdealEquivLocalCotangentIdeal :
    (completedLocalCyclotomicMaximalIdeal p K).cotangentIdeal ≃
      (localCyclotomicMaximalIdeal p K).cotangentIdeal where
  toFun q :=
    ⟨completedQuotientSquareEquivLocalQuotientSquare (p := p) (K := K) q.1,
      completedQuotientSquareEquivLocalQuotientSquare_mem_cotangentIdeal
        (p := p) (K := K) q.2⟩
  invFun q :=
    ⟨localQuotientSquareToCompletedQuotientSquare (p := p) (K := K) q.1,
      localQuotientSquareToCompletedQuotientSquare_mem_cotangentIdeal
        (p := p) (K := K) q.2⟩
  left_inv q := by
    ext
    exact Equiv.apply_symm_apply
      (localQuotientSquareToCompletedQuotientSquare (p := p) (K := K)) q.1
  right_inv q := by
    ext
    exact Equiv.symm_apply_apply
      (localQuotientSquareToCompletedQuotientSquare (p := p) (K := K)) q.1

theorem completedCotangentCard :
    Nat.card (completedLocalCyclotomicMaximalIdeal p K).Cotangent = p := by
  let Mhat := completedLocalCyclotomicMaximalIdeal p K
  let M := localCyclotomicMaximalIdeal p K
  calc
    Nat.card Mhat.Cotangent = Nat.card Mhat.cotangentIdeal :=
      Nat.card_congr (Mhat.cotangentEquivIdeal).toEquiv
    _ = Nat.card M.cotangentIdeal :=
      Nat.card_congr (completedCotangentIdealEquivLocalCotangentIdeal (p := p) (K := K))
    _ = Nat.card M.Cotangent :=
      (Nat.card_congr (M.cotangentEquivIdeal).toEquiv).symm
    _ = p := localCotangentCard (p := p) (K := K)

theorem completedCotangentMultiplicativeCard :
    Nat.card (Multiplicative (completedLocalCyclotomicMaximalIdeal p K).Cotangent) = p :=
  (Nat.card_congr Multiplicative.toAdd).trans
    (completedCotangentCard (p := p) (K := K))

theorem completedLocalCyclotomicMaximalIdeal_pow_eq_span_uniformizer_pow (n : ℕ) :
    completedLocalCyclotomicMaximalIdeal p K ^ n =
      Ideal.span ({completedLocalCyclotomicUniformizer p K ^ n} :
        Set (completedLocalCyclotomicRing p K)) := by
  rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer]
  exact Ideal.span_singleton_pow (completedLocalCyclotomicUniformizer p K) n

theorem exists_uniformizer_pow_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow
    {n : ℕ} {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ n) :
    ∃ y, completedLocalCyclotomicUniformizer p K ^ n * y = x := by
  rw [completedLocalCyclotomicMaximalIdeal_pow_eq_span_uniformizer_pow] at hx
  rcases Ideal.mem_span_singleton.mp hx with ⟨y, hy⟩
  exact ⟨y, hy.symm⟩

/-- Exact ramification at the localized cyclotomic prime: `(p) = m^(p-1)`. -/
theorem span_natCast_prime_eq_localCyclotomicMaximalIdeal_pow_pred :
    Ideal.span ({(p : localCyclotomicRing p K)} : Set (localCyclotomicRing p K)) =
      localCyclotomicMaximalIdeal p K ^ (p - 1) := by
  let Rloc := localCyclotomicRing p K
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hglobal : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span ({(p : ℤ)} : Set ℤ)) =
      cyclotomicLambda p K ^ (p - 1) := by
    simpa [cyclotomicLambda, zetaPrime, hfin] using
      (IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ)
  have hmap := congrArg (Ideal.map (algebraMap (𝓞 K) Rloc)) hglobal
  rw [Ideal.map_map] at hmap
  rw [Ideal.map_pow, localCyclotomicMaximalIdeal_eq_map p K] at hmap
  simpa [Rloc, Ideal.map_span] using hmap

/-- Exact ramification after completion: `(p) = completed_m^(p-1)`. -/
theorem span_natCast_prime_eq_completedLocalCyclotomicMaximalIdeal_pow_pred :
    Ideal.span ({(p : completedLocalCyclotomicRing p K)} :
        Set (completedLocalCyclotomicRing p K)) =
      completedLocalCyclotomicMaximalIdeal p K ^ (p - 1) := by
  let Rloc := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  have hlocal := span_natCast_prime_eq_localCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  have hmap := congrArg (Ideal.map (algebraMap Rloc S)) hlocal
  rw [Ideal.map_pow] at hmap
  simpa [S, Rloc, completedLocalCyclotomicMaximalIdeal, Ideal.map_span] using hmap

theorem natCast_prime_dvd_completedLocalCyclotomicUniformizer_pow_pred :
    (p : completedLocalCyclotomicRing p K) ∣
      completedLocalCyclotomicUniformizer p K ^ (p - 1) := by
  have hmem : completedLocalCyclotomicUniformizer p K ^ (p - 1) ∈
      Ideal.span ({(p : completedLocalCyclotomicRing p K)} :
        Set (completedLocalCyclotomicRing p K)) := by
    rw [span_natCast_prime_eq_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K),
      completedLocalCyclotomicMaximalIdeal_pow_eq_span_uniformizer_pow]
    exact Ideal.mem_span_singleton_self (completedLocalCyclotomicUniformizer p K ^ (p - 1))
  exact Ideal.mem_span_singleton.mp hmem

theorem natCast_prime_mul_uniformizer_pow_mul_uniformizer_dvd_uniformizer_pow_prime
    {n : ℕ} (hn : 2 ≤ n) :
    (p : completedLocalCyclotomicRing p K) *
        completedLocalCyclotomicUniformizer p K ^ n *
        completedLocalCyclotomicUniformizer p K ∣
      (completedLocalCyclotomicUniformizer p K ^ n) ^ p := by
  let S := completedLocalCyclotomicRing p K
  let π : S := completedLocalCyclotomicUniformizer p K
  rcases natCast_prime_dvd_completedLocalCyclotomicUniformizer_pow_pred (p := p) (K := K) with
    ⟨c, hc⟩
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hle_pred : p ≤ n * (p - 1) := by
    have htwo : p ≤ 2 * (p - 1) := by omega
    exact htwo.trans (Nat.mul_le_mul_right (p - 1) hn)
  have hmul : n * p = n + n * (p - 1) := by
    calc
      n * p = n * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp_one]
      _ = n * (p - 1) + n := by rw [Nat.mul_add, Nat.mul_one]
      _ = n + n * (p - 1) := by rw [Nat.add_comm]
  have hle : p + n ≤ n * p := by
    rw [hmul, Nat.add_comm p n]
    exact Nat.add_le_add_left hle_pred n
  refine ⟨c * π ^ (n * p - (p + n)), ?_⟩
  have hpn : p + n = (p - 1) + n + 1 := by omega
  have hpown : π ^ (p + n) = ((p : S) * π ^ n * π) * c := by
    calc
      π ^ (p + n) = π ^ ((p - 1) + n + 1) := by rw [hpn]
      _ = (π ^ (p - 1) * π ^ n) * π := by rw [pow_add, pow_add, pow_one]
      _ = ((p : S) * π ^ n * π) * c := by
        rw [hc]
        ring
  calc
    (π ^ n) ^ p = π ^ (n * p) := by rw [pow_mul]
    _ = π ^ (p + n) * π ^ (n * p - (p + n)) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    _ = ((p : S) * π ^ n * π) * (c * π ^ (n * p - (p + n))) := by
      rw [hpown]
      ring

theorem natCast_prime_mem_completedLocalCyclotomicMaximalIdeal_pow_pred :
    (p : completedLocalCyclotomicRing p K) ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (p - 1) := by
  rw [← span_natCast_prime_eq_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)]
  exact Ideal.mem_span_singleton_self (p : completedLocalCyclotomicRing p K)

theorem natCast_prime_mem_completedLocalCyclotomicMaximalIdeal :
    (p : completedLocalCyclotomicRing p K) ∈ completedLocalCyclotomicMaximalIdeal p K := by
  have hp : (p : completedLocalCyclotomicRing p K) ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (p - 1) :=
    natCast_prime_mem_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)
  exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Fact.out : Nat.Prime p).one_lt) hp

theorem completedLocalCyclotomicMaximalIdeal_pow_add_pred_eq_mul_span_natCast (n : ℕ) :
    completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1)) =
      completedLocalCyclotomicMaximalIdeal p K ^ n *
        Ideal.span ({(p : completedLocalCyclotomicRing p K)} :
          Set (completedLocalCyclotomicRing p K)) := by
  rw [pow_add,
    ← span_natCast_prime_eq_completedLocalCyclotomicMaximalIdeal_pow_pred (p := p) (K := K)]

theorem completedLocalCyclotomicMaximalIdeal_pow_add_pred_eq_span_natCast_mul (n : ℕ) :
    completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1)) =
      Ideal.span ({(p : completedLocalCyclotomicRing p K)} :
        Set (completedLocalCyclotomicRing p K)) *
        completedLocalCyclotomicMaximalIdeal p K ^ n := by
  rw [completedLocalCyclotomicMaximalIdeal_pow_add_pred_eq_mul_span_natCast (p := p) (K := K),
    mul_comm]

theorem exists_natCast_prime_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow_add_pred
    {n : ℕ} {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ (n + (p - 1))) :
    ∃ y, y ∈ completedLocalCyclotomicMaximalIdeal p K ^ n ∧
      (p : completedLocalCyclotomicRing p K) * y = x := by
  have hx' : x ∈
      Ideal.span ({(p : completedLocalCyclotomicRing p K)} :
        Set (completedLocalCyclotomicRing p K)) *
        completedLocalCyclotomicMaximalIdeal p K ^ n := by
    simpa [completedLocalCyclotomicMaximalIdeal_pow_add_pred_eq_span_natCast_mul
      (p := p) (K := K) n] using hx
  exact Ideal.mem_span_singleton_mul.mp hx'

theorem isUnit_one_add_of_mem_completedLocalCyclotomicMaximalIdeal
    {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K) : IsUnit (1 + x) := by
  have hH : HenselianRing (completedLocalCyclotomicRing p K)
      (completedLocalCyclotomicMaximalIdeal p K) :=
    completedLocalCyclotomic_henselianRing (p := p) (K := K)
  have hxjac : x ∈ Ideal.jacobson (⊥ : Ideal (completedLocalCyclotomicRing p K)) :=
    hH.jac hx
  simpa [mul_comm, add_comm] using (Ideal.mem_jacobson_bot.mp hxjac 1)

/-- The unit `1 + x` for `x` in a positive completed maximal-ideal power. -/
noncomputable def completedOneAddUnitOfMemMaximalIdealPow {n : ℕ} (hn : n ≠ 0)
    {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ n) :
    completedLocalCyclotomicUnitGroup p K :=
  (isUnit_one_add_of_mem_completedLocalCyclotomicMaximalIdeal (p := p) (K := K)
    (Ideal.pow_le_self hn hx)).unit

@[simp]
theorem completedOneAddUnitOfMemMaximalIdealPow_coe {n : ℕ} (hn : n ≠ 0)
    {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ n) :
    (completedOneAddUnitOfMemMaximalIdealPow (p := p) (K := K) hn hx :
      completedLocalCyclotomicRing p K) = 1 + x :=
  (isUnit_one_add_of_mem_completedLocalCyclotomicMaximalIdeal (p := p) (K := K)
    (Ideal.pow_le_self hn hx)).unit_spec

/-- The completed principal-unit filtration. -/
def completedPrincipalUnitSubgroup (n : ℕ) :
    Subgroup (completedLocalCyclotomicUnitGroup p K) :=
  Ideal.oneUnitsSubgroup ((completedLocalCyclotomicMaximalIdeal p K) ^ n)

@[simp]
theorem mem_completedPrincipalUnitSubgroup_iff {n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K} :
    u ∈ completedPrincipalUnitSubgroup p K n ↔
      (u : completedLocalCyclotomicRing p K) - 1 ∈
        (completedLocalCyclotomicMaximalIdeal p K) ^ n := by
  change u ∈ Ideal.oneUnitsSubgroup ((completedLocalCyclotomicMaximalIdeal p K) ^ n) ↔
    (u : completedLocalCyclotomicRing p K) - 1 ∈
      (completedLocalCyclotomicMaximalIdeal p K) ^ n
  exact Ideal.mem_oneUnitsSubgroup

/-- The completed principal-unit filtration is antitone in the index. -/
theorem completedPrincipalUnitSubgroup_mono {m n : ℕ} (h : n ≤ m) :
    completedPrincipalUnitSubgroup p K m ≤ completedPrincipalUnitSubgroup p K n := by
  intro u hu
  rw [mem_completedPrincipalUnitSubgroup_iff] at hu ⊢
  exact Ideal.pow_le_pow_right h hu

/-- The completed distinguished cyclotomic root is a principal unit. -/
theorem completedLocalCyclotomicZetaUnit_mem_completedPrincipalUnitSubgroup_one :
    completedLocalCyclotomicZetaUnit p K ∈ completedPrincipalUnitSubgroup p K 1 := by
  rw [mem_completedPrincipalUnitSubgroup_iff, pow_one]
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  have hzeta : (localCyclotomicZetaUnit p K : R) - 1 ∈ M := by
    simpa [R, M] using
      (mem_principalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := localCyclotomicZetaUnit p K)).mp
        (localCyclotomicZetaUnit_mem_principalUnitSubgroup_one (p := p) (K := K))
  have hmap : algebraMap R S ((localCyclotomicZetaUnit p K : R) - 1) ∈
      completedLocalCyclotomicMaximalIdeal p K :=
    Ideal.mem_map_of_mem (algebraMap R S) hzeta
  simpa [S, R, completedLocalCyclotomicZetaUnit, completedLocalCyclotomicUnitMap,
    map_sub, map_one] using hmap

theorem completedLocalCyclotomicMuP_le_completedPrincipalUnitSubgroup_one :
    completedLocalCyclotomicMuP p K ≤ completedPrincipalUnitSubgroup p K 1 := by
  rw [completedLocalCyclotomicMuP]
  exact Subgroup.zpowers_le_of_mem
    (completedLocalCyclotomicZetaUnit_mem_completedPrincipalUnitSubgroup_one
      (p := p) (K := K))

theorem completedLocalCyclotomicZetaUnit_not_mem_completedPrincipalUnitSubgroup_two :
    completedLocalCyclotomicZetaUnit p K ∉ completedPrincipalUnitSubgroup p K 2 := by
  intro hzeta
  rw [mem_completedPrincipalUnitSubgroup_iff] at hzeta
  let R := localCyclotomicRing p K
  let S := completedLocalCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  have heval_zero : AdicCompletion.evalₐ M 2
      ((completedLocalCyclotomicZetaUnit p K : S) - 1) = 0 :=
    RingHom.mem_ker.mp
      (completedLocalCyclotomicMaximalIdeal_pow_le_ker_evalₐ (p := p) (K := K) 2 hzeta)
  have hcoe : ((completedLocalCyclotomicZetaUnit p K : S) - 1) =
      algebraMap R S ((localCyclotomicZetaUnit p K : R) - 1) := by
    simp [S, R, completedLocalCyclotomicZetaUnit, completedLocalCyclotomicUnitMap,
      map_sub, map_one]
  rw [hcoe] at heval_zero
  have hlocal_zero : Ideal.Quotient.mk (M ^ 2)
      ((localCyclotomicZetaUnit p K : R) - 1) = 0 := by
    have hof : AdicCompletion.evalₐ M 2
        (algebraMap R S ((localCyclotomicZetaUnit p K : R) - 1)) =
          Ideal.Quotient.mk (M ^ 2) ((localCyclotomicZetaUnit p K : R) - 1) :=
      AdicCompletion.evalₐ_of (I := M) 2 ((localCyclotomicZetaUnit p K : R) - 1)
    rw [← hof]
    exact heval_zero
  exact localCyclotomicZetaUnit_not_mem_principalUnitSubgroup_two (p := p) (K := K) (by
    rw [mem_principalUnitSubgroup_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hlocal_zero)

@[simp]
theorem completedPrincipalUnitSubgroup_zero :
    completedPrincipalUnitSubgroup p K 0 = ⊤ := by
  simp [completedPrincipalUnitSubgroup]

@[simp]
theorem one_mem_completedPrincipalUnitSubgroup (n : ℕ) :
    (1 : completedLocalCyclotomicUnitGroup p K) ∈ completedPrincipalUnitSubgroup p K n :=
  (completedPrincipalUnitSubgroup p K n).one_mem

/-- The subgroup of completed `q`-th powers of `U_n`. -/
def completedPrincipalUnitPowerSubgroup (q n : ℕ) :
    Subgroup (completedLocalCyclotomicUnitGroup p K) :=
  (completedPrincipalUnitSubgroup p K n).map (powMonoidHom q)

@[simp]
theorem mem_completedPrincipalUnitPowerSubgroup_iff {q n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K} :
    u ∈ completedPrincipalUnitPowerSubgroup p K q n ↔
      ∃ v, v ∈ completedPrincipalUnitSubgroup p K n ∧ v ^ q = u := by
  rfl

theorem completedPrincipalUnitPowerSubgroup_le (q n : ℕ) :
    completedPrincipalUnitPowerSubgroup p K q n ≤ completedPrincipalUnitSubgroup p K n := by
  intro u hu
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact (completedPrincipalUnitSubgroup p K n).pow_mem hv q

/-- The first completed graded map `completed U_1 -> completed m / completed m^2`. -/
noncomputable def completedPrincipalUnitFirstGradedHom :
    completedPrincipalUnitSubgroup p K 1 →*
      Multiplicative (completedLocalCyclotomicMaximalIdeal p K).Cotangent :=
  let M := completedLocalCyclotomicMaximalIdeal p K
  let toOneUnits : completedPrincipalUnitSubgroup p K 1 →* Ideal.oneUnitsSubgroup M :=
  {
    toFun := fun u ↦ ⟨(u : completedLocalCyclotomicUnitGroup p K), by
      have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
      simpa [M] using hu⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
  }
  (Ideal.oneUnitsCotangentHom M).comp toOneUnits

/-- The kernel of the completed first graded map is completed `U_2`. -/
theorem mem_completedPrincipalUnitFirstGradedHom_ker
    {u : completedPrincipalUnitSubgroup p K 1} :
    u ∈ (completedPrincipalUnitFirstGradedHom p K).ker ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈
        completedPrincipalUnitSubgroup p K 2 := by
  let M := completedLocalCyclotomicMaximalIdeal p K
  change (⟨(u : completedLocalCyclotomicUnitGroup p K), by
      have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
      simpa [M] using hu⟩ : Ideal.oneUnitsSubgroup M) ∈
        (Ideal.oneUnitsCotangentHom M).ker ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈ completedPrincipalUnitSubgroup p K 2
  rw [Ideal.mem_oneUnitsCotangentHom_ker]
  constructor
  · intro h
    rw [mem_completedPrincipalUnitSubgroup_iff]
    simpa [M] using h
  · intro h
    have hmem := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := 2)
      (u := (u : completedLocalCyclotomicUnitGroup p K))).mp h
    simpa [M] using hmem

theorem completedPrincipalUnitFirstGradedHom_ker :
    (completedPrincipalUnitFirstGradedHom p K).ker =
      (completedPrincipalUnitSubgroup p K 2).subgroupOf
        (completedPrincipalUnitSubgroup p K 1) := by
  ext u
  rw [mem_completedPrincipalUnitFirstGradedHom_ker, Subgroup.mem_subgroupOf]

theorem completedPrincipalUnitFirstGradedHom_surjective :
    Function.Surjective (completedPrincipalUnitFirstGradedHom p K) := by
  intro y
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  obtain ⟨x, hx⟩ := M.toCotangent_surjective (Multiplicative.toAdd y)
  have hunit : IsUnit (1 + (x : S)) :=
    isUnit_one_add_of_mem_completedLocalCyclotomicMaximalIdeal (p := p) (K := K) x.2
  let u0 : completedLocalCyclotomicUnitGroup p K := hunit.unit
  have hu0_val : (u0 : S) = 1 + (x : S) := hunit.unit_spec
  have hu1 : u0 ∈ completedPrincipalUnitSubgroup p K 1 := by
    rw [mem_completedPrincipalUnitSubgroup_iff]
    change (u0 : S) - 1 ∈ M ^ 1
    rw [hu0_val, add_sub_cancel_left, pow_one]
    exact x.2
  refine ⟨⟨u0, hu1⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change M.toCotangent ⟨(u0 : S) - 1, by
      have hu := (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := 1)
        (u := u0)).mp hu1
      rw [← pow_one M]
      exact hu⟩ = Multiplicative.toAdd y
  rw [← hx]
  apply congrArg M.toCotangent
  ext
  simp [hu0_val]

end CyclotomicSetup
end Local
end Reflection
end BernoulliRegular
