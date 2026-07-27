import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Support

/-!
# Patching a finite ring homomorphism across a Cartier divisor

A finite ring homomorphism is bijective if it is bijective away from a
source nonzerodivisor and surjective modulo the corresponding principal
ideal.
-/

open scoped Pointwise

namespace RingHom.Finite

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A finite ring homomorphism that is an isomorphism away from a Cartier
divisor and is surjective along that divisor is bijective. -/
theorem bijective_of_awayMap_bijective_of_mod_span
    (f : R →+* S) (hf : f.Finite) (r : R)
    (hr : r ∈ nonZeroDivisors R)
    (hAway : Function.Bijective (Localization.awayMap f r))
    (hMod : ∀ b : S, ∃ a : R, b - f a ∈ Ideal.span {f r}) :
    Function.Bijective f := by
  algebraize [f]
  haveI : Module.Finite R S := hf
  have hAwayKer : ∀ a : R, f a = 0 → ∃ n : ℕ, r ^ n * a = 0 :=
    Localization.awayMap_injective_iff.mp hAway.1
  have hAwayCoker : ∀ b : S, ∃ (a : R) (n : ℕ), f a = f r ^ n * b :=
    Localization.awayMap_surjective_iff.mp hAway.2
  let l : R →ₗ[R] S := Algebra.linearMap R S
  let Q := S ⧸ LinearMap.range l
  haveI : Module.Finite R Q := Module.Finite.quotient R _
  constructor
  · intro a b hab
    have hzero : f (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨n, hn⟩ := hAwayKer (a - b) hzero
    have hab' : a - b = 0 :=
      (mem_nonZeroDivisors_iff.mp (pow_mem hr n)).1 _ hn
    exact sub_eq_zero.mp hab'
  · have htop : (⊤ : Submodule R Q) ≤ Ideal.span {r} • ⊤ := by
      intro m _
      obtain ⟨b, rfl⟩ := (LinearMap.range l).mkQ_surjective m
      obtain ⟨a, ha⟩ := hMod b
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
      have heq : (LinearMap.range l).mkQ b =
          r • (LinearMap.range l).mkQ c := by
        apply (Submodule.Quotient.eq (LinearMap.range l)).mpr
        change b - r • c ∈ LinearMap.range l
        refine ⟨a, ?_⟩
        change f a = b - f r * c
        calc
          f a = b - (b - f a) := by abel
          _ = b - c * f r := by rw [hc]
          _ = b - f r * c := by rw [mul_comm]
      rw [heq]
      exact Submodule.smul_mem_smul
        (Ideal.mem_span_singleton_self r) Submodule.mem_top
    obtain ⟨q, hq, hqzero⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
        (Ideal.span {r}) (⊤ : Submodule R Q) Module.Finite.fg_top htop
    have hQ : Subsingleton Q := by
      apply (Module.support_eq_empty_iff (R := R) (M := Q)).mp
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp
      obtain ⟨b, rfl⟩ := (LinearMap.range l).mkQ_surjective m
      obtain ⟨a, n, ha⟩ := hAwayCoker b
      have hrpow : r ^ n ∈
          (R ∙ (LinearMap.range l).mkQ b).annihilator := by
        rw [Submodule.mem_annihilator_span_singleton]
        rw [← (LinearMap.range l).mkQ.map_smul]
        change (LinearMap.range l).mkQ (f (r ^ n) * b) = 0
        rw [map_pow, ← ha]
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range l)).mpr ⟨a, rfl⟩
      have hrpPow : r ^ n ∈ p.asIdeal := hm hrpow
      have hrp : r ∈ p.asIdeal :=
        Ideal.IsPrime.mem_of_pow_mem p.isPrime n hrpPow
      have hqAnn : q ∈ Module.annihilator R Q := by
        rw [Module.mem_annihilator]
        intro x
        exact hqzero x Submodule.mem_top
      have hqp : q ∈ p.asIdeal :=
        Module.annihilator_le_of_mem_support hp hqAnn
      have hqsub : q - 1 ∈ p.asIdeal :=
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrp)) hq
      have h1 : (1 : R) ∈ p.asIdeal := by
        have := p.asIdeal.sub_mem hqp hqsub
        simpa using this
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr h1)
    intro b
    have hbzero : (LinearMap.range l).mkQ b = 0 := Subsingleton.elim _ _
    rw [Submodule.mkQ_apply] at hbzero
    obtain ⟨a, ha⟩ :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range l)).mp hbzero
    exact ⟨a, ha⟩

end RingHom.Finite
