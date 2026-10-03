module

import FltRegular.NumberTheory.Hilbert94
public import BernoulliRegular.FLT37.KummerUnits
public import FltRegular.NumberTheory.KummersLemma.KummersLemma

/-!
# Real Kummer's lemma (the concrete Stage 2 target)

Per the project plan (`docs/flt37-lehmer-vandiver-plan.md`) and the
handover, Stage 2 reduces to **adapting flt-regular's
`eq_pow_prime_of_unit_of_congruent`** by:

1. Using `KummersLemma.isUnramified` (regularity-free, in flt-regular).
2. Applying `Hilbert 94` (`dvd_card_classGroup_of_isUnramified_isCyclic`)
   to `K⁺` instead of `K`.
3. Descending the unramified Kummer extension `K(α^{1/p})/K` to
   `K⁺(...)/K⁺` under primarity, using Hilbert 90 from
   `BernoulliRegular/FLT37/Hilbert90.lean`.

The end result is a "real Kummer's lemma": for `u ∈ (𝓞 K⁺)ˣ` real with
`u ≡ a (mod p)`, under `¬ p ∣ h⁺(K)`, `u` is a `p`-th power in
`(𝓞 K⁺)ˣ`.

This file packages **`RealKummerLemma`** as the concrete predicate to
fill, and shows how it reduces from `Stage2KummerRatioK` (which is
case-I-specific) to the cleaner real-form statement.

## References

* flt-regular's `eq_pow_prime_of_unit_of_congruent`
  (`KummersLemma.lean:49`).
* `BernoulliRegular/FLT37/Hilbert90.lean`.
* `docs/flt37-lehmer-vandiver-plan.md`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **Real Kummer's lemma** (Stage 2's concrete target). For a real
unit `u : (𝓞 K⁺)ˣ` congruent to a rational integer mod `p`, under
`¬ p ∣ h⁺(K)`, `u` is a `p`-th power in `(𝓞 K⁺)ˣ`.

This is the K⁺-side analogue of flt-regular's
`eq_pow_prime_of_unit_of_congruent`, parametric on `¬ p ∣ h⁺` instead
of regularity.

Filling this predicate is the substantive Stage 2 work, but the
recipe is concrete: use `KummersLemma.isUnramified` + descend to K⁺
via Hilbert 90 + apply Hilbert 94 to K⁺.

The advantage of this formulation over `Stage2KummerRatioK`: it's
case-I-independent, fits standard Kummer-lemma signatures, and is the
*natural* form derivable from the existing flt-regular toolchain. -/
def RealKummerLemma : Prop :=
  ¬ (p : ℕ) ∣ hPlus K →
    ∀ (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
      (∃ n : ℤ,
        ((p : ℕ) : 𝓞 (NumberField.maximalRealSubfield K)) ∣
          ((u : 𝓞 (NumberField.maximalRealSubfield K)) - (n : ℤ))) →
      ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ, u = v ^ p

/-- **Adjustable real form** when `u` is already known to be a p-th
power in K but possibly not in K⁺. Standard observation: if `u ∈ K⁺^×`
and `v^p = u` for `v ∈ K^×`, then `σ(v)/v` is a p-th root of unity, so
`v · ζ^k` is real for an appropriate `k` (since p is odd, the ζ-power
factors out cleanly).

This is the K-to-K⁺ extraction step that's used both in the regular
case and after the descent has been done. -/
def RealKummerExtract : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ)
    (v : (𝓞 K)ˣ),
    ((v : 𝓞 K) ^ p =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) u) →
    ∃ w : (𝓞 (NumberField.maximalRealSubfield K))ˣ, u = w ^ p

/-- **Lift to K, then extract real**: shows that `RealKummerLemma`
follows from
1. `eq_pow_prime_of_unit_of_congruent` applied to the lifted unit (under
   regularity OR another VC-style hypothesis), AND
2. `RealKummerExtract` (the K-to-K⁺ extraction).

The first ingredient is the Stage 2 substantive content. The second is
elementary algebra (ζ-power adjustment). -/
def RealKummerViaLiftExtract : Prop :=
  ¬ (p : ℕ) ∣ hPlus K →
    ∀ (u : (𝓞 (NumberField.maximalRealSubfield K))ˣ),
    (∃ n : ℤ,
      ((p : ℕ) : 𝓞 (NumberField.maximalRealSubfield K)) ∣
        ((u : 𝓞 (NumberField.maximalRealSubfield K)) - (n : ℤ))) →
    (∃ v : (𝓞 K)ˣ, (v : 𝓞 K) ^ p =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) u)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- **`RealKummerLemma` from lift-and-extract.** Composes the lift
step (which produces a `p`-th-root unit in `(𝓞 K)ˣ`) with the
real-extract step. -/
theorem realKummerLemma_of_lift_extract (h_lift : RealKummerViaLiftExtract p K)
    (h_extract : RealKummerExtract p K) :
    RealKummerLemma p K := by
  intro h_not_dvd u hcong
  obtain ⟨v, hv⟩ := h_lift h_not_dvd u hcong
  exact h_extract u v hv

omit [NumberField.IsCMField K] in
/-- **`RealKummerExtract` is unconditional** (when `2 < p`). The
elementary K-to-K⁺ extraction step using
`exists_zeta_pow_mul_real_eq_unit`: any unit `v ∈ (𝓞 K)ˣ` decomposes
as `ζ^m · algebraMap w` for some `w ∈ (𝓞 K⁺)ˣ`. If `v^p` is real,
then `w^p` is the real `p`-th root.

This is the elementary half of Stage 2 — no CFT, just unit
decomposition + algebra. -/
theorem realKummerExtract_unconditional (hp_two : 2 < p) : RealKummerExtract p K := by
  intro u v hv
  obtain ⟨m, w, hw⟩ :=
    FLT37.exists_zeta_pow_mul_real_eq_unit (p := p) (K := K) hp_two v
  refine ⟨w, ?_⟩
  apply Units.ext
  apply (FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
  -- The key computation: `v = ζ^m · algebraMap w` (from `hw`), so since `p` is odd
  -- `v^p = (ζ^m · algebraMap w)^p = (ζ^m)^p · (algebraMap w)^p = (algebraMap w)^p`.
  have hζ_p_one :
      (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit :
        (𝓞 K)ˣ) ^ p = 1 :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).pow_eq_one
  have hζmp_one :
      (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit :
        (𝓞 K)ˣ) ^ (m * p) = 1 := by
    rw [mul_comm, pow_mul, hζ_p_one, one_pow]
  have hv_pow_unit : v ^ p = (Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 K)).toMonoidHom w) ^ p := by
    rw [hw, mul_pow, ← pow_mul, hζmp_one, one_mul]
  have hv_pow_val : (v : 𝓞 K) ^ p = ((Units.map
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom w
      : (𝓞 K)ˣ) : 𝓞 K) ^ p := by
    rw [← Units.val_pow_eq_pow_val, hv_pow_unit, Units.val_pow_eq_pow_val]
  rw [← hv, hv_pow_val]
  -- `algebraMap (w^p) = (algebraMap w)^p` holds definitionally after `push_cast`.
  push_cast
  rfl

/-- **`RealKummerLemma` reduces to `RealKummerViaLiftExtract`** (when
`2 < p`). With `realKummerExtract_unconditional` shipped, the only
remaining substantive Stage 2 work is the "lift to K and find p-th
power" step.

This makes the Stage 2 contract MORE CONCRETE: instead of a single
Prop predicate, it's now a clean reduction to a simpler statement
about K-side p-th powers. -/
theorem realKummerLemma_of_lift_under_hp_two
    (hp_two : 2 < p) (h_lift : RealKummerViaLiftExtract p K) :
    RealKummerLemma p K :=
  realKummerLemma_of_lift_extract p K h_lift
    (realKummerExtract_unconditional p K hp_two)

/-- **`RealKummerViaLiftExtract` from regularity.** Under regularity
(`p.Coprime |Cl(K)|`), the lift step holds: every real unit congruent
to a rational mod `p` lifts to a `p`-th power in `(𝓞 K)ˣ` via
flt-regular's `eq_pow_prime_of_unit_of_congruent`.

This shows the lift step is fillable for regular primes. For irregular
primes (FLT37), the lift requires the descent to K⁺ via Hilbert 90/94. -/
theorem realKummerViaLiftExtract_of_regular
    (hp_two : 2 < p)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    RealKummerViaLiftExtract p K := by
  intro _h_not_dvd u hcong
  set u_K : (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 K)).toMonoidHom u with hu_K
  -- Transfer the congruence along `algebraMap`: `p ∣ (u - n)` in `𝓞 K⁺` gives
  -- `p ∣ algebraMap (u - n) = u_K - n` in `𝓞 K`.
  have hcong_K : ∃ n : ℤ, ((p : ℕ) : 𝓞 K) ∣ ((u_K : 𝓞 K) - (n : ℤ)) := by
    obtain ⟨n, k, hk⟩ := hcong
    refine ⟨n, ?_⟩
    have h_map : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((u : 𝓞 (NumberField.maximalRealSubfield K)) -
          ((n : ℤ) : 𝓞 (NumberField.maximalRealSubfield K))) =
      (u_K : 𝓞 K) - ((n : ℤ) : 𝓞 K) := by
      rw [map_sub]
      simp [hu_K]
    rw [← h_map, hk, map_mul]
    exact dvd_mul_of_dvd_left (by simp) _
  obtain ⟨v_K, hv_K⟩ := eq_pow_prime_of_unit_of_congruent
    (K := K) (Nat.ne_of_gt hp_two) hreg u_K hcong_K
  -- `hv_K : u_K = v_K^p` at the unit level; `(u_K : 𝓞 K) = algebraMap u` definitionally.
  refine ⟨v_K, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← hv_K]
  rfl

/-- **`RealKummerLemma` from regularity (combined).** Under regularity
(`p.Coprime |Cl(K)|`) and `2 < p`, the full real Kummer's lemma
holds. This combines:
- `realKummerViaLiftExtract_of_regular` (the lift step).
- `realKummerExtract_unconditional` (the extract step).

Demonstrates that Stage 2 is COMPLETELY proven under regularity (mirroring
flt-regular's caseI/caseII for regular primes). For irregular primes
(FLT37), the substantive remaining work is just the lift step under
`¬p ∣ h⁺` instead of regularity. -/
theorem realKummerLemma_of_regular
    (hp_two : 2 < p)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    RealKummerLemma p K :=
  realKummerLemma_of_lift_under_hp_two p K hp_two
    (realKummerViaLiftExtract_of_regular p K hp_two hreg)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Hilbert 94 contrapositive for K⁺.** Under `¬ p ∣ h⁺(K)`, no
unramified cyclic prime-degree (p) extension `L⁺/K⁺` exists.

This is the direct contrapositive of `dvd_card_classGroup_of_isUnramified_isCyclic`
applied to K⁺. It's the K⁺-side analogue of the regularity contradiction
in flt-regular's `eq_pow_prime_of_unit_of_congruent`.

The descent step in Stage 2 (still TODO) constructs such an extension
from `u^{1/p}` for real u; this theorem shows that if such an
extension existed, we'd contradict `¬p ∣ h⁺`. -/
theorem no_h94_extension_of_Kplus_under_VC (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (Lplus : Type) [Field Lplus]
    [Algebra (NumberField.maximalRealSubfield K) Lplus] [NumberField Lplus]
    [FiniteDimensional (NumberField.maximalRealSubfield K) Lplus]
    [IsGalois (NumberField.maximalRealSubfield K) Lplus]
    [Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 Lplus)]
    [IsCyclic (Lplus ≃ₐ[NumberField.maximalRealSubfield K] Lplus)]
    (hKL : Module.finrank (NumberField.maximalRealSubfield K) Lplus = p) :
    False := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_finrank : Nat.Prime
      (Module.finrank (NumberField.maximalRealSubfield K) Lplus) :=
    hKL.symm ▸ hp_prime
  have hp_ne_two : Module.finrank (NumberField.maximalRealSubfield K) Lplus ≠ 2 :=
    hKL.symm ▸ hp_odd
  have hdvd : Module.finrank (NumberField.maximalRealSubfield K) Lplus ∣
      Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :=
    dvd_card_classGroup_of_unramified_isCyclic hp_finrank hp_ne_two
  rw [hKL] at hdvd
  -- `hdvd : p ∣ |Cl(𝓞 K⁺)|`, and `|Cl(𝓞 K⁺)| = hPlus K`, contradicting `h_not_dvd`.
  exact h_not_dvd hdvd

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
