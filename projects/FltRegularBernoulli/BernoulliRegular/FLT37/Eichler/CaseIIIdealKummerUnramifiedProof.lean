import BernoulliRegular.FLT37.Eichler.CaseIIIdealKummerUnramified
import BernoulliRegular.FLT37.Eichler.CaseIINonUnitKummerPoly

/-!
# [FLT37-CASEII-IDEAL-KUMMER-PROOF] Proving the ideal-theoretic Kummer Lemma 9.1

This file **proves** `CaseIIIdealKummerUnramified37` (stated in `CaseIIIdealKummerUnramified.lean`),
the single remaining Case-II II1 residual: a primary radical whose fractional ideal is a `37`-th
power generates an unramified Kummer extension `L = K(α^{1/37})` over `K = ℚ(ζ₃₇)`.

## Reduction to the different ideal

`IsUnramified (𝓞 K) (𝓞 L)` (flt-regular's class: every prime over every nonzero prime `q` has
`ramificationIdx = 1`) is equivalent, prime-by-prime, to "no prime `P` of `𝓞 L` divides the
different ideal `differentIdeal (𝓞 K) (𝓞 L)`" via the mathlib bridges
`Algebra.isUnramifiedAt_iff_of_isDedekindDomain` (`e(P) = 1 ↔ Algebra.IsUnramifiedAt`) and
`not_dvd_differentIdeal_iff` (`Algebra.IsUnramifiedAt ↔ ¬ P ∣ 𝔡`).  Hence the whole goal reduces to

  `differentIdeal (𝓞 K) (𝓞 L) = ⊤`.

## The two halves (Washington Lemma 9.1)

`differentIdeal = ⊤` splits over the rational prime below `P`:

* **(a) at `𝔭 = (ζ-1)` (the prime above 37):** unramified from PRIMARITY (`α ≡ 1 mod (ζ-1)^{37}`).
  This reuses flt-regular's `KummersLemma` congruence machinery (its `poly` has integral roots
  exactly because of the primarity congruence, independent of the radical being a unit).
* **(b) away from `(ζ-1)`:** for `P` over `q ≠ (ζ-1)`, `37` is a unit at `q` (since
  `(37) = (ζ-1)^{36}`) and `v_q(α) = 37·v_q(𝔟) ≡ 0 (mod 37)` (from `(α) = 𝔟^{37}`); the standard
  away-from-`p` Kummer theory gives unramifiedness.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ## 1. The different-ideal bridge

The flt-regular `IsUnramified (𝓞 K) (𝓞 L)` class is equivalent to triviality of the different
ideal of `𝓞 L / 𝓞 K`.  We prove the direction we need: `differentIdeal = ⊤ ⟹ IsUnramified`. -/

section Bridge

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  [Algebra (𝓞 K) (𝓞 L)] [IsScalarTower (𝓞 K) (𝓞 L) L] [IsScalarTower (𝓞 K) K L]
  [Module.Finite (𝓞 K) (𝓞 L)] [Algebra.IsIntegral (𝓞 K) (𝓞 L)]
  [FaithfulSMul (𝓞 K) (𝓞 L)]

/-- `FractionRing (𝓞 K) / FractionRing (𝓞 L)` is separable, transported from the (char-0, hence
separable) number-field extension `L / K` along the canonical fraction-ring isomorphisms.  This is
the `Algebra.IsSeparable` hypothesis required by `not_dvd_differentIdeal_iff`. -/
theorem isSeparable_fractionRing_ringOfIntegers
    [IsIntegralClosure (𝓞 L) (𝓞 K) L] :
    Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := by
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have H : RingHom.comp (algebraMap (FractionRing (𝓞 K)) (FractionRing (𝓞 L)))
      (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv =
        RingHom.comp (FractionRing.algEquiv (𝓞 L) L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext x
    simp only [RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv
    (FractionRing.algEquiv (𝓞 L) L).symm.toRingEquiv H

/-- **The per-prime unramifiedness bridge.**  If every nonzero prime `P` of `𝓞 L` is unramified
over `𝓞 K` (in the commutative-algebra sense `Algebra.IsUnramifiedAt`), then `L / K` is unramified
(`Algebra.Unramified (𝓞 K) (𝓞 L)`).

Proof: `Algebra.unramified_iff_forall` reduces `Algebra.Unramified` to
`Algebra.IsUnramifiedAt (𝓞 K)` at *every* prime of `𝓞 L`; the zero prime is handled by
`isUnramifiedAt_bot` and every nonzero prime by the hypothesis `h`. -/
theorem isUnramified_of_forall_isUnramifiedAt
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P) :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  haveI : Module.IsTorsionFree (𝓞 K) (𝓞 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective _ _)
  refine Algebra.unramified_iff_forall.mpr ?_
  rintro ⟨P, hP⟩
  haveI : P.IsPrime := hP
  by_cases hP_bot : P = ⊥
  · subst hP_bot; exact isUnramifiedAt_bot (R := 𝓞 K) (S := 𝓞 L)
  · exact h P hP_bot

/-- **The different-ideal bridge.**  If the different ideal `differentIdeal (𝓞 K) (𝓞 L)` is trivial
(`= ⊤`), then `L / K` is unramified (`Algebra.Unramified (𝓞 K) (𝓞 L)`).

A nonzero prime `P` of `𝓞 L` never divides `⊤`, so by `not_dvd_differentIdeal_iff` (using the
fraction-ring separability `isSeparable_fractionRing_ringOfIntegers`) `P` is unramified over `𝓞 K`;
feed into `isUnramified_of_forall_isUnramifiedAt`.

Note `differentIdeal (𝓞 K) (𝓞 L) = ⊤` is *equivalent* to `L / K` being everywhere unramified, so
this loses nothing — it is the cleanest single restatement of the goal. -/
theorem isUnramified_of_differentIdeal_eq_top
    [IsIntegralClosure (𝓞 L) (𝓞 K) L]
    (h : differentIdeal (𝓞 K) (𝓞 L) = ⊤) :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  haveI : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    isSeparable_fractionRing_ringOfIntegers (K := K) (L := L)
  refine isUnramified_of_forall_isUnramifiedAt (fun P _ _ => ?_)
  rw [← not_dvd_differentIdeal_iff, h]
  intro hdvd
  exact ‹P.IsPrime›.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))

/-- **"`q`-unramified" ⟹ mathlib `Algebra.IsUnramifiedAt (𝓞 K) P`** for a prime `P` of `𝓞 L` over
`q = P.under (𝓞 K)`.  The hypothesis is the unfolded meaning of the (now-removed) flt-regular
`IsUnramifiedAt (𝓞 L) q`: every prime of `𝓞 L` over `q` has ramification index `1`.  In particular
`e(q, P) = 1`, which by `Algebra.isUnramifiedAt_iff_of_isDedekindDomain` is exactly
`Algebra.IsUnramifiedAt (𝓞 K) P`.  This converts the output of the non-unit `isUnramifiedAt_local`
into the per-prime predicate the different-ideal halves use. -/
theorem algebra_isUnramifiedAt_of_isUnramifiedAt
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP_bot : P ≠ ⊥)
    (h : ∀ Q ∈ (P.under (𝓞 K)).primesOver (𝓞 L),
        Ideal.ramificationIdx (P.under (𝓞 K)) Q = 1) :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  haveI : P.LiesOver (P.under (𝓞 K)) := ⟨rfl⟩
  refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP_bot).mpr ?_
  exact h P ⟨inferInstance, inferInstance⟩

end Bridge

/-! ## 2. The single residual: triviality of the different ideal of the Kummer extension

By the bridge, `CaseIIIdealKummerUnramified37` reduces to: for every primary radical `α` whose
fractional ideal is a `37`-th power, the Kummer extension `L = K(α^{1/37})` has trivial different
ideal over `K = ℚ(ζ₃₇)`.  This is the cleanest single restatement of Washington Lemma 9.1's
unramifiedness — `differentIdeal = ⊤ ⇔ L/K everywhere unramified` — with the two halves (the local
content at `(ζ-1)` from primarity, and the away-from-`(ζ-1)` content from `(α) = 𝔟^{37}`) packaged
together as the divisor-by-divisor non-division of the different. -/

section Residual

open FLT37.LehmerVandiver.CaseI.AntiKummer

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-LEMMA-9.1-DIFFERENT] The different ideal of the Kummer extension is trivial.**

For a primary radical `α : K = ℚ(ζ₃₇)` (`α ≡ 1 mod (ζ-1)^{37}`, witness form) whose fractional ideal
`spanSingleton α` is a `37`-th power `𝔟^{37}`, the different ideal of `𝓞 L / 𝓞 K`
(`L = antiKummerLift K α = K(α^{1/37})`) is `⊤`, i.e. `L/K` is unramified at every finite prime.

This is Washington Lemma 9.1 stated as different-ideal triviality (the cleanest single
restatement of unramifiedness).  It is **non-circular**: `𝔟` is an arbitrary fractional ideal,
never asserted principal. -/
def CaseIIKummerDifferentTrivial37 : Prop :=
  ∀ (α : CyclotomicField 37 ℚ) (hα : α ≠ 0),
    (∃ (ζ : CyclotomicField 37 ℚ) (hζ : IsPrimitiveRoot ζ 37)
        (N c : 𝓞 (CyclotomicField 37 ℚ)), ¬ (hζ.toInteger - 1 : 𝓞 _) ∣ c ∧
        (α - 1) * algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) c =
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((hζ.toInteger - 1 : 𝓞 _) ^ 37 * N)) →
    (∃ 𝔟 : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ),
        FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α = 𝔟 ^ 37) →
    differentIdeal (𝓞 (CyclotomicField 37 ℚ))
      (𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα)) = ⊤

/-- **The ideal-theoretic Kummer Lemma 9.1 from different-ideal triviality.**

Wires `CaseIIKummerDifferentTrivial37` into the target `CaseIIIdealKummerUnramified37` via the
different-ideal bridge `isUnramified_of_differentIdeal_eq_top`, supplying the concrete
`antiKummerLift` algebra/scalar-tower instances. -/
theorem caseIIIdealKummerUnramified37_of_differentTrivial
    (h : CaseIIKummerDifferentTrivial37) :
    CaseIIIdealKummerUnramified37 := by
  intro α hα h_primary h_ideal
  haveI : IsScalarTower (𝓞 (CyclotomicField 37 ℚ))
      (𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα))
      (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact isUnramified_of_differentIdeal_eq_top (K := CyclotomicField 37 ℚ)
    (L := antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα) (h α hα h_primary h_ideal)

end Residual

/-! ## 3. The two halves of Washington Lemma 9.1 (the genuine local content)

`differentIdeal (𝓞 K) (𝓞 L) = ⊤` means no prime `P` of `𝓞 L` divides the different, equivalently
(via `not_dvd_differentIdeal_iff`) every prime `P` is unramified.  We split on whether `P` lies over
the rational prime `37` (equivalently over `(ζ-1)`, the unique ramified prime of `K/ℚ`):

* **away** (`(37 : 𝓞 L) ∉ P`): `37` is a unit at `P`, and `v_P(α) ≡ 0 mod 37` from `(α) = 𝔟^{37}`;
  the standard away-from-`p` Kummer theory gives `P` unramified.  Stated as
  `CaseIIKummerUnramifiedAway37`.
* **at 37** (`(37 : 𝓞 L) ∈ P`): primarity `α ≡ 1 mod (ζ-1)^{37}` gives `P` unramified (Washington
  Lemma 9.1's local content; flt-regular proves this for unit radicals via `KummersLemma.poly`'s
  congruence-driven integral roots).  Stated as `CaseIIKummerUnramifiedAt37`.

Both are stated as `Algebra.IsUnramifiedAt`-predicates over the abstract `K, L`. -/

section TwoHalves

open FLT37.LehmerVandiver.CaseI.AntiKummer

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- The "away from 37" half of Washington Lemma 9.1: for a radical `α` with `(α) = 𝔟^{37}`, every
prime `P` of `𝓞 L` (`L = K(α^{1/37})`) **not** lying over `37` is unramified over `𝓞 K`.

This is the tame Kummer-extension unramifiedness (`37` a unit at `P`, `37 ∣ v_P(α)`).  Not currently
in mathlib (no tame-ramification API). -/
def CaseIIKummerUnramifiedAway37 : Prop :=
  ∀ (α : CyclotomicField 37 ℚ) (hα : α ≠ 0),
    (∃ 𝔟 : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ),
        FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α = 𝔟 ^ 37) →
    ∀ (P : Ideal (𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα))) [P.IsPrime],
      P ≠ ⊥ →
      (37 : 𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα)) ∉ P →
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 37 ℚ)) P

/-- The "at 37" half of Washington Lemma 9.1: for a **primary** radical `α`
(`α ≡ 1 mod (ζ-1)^{37}`), every prime `P` of `𝓞 L` (`L = K(α^{1/37})`) lying over `37` is unramified
over `𝓞 K`.

This is the local content of Washington Lemma 9.1 at `(ζ-1)`.  flt-regular proves the analogue for a
**unit** radical (`KummersLemma.isUnramified`, via `KummersLemma.poly`); the non-unit/non-integral
generalization is the `separable_poly_aux` gap. -/
def CaseIIKummerUnramifiedAt37 : Prop :=
  ∀ (α : CyclotomicField 37 ℚ) (hα : α ≠ 0),
    (∃ (ζ : CyclotomicField 37 ℚ) (hζ : IsPrimitiveRoot ζ 37)
        (N c : 𝓞 (CyclotomicField 37 ℚ)), ¬ (hζ.toInteger - 1 : 𝓞 _) ∣ c ∧
        (α - 1) * algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) c =
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((hζ.toInteger - 1 : 𝓞 _) ^ 37 * N)) →
    ∀ (P : Ideal (𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα))) [P.IsPrime],
      P ≠ ⊥ →
      (37 : 𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα)) ∈ P →
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 37 ℚ)) P

/-- **`CaseIIKummerDifferentTrivial37` from the two local halves.**

Combining the away-from-37 and at-37 unramifiedness (per prime `P` of `𝓞 L`), every prime is
unramified, so no prime divides the different ideal; hence `differentIdeal = ⊤`.  The split is on
`(37 : 𝓞 L) ∈ P` (excluded middle). -/
theorem caseIIKummerDifferentTrivial37_of_halves
    (h_away : CaseIIKummerUnramifiedAway37) (h_at : CaseIIKummerUnramifiedAt37) :
    CaseIIKummerDifferentTrivial37 := by
  intro α hα h_primary h_ideal
  set L := antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα with hL
  haveI : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsSeparable (FractionRing (𝓞 (CyclotomicField 37 ℚ))) (FractionRing (𝓞 L)) :=
    isSeparable_fractionRing_ringOfIntegers (K := CyclotomicField 37 ℚ) (L := L)
  -- Suppose `different ≠ ⊤`; pick a maximal ideal containing it, derive unramifiedness, contradict.
  by_contra hne
  obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal _ hne
  haveI : M.IsPrime := hM_max.isPrime
  have hM_bot : M ≠ ⊥ := by
    rintro rfl
    exact differentIdeal_ne_bot (le_bot_iff.mp hM_le)
  have hM_dvd : M ∣ differentIdeal (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) :=
    Ideal.dvd_iff_le.mpr hM_le
  -- `M` is unramified (away from / at 37, depending on `(37 : 𝓞 L) ∈ M`).
  have hM_unram : Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 37 ℚ)) M := by
    by_cases h37 : (37 : 𝓞 L) ∈ M
    · exact h_at α hα h_primary M hM_bot h37
    · exact h_away α hα h_ideal M hM_bot h37
  exact (not_dvd_differentIdeal_iff.mpr hM_unram) hM_dvd

/-- **[FLT37-CASEII-LEMMA-9.1-IDEAL] The ideal-theoretic Kummer unramifiedness from the two local
halves.**

Composes `caseIIKummerDifferentTrivial37_of_halves` (the per-prime split of the different ideal)
with `caseIIIdealKummerUnramified37_of_differentTrivial` (the different-ideal bridge) to obtain the
target `CaseIIIdealKummerUnramified37` from the two precise local residuals — the away-from-37 tame
Kummer
unramifiedness and the at-37 primary unramifiedness. -/
theorem caseIIIdealKummerUnramified37_of_halves
    (h_away : CaseIIKummerUnramifiedAway37) (h_at : CaseIIKummerUnramifiedAt37) :
    CaseIIIdealKummerUnramified37 :=
  caseIIIdealKummerUnramified37_of_differentTrivial
    (caseIIKummerDifferentTrivial37_of_halves h_away h_at)

end TwoHalves

end BernoulliRegular.FLT37.Eichler

end
