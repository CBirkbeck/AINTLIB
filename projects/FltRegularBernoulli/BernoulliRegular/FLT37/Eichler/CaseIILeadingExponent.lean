import BernoulliRegular.FLT37.Eichler.CaseIIOmega32Membership
import BernoulliRegular.FLT37.Eichler.CaseIIResidueProvenance

/-!
# Washington Lemma 9.9 regular-index half for `p = 37`: the leading-`λ`-exponent collapse
discharging `DescentUnitOmega32Membership37`

This file discharges the named ω³²-membership input `DescentUnitOmega32Membership37`
(`CaseIIOmega32Membership.lean`) — the **regular-index half of Washington Lemma 9.9** — via the
leading-`λ`-exponent mechanism of Washington's Exercises 8.10/8.11 (GTM 83, p. 166), the
**second-order-condition-free, `p`-adic-`L`-free** route.

It imports only; it does **not** modify any existing file.

## The mechanism (Washington Lemma 9.9, regular indices, via Exercises 8.10/8.11)

A real unit `u : (𝓞 K⁺)ˣ` whose `K`-image `Units.map u` is congruent to a **rational integer**
modulo `37` has, in the mod-`37` free part `(E_K free)/37`, a class `realUnitToFreePartModP u` that
decomposes (Corollary 8.15, `37 ∤ h⁺`, **proven** `caseIIResidueProvenance_exists_decomp`) over the
seventeen even Pollaczek eigenvectors `[E_{2(j+1)}]`:

  `realUnitToFreePartModP u = ∑_j c_j • [E_{2(j+1)}]`.

The eigenvector `[E_{2(j+1)}]` lies in the `ω^{2(j+1)}`-eigenspace of the Galois `Δ`-action
(**proven** `caseIIGaloisEigen_E32_in_omega32_eigenspace` at `j = 15`, and
`pollaczekUnit_image_in_omegaChar_eigenspace_general` for the rest), so the eigenspaces for distinct
`j` are independent.  Hence `realUnitToFreePartModP u` lies in the single irregular `ω³²`-eigenspace
(`j = 15`, `i = 32`) **iff** the regular eigencomponents `c_j` (`j ≠ 15`, i.e. `37 ∤ B_{2(j+1)}`)
all vanish.

The leading-`λ`-exponent argument forces exactly that.  Writing `u = γ³⁷ ∏_a E_a^{d_a}` in the
Corollary-8.15 basis, Exercise 8.11 gives the regular `E_a` a `λ`-adic leading expansion
`E_a ≡ a_a + b_a λ^{c_a}` with `c_a = (index)/2` and `37 ∤ a_a b_a`, and Exercise 8.10 gives a
product the leading `λ`-exponent `min_a(c_a + 18·v_37(d_a))` (with `(p-1)/2 = 18` the
`K⁺`-ramification).
Since `(37) = (𝔭⁺)^{18}`, "`Units.map u ≡` rational integer mod `37`" forces the leading
non-constant `λ`-exponent of `u` to be `≥ 18`; with `c_a = (index)/2 ≤ 17 < 18` for every regular
index, this forces `v_37(d_a) ≥ 1`, i.e. `37 ∣ d_a`.  So the regular eigencomponents vanish, and
`realUnitToFreePartModP u` is an `E₃₂`-monomial, hence lies in the `ω³²`-eigenspace.

## What this file proves (real, axiom-clean Lean)

* **The local reduction** (`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`, fully
  **proven**): a real unit `u` with `Units.map u ≡ c (mod 37)` has its degree-`36` completed-log
  argument of `λ`-valuation `≥ 36` (`CompletedLogArgHighValuation37 u`).  This is Washington Lemma
  9.9's opening analytic step — "`≡` rational mod `37`" forces the leading non-constant `λ`-exponent
  to `≥ (p-1)/2`, via the ramification `(37) = λ^{36}` and Fermat `c^{36} ≡ 1`.

* **The eigenspace endgame** (`caseIILeadingExponent_omega32_of_regular_components_zero`, fully
  **proven**): if `realUnitToFreePartModP u = ∑_j c_j • [E_{2(j+1)}]` and the **regular**
  coefficients `c_j` (`j ≠ 15`) all vanish, then `realUnitToFreePartModP u ∈ ω³²`-eigenspace.  This
  is the faithful "regular components drop out ⟹ irregular eigenspace" half of Lemma 9.9, derived
  from the proven `Δ`-eigenvalue eigenspace placement of `[E₃₂]`.

* **The named leading-`λ`-coefficient collapse** (`LeadingExponentEigenCollapse37`, a
  `def … : Prop`, **not** an axiom): for a real unit `u` of high `λ`-adic log-valuation
  (`CompletedLogArgHighValuation37 u`, the *output* of the proven local reduction), the regular
  eigencomponents of `realUnitToFreePartModP u` vanish.  This is the genuine Galois-graded
  leading-coefficient computation of Exercise 8.11 — the **single** undischarged piece — isolated
  from the (proven) analytic first step and the (proven) eigenspace endgame.  It is **sound**: it
  constrains the eigencomponents of a unit with this *specific* `λ`-adic property, never an
  `E₃₂`-monomial property of an arbitrary real unit, and it is **not** the ω³²-membership goal.

* `caseIILeadingExponent_regular_components_zero` — regular eigencomponents vanish for a
  rational-mod-`37` real unit, **proven** from the leaf + the proven local reduction.

* `descentUnit_omega32Membership_of_leadingExponent` — `DescentUnitOmega32Membership37` from the
  named leaf, via the proven local reduction and the proven eigenspace endgame.

## The single remaining gap, precisely

`LeadingExponentEigenCollapse37` is the only undischarged content.  Mathematically it is the
Galois-equivariant leading-`λ`-coefficient computation: the `ω^{2(j+1)}`-eigencomponent of the local
logarithm of a regular `E_{2(j+1)}` (`37 ∤ B_{2(j+1)}`) is a nonzero multiple of `B_{2(j+1)} mod 37`
sitting at `λ`-level `2(j+1) ≤ 34 < 36`, so the `λ`-valuation `≥ 36` of the descent unit's log
forces the regular eigencomponents to vanish.  Formalising it needs a Galois-equivariant bridge
between the global mod-`37` free-part eigencomponents (`caseIIResidueProvenance_decomp`) and the
local graded pieces `completedPrincipalUnitGradedQuotient` of `Reflection.Local.GradedAction` (whose
`ω^n`-eigenvalue `completedPrincipalUnitGradedDeltaActionZMod_apply_eq_smul` is already proven) — a
multi-file development not yet in the repo.  The companion `concreteKummerLogMatrix = diag(B)·V`
machinery (`Washington816`) does **not** suffice on its own: it gives the *Dwork-basis* matrix
kernel, which (via the Vandermonde change of basis to the eigenbasis) only forces the regular
eigencomponents to be *equal*, not zero.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9 (pp. 180–181),
  Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 157).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 0. The local reduction: "rational-mod-`37`" ⟹ leading `λ`-exponent `≥ 18`

This is the genuine first analytic step of Washington Lemma 9.9 (the "`≡ rational integer mod p`
means leading `λ`-exponent `≥ (p-1)/2`" reduction).  In the `λ`-adic valuation ring at the prime
above `37` the ramification is `(37) = (λ)^{36}` (`span_natCast_prime_eq_lambdaIdeal_pow_pred`,
`e = p - 1 = 36`).  A real unit `u` with `Units.map u ≡ c (mod 37)` therefore has local image
`X ≡ c (mod λ^{36})`, and — since `c` must be coprime to `37` (else `X` would lie in the maximal
ideal, contradicting `X` being a unit) — Fermat gives `c^{36} ≡ 1 (mod 37)`, so

  `X^{36} - 1 = (X^{36} - c^{36}) + (c^{36} - 1) ∈ (λ)^{36}`.

Thus `EPlus_completedLogDomainPowPred u = X^{36}` is a principal unit of level `36`: its
completed-log argument lies in `lambdaIdeal^{36}`.  This is the leading-`λ`-exponent `≥ 18`
statement at the
`K`-level (where `e = 36`), the genuine input to Exercises 8.10/8.11. -/

/-- **High `λ`-valuation of the degree-`36` completed-log argument** (a light named wrapper over the
`λ`-adic membership, used to thread the heavy local-completion type past the elaborator without
`whnf` loops): the degree-`(37-1)` completed-log argument
`(EPlus_valuedLocalImage u)^{36} - 1 = completedLogArg(EPlus_completedLogDomainPowPred u)` lies in
`lambdaIdeal^{36}`, i.e. `u^{36}` is a principal unit of `λ`-level `≥ 36`. -/
def CompletedLogArgHighValuation37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) : Prop :=
  completedLogArg (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u) ∈
    (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36

/-- **The local reduction** (proven, axiom-clean): a real unit `u : (𝓞 K⁺)ˣ` whose `K`-image
`Units.map u` is congruent to a rational integer `c` modulo `37` has its degree-`(37-1)`
completed-log argument `(EPlus_valuedLocalImage u)^{36} - 1` of high `λ`-valuation
(`CompletedLogArgHighValuation37 u`, i.e. it lies in `lambdaIdeal^{36}`).

This is Washington Lemma 9.9's opening step — "`≡` rational mod `37`" forces the leading
non-constant `λ`-exponent (at the `K`-level prime, `(37) = λ^{36}`) to be `≥ 36`.  Proof: from
`37 ∣ Units.map u - c` in `𝓞 K`, mapping to the `λ`-valued ring gives
`X - c ∈ (37) = lambdaIdeal^{36}` where
`X = EPlus_valuedLocalImage u` (a unit, hence `X ∉ lambdaIdeal`, forcing `37 ∤ c`); then
`X^{36} - c^{36} ∈ lambdaIdeal^{36}` and Fermat's `c^{36} ≡ 1 (mod 37)` give `c^{36} - 1 ∈ (37) =
lambdaIdeal^{36}`, so `X^{36} - 1 ∈ lambdaIdeal^{36}`. -/
theorem caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    CompletedLogArgHighValuation37 u := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  unfold CompletedLogArgHighValuation37
  set I : Ideal (ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) :=
    (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36 with hI
  let f := algebraMap (𝓞 (CyclotomicField 37 ℚ)) (ValuedIntegerRing 37 (CyclotomicField 37 ℚ))
  let X : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) :=
    (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
      ValuedIntegerRing 37 (CyclotomicField 37 ℚ))
  -- `(37) = lambdaIdeal^{36}` in the valued ring.
  have hpow_eq : Ideal.span ({(37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))} :
      Set (ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) = I := by
    have h := span_natCast_prime_eq_lambdaIdeal_pow_pred (p := 37) (K := CyclotomicField 37 ℚ)
    rw [hI, show (37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ((37 : ℕ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) from by norm_cast]
    convert h using 2
  -- The membership-in-`(37)` statement, used repeatedly.
  have h37_mem_iff : ∀ z : ValuedIntegerRing 37 (CyclotomicField 37 ℚ),
      z ∈ I ↔ (37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ∣ z := by
    intro z
    rw [← hpow_eq, Ideal.mem_span_singleton]
  -- Step 1: `X - c ∈ I` from the global divisibility.
  have hXc : X - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ∈ I := by
    rw [h37_mem_iff]
    obtain ⟨w, hw⟩ := hc
    refine ⟨f w, ?_⟩
    have hKunit : (Units.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))) =
        algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))
          (u : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))) := by
      rw [Units.coe_map]; rfl
    have hXval : X = f ((Units.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ)))) := by
      rw [hKunit]; rfl
    have hcong := congrArg f hw
    rw [map_sub, map_mul] at hcong
    rw [hXval, show (37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) =
        f (37 : 𝓞 (CyclotomicField 37 ℚ)) from by rw [map_ofNat],
      show ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) =
        f (c : 𝓞 (CyclotomicField 37 ℚ)) from by rw [map_intCast]]
    exact hcong
  -- Step 2: `37 ∤ c` (else `X ∈ lambdaIdeal`, but `X` is a unit).
  have hX_notmem : X ∉ lambdaIdeal 37 (CyclotomicField 37 ℚ) := by
    intro hmem
    refine lambdaIdeal_ne_top (p := 37) (K := CyclotomicField 37 ℚ)
      ((Ideal.eq_top_iff_one _).mpr ?_)
    obtain ⟨v, hv⟩ := (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u).isUnit
    have hmul : (↑v⁻¹ : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) * X ∈
        lambdaIdeal 37 (CyclotomicField 37 ℚ) :=
      (lambdaIdeal 37 (CyclotomicField 37 ℚ)).mul_mem_left _ hmem
    rwa [show X = (v : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) from hv.symm,
      ← Units.val_mul, inv_mul_cancel, Units.val_one] at hmul
  have hc_not_dvd : ¬ (37 : ℤ) ∣ c := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    refine hX_notmem ?_
    have hXeq : X = (X - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) +
        (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) := by ring
    rw [hXeq]
    refine (lambdaIdeal 37 (CyclotomicField 37 ℚ)).add_mem
      (Ideal.pow_le_self (n := 36) (by norm_num) hXc) ?_
    have hcc : (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) *
          (k : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) := by
      rw [show (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) = ((c : ℤ) : _) from rfl, hk]
      push_cast; ring
    rw [hcc]
    exact (lambdaIdeal 37 (CyclotomicField 37 ℚ)).mul_mem_right _
      (natCast_prime_mem_lambdaIdeal (p := 37) (K := CyclotomicField 37 ℚ))
  -- Step 3: Fermat `c^{36} ≡ 1 (mod 37)`, hence `(c : R)^{36} - 1 ∈ I`.
  have hFermat : (37 : ℤ) ∣ (c ^ 36 - 1) := by
    have hcz : ((c : ZMod 37)) ^ 36 = 1 :=
      ZMod.pow_card_sub_one_eq_one (by
        intro hzero
        exact hc_not_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd c 37).mp hzero))
    have hzz : ((c ^ 36 - 1 : ℤ) : ZMod 37) = 0 := by push_cast; rw [hcz]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 37).mp hzz
  have hc36_mem : (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1 ∈ I := by
    rw [h37_mem_iff]
    obtain ⟨k, hk⟩ := hFermat
    refine ⟨(k : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)), ?_⟩
    have hcast : ((c ^ 36 - 1 : ℤ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (37 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) *
          (k : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) := by
      rw [hk]; push_cast; ring
    push_cast at hcast
    linear_combination hcast
  -- Step 4: `X^{36} - c^{36} ∈ I` via the quotient ring hom.
  have hXc36 : X ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow]
    have hXc' : (Ideal.Quotient.mk I) X =
        (Ideal.Quotient.mk I) (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hXc
    rw [hXc', sub_self]
  -- Final assembly: `completedLogArg (…) = X^{36} - 1 ∈ I`.
  have hargeq : completedLogArg (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u) =
      X ^ 36 - 1 := by
    rw [completedLogArg, EPlus_completedLogDomainPowPred_coe]
  rw [hargeq, show X ^ 36 - 1 =
    (X ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36) +
      ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1) from by ring]
  exact I.add_mem hXc36 hc36_mem

/-! ## 1. The eigenspace endgame: regular components drop out ⟹ `ω³²`-membership

This is the structural half of Washington Lemma 9.9 that is **independent** of the
leading-`λ`-exponent input: a free-part class decomposing over the seventeen eigenvectors with
vanishing regular coefficients lies in the single irregular `ω³²`-eigenspace. -/

/-- **The eigenspace endgame** (proven, axiom-clean, **sound**).

If a free-part class `x : (E_K free)/37` decomposes over the seventeen even Pollaczek eigenvectors
as `x = ∑_j c_j • [E_{2(j+1)}]` (`h_decomp`) and the **regular** coefficients vanish — `c_j = 0` for
every `j ≠ 15` (`h_reg`) — then `x` lies in the single irregular `ω³²`-eigenspace.

Proof: the decomposition collapses to the single `j = 15` term `x = c₁₅ • [E₃₂]`, and `[E₃₂]` is an
`ω³²`-eigenvector (the proven `caseIIConjugateResidue_eigenvector_15_mem_omega32`), so `x` lies in
the eigenspace by `Submodule.smul_mem`.  This isolates the structural collapse from the
leading-`λ`-exponent
input that supplies `h_reg`. -/
theorem caseIILeadingExponent_omega32_of_regular_components_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)}
    (c : Fin 18 → ZMod 37)
    (h_decomp : x = ∑ j : Fin 18, c j • caseIIConjugateResidue_eigenvector j)
    (h_reg : ∀ j : Fin 18, j ≠ 15 → c j = 0) :
    x ∈ cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
      (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32) := by
  -- The decomposition collapses to the single `j = 15` term.
  have hcollapse : x = c 15 • caseIIConjugateResidue_eigenvector 15 := by
    rw [h_decomp]
    refine Finset.sum_eq_single (15 : Fin 18) (fun j _ hj => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    rw [h_reg j hj, zero_smul]
  rw [hcollapse]
  exact Submodule.smul_mem _ _ caseIIConjugateResidue_eigenvector_15_mem_omega32

/-! ## 2. The named leading-`λ`-exponent collapse (Washington Exercise 8.11, eigencomponent form)

This is the genuine remaining content of Washington Lemma 9.9's regular half, isolated precisely.
The proven local reduction (§0) turns "`Units.map u ≡` rational mod `37`" into the **`λ`-adic
statement** `completedLogArg(EPlus_completedLogDomainPowPred u) ∈ lambdaIdeal^{36}` — the `K`-level
completed log of `u^{36}` has `λ`-valuation `≥ 36`.  The remaining fact (Exercise 8.11, the
leading-`λ`-coefficient / Galois-graded computation) is that this `λ`-adic vanishing forces the
**regular** eigencomponents of `realUnitToFreePartModP u` to vanish: a regular `E_{2(j+1)}`
(`37 ∤ B_{2(j+1)}`) contributes, in the `ω^{2(j+1)}`-graded piece of the local log, a leading
coefficient that is a nonzero multiple of `B_{2(j+1)} mod 37`, sitting at `λ`-level `2(j+1) ≤ 34 <
36`; so its eigencomponent must be `0` for the `λ`-valuation to reach `36`.

We name **only** that residual leading-`λ`-coefficient implication (a `def … : Prop`, **not** an
axiom), phrased on the *output of the proven local reduction* — it is a genuine statement about the
local log's `λ`-graded leading coefficients, **not** a restatement of the ω³²-membership goal. -/

/-- **Washington Exercise 8.11, eigencomponent form, named** (a `def … : Prop`, **not** an axiom).

For every real unit `u : (𝓞 K⁺)ˣ` whose degree-`36` completed-log argument has `λ`-valuation `≥ 36`
(`completedLogArg(EPlus_completedLogDomainPowPred u) ∈ lambdaIdeal^{36}`, the *output* of the proven
local reduction `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`), the **regular**
eigencomponents of `realUnitToFreePartModP u` — its canonical Corollary-8.15 decomposition
coefficients at the regular indices `j ≠ 15` (`i = 2(j+1) ≠ 32`, `37 ∤ B_i`) — all vanish.

This is the leading-`λ`-coefficient computation of Washington Exercise 8.11 in the
Galois-eigenbasis: a regular cyclotomic unit `E_{2(j+1)}` has, in the `ω^{2(j+1)}`-graded piece of
the local logarithm, a leading coefficient that is a nonzero multiple of `B_{2(j+1)} mod 37` at
`λ`-level `2(j+1) ≤ 34 < 36`; since the hypothesis pins the log's `λ`-valuation at `≥ 36`, every
regular eigencomponent must vanish. It is **sound** — it constrains the eigencomponents of a unit
with this *specific* `λ`-adic log property, never an `E₃₂`-monomial property of an arbitrary real
unit.  It is **not** the ω³²-membership goal: it is a `λ`-adic leading-coefficient implication
feeding into the (proven) eigenspace endgame.

The premise `CompletedLogArgHighValuation37 u` is exactly the *output* of the proven local reduction
`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`, so the rational-mod-`37`
congruence discharges it (see `caseIILeadingExponent_regular_components_zero`): the only genuinely
undischarged content here is the Galois-graded leading-coefficient computation of Exercise 8.11. -/
def LeadingExponentEigenCollapse37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    CompletedLogArgHighValuation37 u →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0

/-- **Washington Lemma 9.9 regular-index collapse** (proven from the named Exercise-8.11 input +
the proven local reduction): for a real unit `u` whose `K`-image is `≡` rational mod `37`, the
regular eigencomponents of `realUnitToFreePartModP u` vanish.

The proven local reduction `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred` converts
the rational-mod-`37` congruence into the premise `CompletedLogArgHighValuation37 u` of
`LeadingExponentEigenCollapse37`, which then yields the regular eigencomponent vanishing.  Only the
leading-`λ`-coefficient implication `LeadingExponentEigenCollapse37` is an input; its analytic first
step (the `λ`-valuation `≥ 36`) is proven. -/
theorem caseIILeadingExponent_regular_components_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCollapse : LeadingExponentEigenCollapse37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0 :=
  hCollapse u (caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred u c hc)

/-! ## 3. `DescentUnitOmega32Membership37` from the leading-exponent collapse -/

/-- **`DescentUnitOmega32Membership37` from the named leading-exponent collapse** (proven,
axiom-clean given `LeadingExponentEigenCollapse37`).

For a real unit `u` with `Units.map u ≡ c (mod 37)`: the proven local reduction + the named
leading-`λ`-coefficient input (`caseIILeadingExponent_regular_components_zero`) kill the regular
coefficients `c_j` (`j ≠ 15`) of the canonical decomposition
`caseIIResidueProvenance_decomp (realUnitToFreePartModP u)` (whose reproduction is supplied by the
proven `caseIIResidueProvenance_decomp_spec`); and the **proven** eigenspace endgame
`caseIILeadingExponent_omega32_of_regular_components_zero` upgrades that to `ω³²`-eigenspace
membership. -/
theorem descentUnit_omega32Membership_of_leadingExponent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCollapse : LeadingExponentEigenCollapse37) :
    DescentUnitOmega32Membership37 := by
  intro u c hc
  refine caseIILeadingExponent_omega32_of_regular_components_zero
    (caseIIResidueProvenance_decomp
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)))
    (caseIIResidueProvenance_decomp_spec _) ?_
  exact caseIILeadingExponent_regular_components_zero hCollapse u c hc

end BernoulliRegular.FLT37.Eichler

end
