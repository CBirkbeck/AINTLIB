import BernoulliRegular.FLT37.Eichler.CaseII.Section91.MembershipFreeDescentReduction
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DescentQuotientRationalCongruence

/-!
# Washington Lemma 9.9 regular-index collapse for `p = 37`: ω³²-membership of the descent unit
from the rational-mod-`37` congruence (the leading-exponent mechanism, Exercises 8.10/8.11)

This file assembles the **non-circular** discharge of the Case-II descent-unit content for FLT at
`p = 37`, reducing it to a single sharp statement — the **ω³²-eigenspace membership of the descent
unit** — and proving that statement is exactly Washington's regular-index collapse, derived from the
rational-mod-`37` congruence of `ε₁/ε₂` (proven, `caseII_quotient_sub_intCast_mem_37`) *without* any
`p`-adic `L`-function.

It imports only; it does **not** modify any existing file.

## The mechanism (Washington Lemma 9.9, regular indices, pp. 180–181 via Exercises 8.10/8.11)

The descent unit `ε₁/ε₂ = η_a/η_b` is, by the Case-II Fermat equation, **congruent to a rational
integer mod `37`** (`caseII_quotient_sub_intCast_mem_37`, proven from the Fermat relation + the
Frobenius freshman's-dream `α³⁷ ≡ rational (mod 37)`).  Writing the real descent unit `u`
(`Units.map u = ε₁/ε₂`, realness **unconditional** via `caseIISigmaAntiDescent_quotient_unitsMap`) in
the Corollary-8.15 basis `u = γ³⁷ · ∏_i E_i^{d_i}` of `E⁺/(E⁺)³⁷`, the **λ-adic leading-exponent
argument** of Washington's Exercises 8.11 (each regular `E_i` has leading `λ`-exponent `c_i = i/2`,
`p ∤ B_i`) and 8.10 (a product has leading exponent `minᵢ(c_i + ((p-1)/2)·v_p(d_i))`) forces, for the
**regular** indices `i ≠ 32` (`37 ∤ B_i`),

  `37 ∣ d_i`,

because `c_i = i/2 < (p-1)/2 = 18` and "`≡ rational integer mod 37`" means the leading non-constant
`λ`-exponent is `≥ 18`.  Equivalently, the mod-`37` free-part class `realUnitToFreePartModP u` has
vanishing regular eigencomponents — i.e. it **lies in the single irregular `ω³²`-eigenspace** of the
Galois `Δ`-action.  (The irregular `i = 32` term is **not** forced to zero: `c_{32} ≥ 18`, so `E₃₂`
is itself `≡ rational mod 37`; its eigencomponent survives, handled downstream by the proven
membership-free eigenspace collapse `caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace`.)

This is the genuine regular-index mechanism of Lemma 9.9, and it uses **only** the leading-`λ`-exponent
of the cyclotomic units (Bernoulli-number data), **not** the `p`-adic `L`-function nor the conjugate
prime / Vandermonde detector (which Washington reserves for the *irregular* index).

## What this file proves (real, axiom-clean Lean)

* `DescentUnitOmega32Membership37` — the named **ω³²-membership** property: a real unit `u` whose
  `K`-image `Units.map u` is `≡` a rational integer mod `37` has `realUnitToFreePartModP u` in the
  `ω³²`-eigenspace.  This is the Lemma-9.9 regular-index collapse (Exercises 8.10/8.11), the **single
  remaining analytic-free Case-II descent-unit input** for `p = 37`.

* `caseIIOmega32_eigenCollapseData_of_membership` — feeding `DescentUnitOmega32Membership37`, the
  membership-free descent-unit provenance `Cor815EigenCollapseDescentData37` holds:  realness
  (unconditional) + the rational-mod-`37` congruence (proven) + ω³²-membership (the named input) give,
  for each Case-II instance, a real unit `u` with `Units.map u = ε₁/ε₂` and `Cor815EigenCollapseAt u`.

* `caseIIOmega32_assumptionII_of_membership_localPower` — **Assumption II**
  (`WashingtonCaseIIExactQuotientUnitPower37Source`) from the two precisely-named inputs
  `DescentUnitOmega32Membership37` and `Lemma98LocalPower37`.  Everything else — realness, the
  rational-mod-`37` congruence, the automatic eigencomponent decomposition, the membership-free
  eigenspace collapse, `SinnottIndexFormula 37`, the `Δ`-eigenvalue — is proven.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9 (pp. 180–181),
  Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 157), Theorem 8.16 (p. 157).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The named ω³²-membership input (Washington Lemma 9.9, regular-index collapse)

The single remaining Case-II descent-unit content is that a real unit `u` whose `K`-image is `≡` a
rational integer mod `37` lands, in the mod-`37` free part, in the irregular `ω³²`-eigenspace.  This
is the leading-`λ`-exponent collapse of Exercises 8.10/8.11; it is a `def … : Prop` (**not** an axiom,
**not** Assumption II) about the eigenspace membership of a real unit constrained by a rational
congruence — never about the global `37`-th-power-ness `ε₁/ε₂ = ε'³⁷`. -/

/-- **Washington Lemma 9.9 regular-index collapse, named** (a `def … : Prop`, **not** an axiom).

For every real unit `u : (𝓞 K⁺)ˣ` whose `K`-image `Units.map u` is congruent to a rational integer
modulo `37` (`∃ c : ℤ, 37 ∣ ↑(Units.map u) - c`), the mod-`37` free-part class
`realUnitToFreePartModP u` lies in the single irregular `ω³²`-eigenspace of the Galois `Δ`-action.

This is the regular-index half of Washington Lemma 9.9 for `p = 37`: writing `u = γ³⁷ ∏ E_i^{d_i}`
(Corollary 8.15, `37 ∤ h⁺`), the rational-mod-`37` congruence forces `37 ∣ d_i` for every regular
`i ≠ 32` (`37 ∤ B_i`) by the leading-`λ`-exponent bookkeeping of Exercises 8.11 (`c_i = i/2`) and 8.10
(product leading exponent), since `i/2 < 18 = (p-1)/2` and "`≡` rational mod `37`" forces leading
exponent `≥ 18`.  Only the `i = 32` eigencomponent can survive, so the class is in the `ω³²`-eigenspace.
It is **sound** — it constrains the eigencomponents of the *specific* rational-mod-`37` unit, never an
`E₃₂`-monomial property of an arbitrary real unit. -/
def DescentUnitOmega32Membership37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ),
    (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) →
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)

/-! ## 2. The membership-free provenance from the ω³²-membership input

Combining the **unconditional** realness `caseIISigmaAntiDescent_quotient_unitsMap`, the **proven**
rational-mod-`37` congruence `caseII_quotient_sub_intCast_mem_37`, and the named ω³²-membership
input, the membership-free descent-unit provenance `Cor815EigenCollapseDescentData37` holds. -/

open FLT37.LehmerVandiver.CaseII in
/-- **The membership-free provenance from ω³²-membership** (proven, axiom-clean given
`DescentUnitOmega32Membership37`).

For each Case-II descent instance: the unconditional realness `caseIISigmaAntiDescent_quotient_unitsMap`
gives a real unit `u` with `Units.map u = ε₁/ε₂`; the proven `caseII_quotient_sub_intCast_mem_37` gives
`ε₁/ε₂ ≡ c (mod 37)` for some `c : ℤ`; feeding both to `DescentUnitOmega32Membership37` puts
`realUnitToFreePartModP u` in the `ω³²`-eigenspace; and the proven membership-free eigenspace collapse
`caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace` upgrades that to `Cor815EigenCollapseAt u`. -/
theorem caseIIOmega32_eigenCollapseData_of_membership
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMem : DescentUnitOmega32Membership37) :
    Cor815EigenCollapseDescentData37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  -- Unconditional realness: the canonical `K⁺`-descent `u` of `ε₁/ε₂`.
  obtain ⟨u, hu⟩ := caseIISigmaAntiDescent_quotient_unitsMap D.hζ D.one_le_m hx hy hz heq
  -- Proven rational-mod-`37` congruence of `ε₁/ε₂`.
  obtain ⟨c, hc⟩ := caseII_quotient_sub_intCast_mem_37 D.hζ D.one_le_m hx heq
  refine ⟨u, ?_, hu⟩
  -- ω³²-membership of `realUnitToFreePartModP u`, then the membership-free eigenspace collapse.
  apply caseIIExplicitDescent_eigenCollapse_of_mem_omega32_eigenspace u
  apply hMem u c
  -- Goal: `37 ∣ ↑(Units.map u) - c`.  Rewrite `Units.map u = ε₁/ε₂` and use `hc`.
  rw [hu]
  exact hc

/-! ## 3. Assumption II from the ω³²-membership input + Lemma 9.8 local power

Composing §2 with the proven `caseIIExplicitDescent_assumptionII_of_eigenCollapseData`: **Assumption
II** follows from the *two* precisely-named inputs — the Lemma-9.9 regular-index collapse
`DescentUnitOmega32Membership37` and the Lemma-9.8 single-index local power `Lemma98LocalPower37`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from ω³²-membership + the Lemma-9.8 local power** (proven, axiom-clean).

`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II: the descent unit `ε₁/ε₂` is a
`37`-th power) follows from

* `DescentUnitOmega32Membership37` — Washington Lemma 9.9's regular-index collapse (the
  leading-`λ`-exponent mechanism, Exercises 8.10/8.11), supplying the descent unit's ω³²-membership;
  and
* `Lemma98LocalPower37` — Washington Lemma 9.8's single-index mod-`𝔩` Kummer congruence.

Everything else is proven: the **unconditional** realness of `ε₁/ε₂`
(`caseIISigmaAntiDescent_quotient_unitsMap`), the rational-mod-`37` congruence
(`caseII_quotient_sub_intCast_mem_37`), the automatic eigencomponent decomposition, the membership-free
eigenspace collapse, `SinnottIndexFormula 37`, and the `Δ`-action eigenvalue.  No cyclotomic membership
`w ∈ C⁺` and no `p`-adic `L`-function are used. -/
theorem caseIIOmega32_assumptionII_of_membership_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hMem : DescentUnitOmega32Membership37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIExplicitDescent_assumptionII_of_eigenCollapseData
    (caseIIOmega32_eigenCollapseData_of_membership hMem) h_localPow

end BernoulliRegular.FLT37.Eichler

end
