import BernoulliRegular.FLT37.Eichler.CaseIISigmaAntiDescent

/-!
# Washington §9.1 cyclotomic identification of the Case-II descent unit `η_a/η_b`

This file builds the **cyclotomic-unit identification** half of piece (i) of
`Cor815RealDescentResidueDataProvenance37`: that the real `K⁺`-descent `u` of the Case-II
descent unit `ε₁/ε₂` (Washington's `η_a/η_b`) lies in the cyclotomic-unit subgroup
`C⁺ = caseIICPlus37`.  It imports only; it does **not** modify any existing file.

## The math (Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 169-172)

In Washington's Case-II descent the descent unit is built from `(1-ζ^a)`-factors:

  `η_a = (ω_j + ζ^a ω_j)/(1 - ζ^a)`,        (Washington §9.1, p. 170)

and the descent quotient `η_a/η_b` is, up to the σ-pair descent `ρ`'s and a root of unity, a
ratio of the explicit cyclotomic units `(1 - ζ^k)/(1 - ζ)`.  After the realness descent of §2 of
`CaseIISigmaAntiDescent.lean` (the unconditional free-Case-II-primarity result), `u = ε₁/ε₂`
descends to a **real** unit of `𝓞 K⁺`, and the same `(1-ζ^a)`-construction expresses that real
descent as a product of the **real** cyclotomic units `ν_a = (1-ζ^a)(1-ζ^{-a})/((1-ζ)(1-ζ^{-1}))`
— exactly the family generators `CPlusGenerator a = realCyclotomicUnit a` whose closure (with the
sign `-1`) is `C⁺ = caseIICPlus37` (`caseIIGaloisEigen_caseIICPlus37_eq_CPlus`).

Concretely: the descent unit `u`, being the `K⁺`-norm-descent of the `(1-ζ^a)`-built `η_a/η_b`, is
an **integer-exponent product of `-1` and the real cyclotomic-unit family generators** — i.e. a
`CPlusExponentProduct s e` in the sense of `CyclotomicUnits/Saturation.lean`.  Every such product
lies in `C⁺` by subgroup closure (`CPlusExponentProduct_mem_CPlus`), so `u ∈ caseIICPlus37`.

## What this file proves (real, axiom-clean Lean)

* `caseIICyclotomicIdentification_CPlusExponentProduct_mem` — **the closure-membership core**
  (proven, unconditional): every integer-exponent cyclotomic-unit product
  `CPlusExponentProduct 37 s e` (a product of `-1` and the real cyclotomic-unit family generators
  `CPlusGenerator a`) lies in `caseIICPlus37`.  This is the load-bearing fact: `C⁺` is *generated*
  by exactly these, so the §9.1 `(1-ζ^a)`-form of `η_a/η_b` lands in `C⁺`.

* `caseIICyclotomicIdentification_mem_of_eq_product` — **the bridge** (proven, unconditional): if a
  real unit `u` equals such a cyclotomic-unit product `u = CPlusExponentProduct 37 s e`, then
  `u ∈ caseIICPlus37`.

* `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct` — **the precise remaining §9.1
  content** named as a `def … : Prop` (**not** an axiom): for every Case-II descent instance, the
  canonical `K⁺`-descent `u` of `ε₁/ε₂` is an explicit cyclotomic-unit product
  `u = CPlusExponentProduct 37 s e`.  This is exactly Washington §9.1's `(1-ζ^a)`-form of `η_a/η_b`
  (the explicit construction `η_a = (ω_j + ζ^a ω_j)/(1-ζ^a)`, pp. 169-172) — a fact about the
  *concrete* descent unit, never about an arbitrary real unit.

* `caseIICyclotomicIdentification_quotient_in_CPlus_of_product` — **discharging the target**
  (proven, axiom-clean): the §9.1-form hypothesis above implies
  `caseIISigmaAntiDescent_quotient_in_CPlus`, the C⁺-membership conjunct of piece (i).  The
  closure-membership work is *proven* here; the only remaining input is the explicit §9.1
  `(1-ζ^a)`-form, named sharply.

* `caseIICyclotomicIdentification_realness_membership_of_product` and
  `caseIICyclotomicIdentification_residueDataProvenance_of_product` and
  `caseIICyclotomicIdentification_assumptionII_of_product` — the **wiring**: combining the §9.1
  cyclotomic-form hypothesis with the unconditional realness of §2 of `CaseIISigmaAntiDescent.lean`
  discharges the realness/membership conjunct of piece (i), the residue-data provenance, and (with
  the Lemma-9.8 residue equations + `Lemma98LocalPower37`) **Assumption II** — leaving only the
  Washington Lemma-9.8 residue equations `(ii′)` as the residual Case-II content.

## What remains (the precise §9.1 source)

The single remaining cyclotomic-unit input is
`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`: that the descent unit `u` is the
explicit cyclotomic-unit product.  This is the verbatim content of Washington §9.1, pp. 169-172 —
the explicit construction of `η_a = (ω_j + ζ^a ω_j)/(1-ζ^a)` and the resulting `(1-ζ^a)/(1-ζ)`-form
of `η_a/η_b`.  That explicit construction (the `ω_j`, the `ζ^a`-numerators) is the one piece of the
§9.1 descent not present in the repo's abstract `CaseIIData37` (whose `ε₁, ε₂, ε₃` are unconstrained
units); everything *downstream* of it — the closure-membership of the `(1-ζ^a)`-form in `C⁺`, and the
wiring into piece (i) — is proved here.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`,
  pp. 169-172), Lemma 9.1, Lemma 9.2, Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The closure-membership core: cyclotomic-unit products lie in `C⁺`

`caseIICPlus37 = C⁺ = CPlus 37` is *generated* by `-1` and the real cyclotomic-unit family
generators `CPlusGenerator a = realCyclotomicUnit a` (Washington's `ν_a`).  Hence every
integer-exponent product `CPlusExponentProduct 37 s e` of these lies in `C⁺` — this is the proven
`CPlusExponentProduct_mem_CPlus` transported across `caseIIGaloisEigen_caseIICPlus37_eq_CPlus`. -/

/-- **Every cyclotomic-unit product lies in `C⁺`** (proven, unconditional).

For any sign exponent `s : ℤ` and family exponents `e : Fin 17 → ℤ`, the integer-exponent product
`CPlusExponentProduct 37 s e = (-1)^s · ∏ a, CPlusGenerator a ^ e a` of the real cyclotomic-unit
family generators lies in `caseIICPlus37`.

This is the load-bearing closure fact: `C⁺ = caseIICPlus37` is generated by exactly `-1` and the
real cyclotomic units `CPlusGenerator a = realCyclotomicUnit a`, so Washington §9.1's
`(1-ζ^a)/(1-ζ)`-form of the descent unit `η_a/η_b` lands in `C⁺`. -/
theorem caseIICyclotomicIdentification_CPlusExponentProduct_mem
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ) :
    BernoulliRegular.CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e ∈
      caseIICPlus37 := by
  rw [caseIIGaloisEigen_caseIICPlus37_eq_CPlus]
  exact BernoulliRegular.CPlusExponentProduct_mem_CPlus
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e

/-- **A real unit equal to a cyclotomic-unit product lies in `C⁺`** (proven, unconditional).

If a real unit `u : (𝓞 K⁺)ˣ` equals an integer-exponent cyclotomic-unit product
`u = CPlusExponentProduct 37 s e`, then `u ∈ caseIICPlus37`.  Immediate from
`caseIICyclotomicIdentification_CPlusExponentProduct_mem`. -/
theorem caseIICyclotomicIdentification_mem_of_eq_product
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ)
    (hu : u =
      BernoulliRegular.CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e) :
    u ∈ caseIICPlus37 := by
  rw [hu]
  exact caseIICyclotomicIdentification_CPlusExponentProduct_mem s e

/-! ## 2. The precise remaining §9.1 content: the descent unit is a cyclotomic-unit product

Piece (i) of `Cor815RealDescentResidueDataProvenance37` asks for the real descent unit `u` (the
unconditional `K⁺`-descent of `ε₁/ε₂` from §2 of `CaseIISigmaAntiDescent.lean`) to lie in
`C⁺ = caseIICPlus37`.  By §1 above, this follows once `u` is *expressed* as an explicit
cyclotomic-unit product `CPlusExponentProduct 37 s e`.

This expression is exactly Washington §9.1's `(1-ζ^a)`-form of `η_a/η_b` (pp. 169-172): the
descent unit `η_a = (ω_j + ζ^a ω_j)/(1-ζ^a)` is built from `(1-ζ^a)`-factors, and its real
`K⁺`-descent is a product of the real cyclotomic units `ν_a = CPlusGenerator a`.  We name precisely
this expression as a `def … : Prop` (**not** an axiom). -/

/-- **The descent unit is an explicit cyclotomic-unit product** (a `def … : Prop`, **not** an
axiom).

For every Case-II descent instance, the canonical `(𝓞 K⁺)ˣ`-descent `u` of `ε₁/ε₂` (the realness of
which is the *unconditional* `caseIISigmaAntiDescent_quotient_unitsMap` of §2 of
`CaseIISigmaAntiDescent.lean`) equals an explicit integer-exponent cyclotomic-unit product
`u = CPlusExponentProduct 37 s e` of the real cyclotomic-unit family generators.

This is the *only* cyclotomic-unit content of piece (i) not yet discharged: Washington §9.1's
explicit `(1-ζ^a)`-form of the descent unit `η_a` (the construction
`η_a = (ω_j + ζ^a ω_j)/(1-ζ^a)`, pp. 169-172, whose real `K⁺`-descent is a product of the cyclotomic
units `ν_a`).  It is **sound** — it asserts an explicit cyclotomic-unit expression for the *specific*
descent unit, never for an arbitrary real unit (a generic real unit need not lie in `C⁺`, whose
index in `(𝓞 K⁺)ˣ` is `h⁺`).  The realness in `Units.map` form is supplied by §2, so the assertion
is stated only about the canonical `K⁺`-descent `u`. -/
def caseIICyclotomicIdentification_quotient_isCPlusExponentProduct
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (_hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (_hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (_hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (_heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37)
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (_hu : Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u = ε₁ / ε₂),
    ∃ (s : ℤ) (e : Fin ((37 - 3) / 2) → ℤ),
      u = BernoulliRegular.CPlusExponentProduct
        (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e

/-! ## 3. Discharging `caseIISigmaAntiDescent_quotient_in_CPlus`

The target `def : Prop` `caseIISigmaAntiDescent_quotient_in_CPlus` (of `CaseIISigmaAntiDescent.lean`)
asks, for each Case-II descent instance, for the canonical descent unit `u` to lie in
`caseIICPlus37`.  Combining the §9.1 cyclotomic-form hypothesis (§2) with the proven
closure-membership core (§1) discharges it directly. -/

/-- **`caseIISigmaAntiDescent_quotient_in_CPlus` from the §9.1 cyclotomic form** (proven,
axiom-clean).

Given the Washington §9.1 cyclotomic-unit form
(`caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`: the descent unit `u` equals an
explicit cyclotomic-unit product), the C⁺-membership conjunct
`caseIISigmaAntiDescent_quotient_in_CPlus` of piece (i) holds: for every Case-II descent instance,
the canonical `K⁺`-descent `u` of `ε₁/ε₂` lies in `caseIICPlus37`.

The closure-membership step (`caseIICyclotomicIdentification_mem_of_eq_product`, from the proven
`CPlusExponentProduct_mem_CPlus`) is *proven* here; only the explicit §9.1 `(1-ζ^a)`-form remains as
the named input. -/
theorem caseIICyclotomicIdentification_quotient_in_CPlus_of_product
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_form : caseIICyclotomicIdentification_quotient_isCPlusExponentProduct) :
    caseIISigmaAntiDescent_quotient_in_CPlus := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' heq u hu
  obtain ⟨s, e, hue⟩ := h_form hV hSO D hx' hy' hz' heq u hu
  exact caseIICyclotomicIdentification_mem_of_eq_product u s e hue

/-! ## 4. Wiring: piece (i), the residue-data provenance, and Assumption II

With `caseIISigmaAntiDescent_quotient_in_CPlus` discharged from the §9.1 cyclotomic form, the
realness/membership conjunct of piece (i) — and, together with the Lemma-9.8 residue equations and
`Lemma98LocalPower37`, **Assumption II** — follow from the proven §2 realness and §3–§6 wiring of
`CaseIISigmaAntiDescent.lean`. -/

/-- **Realness + membership of `η_a/η_b` from the §9.1 cyclotomic form** (proven, axiom-clean).

Composing `caseIICyclotomicIdentification_quotient_in_CPlus_of_product` with the proven
`caseIISigmaAntiDescent_realness_membership`: from the Washington §9.1 cyclotomic-unit form, the
realness/membership conjunct of piece (i) of `Cor815RealDescentResidueDataProvenance37` holds — for
every Case-II descent instance there is `w ∈ caseIICPlus37` with `Units.map w = ε₁/ε₂`.

The **realness** (the `(𝓞 K⁺)ˣ`-descent) is the *unconditional* §2 result of
`CaseIISigmaAntiDescent.lean`; only the cyclotomic-unit form is supplied as the named §9.1 input. -/
theorem caseIICyclotomicIdentification_realness_membership_of_product
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_form : caseIICyclotomicIdentification_quotient_isCPlusExponentProduct)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : FLT37.LehmerVandiver.CaseII.CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)} {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ w ∈ caseIICPlus37,
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂ :=
  caseIISigmaAntiDescent_realness_membership
    (caseIICyclotomicIdentification_quotient_in_CPlus_of_product h_form)
    hV hSO D hx' hy' hz' heq

open FLT37.LehmerVandiver.CaseII in
/-- **The residue-data provenance from the §9.1 cyclotomic form + Lemma 9.8 residue equations**
(proven, axiom-clean).

Composing `caseIICyclotomicIdentification_quotient_in_CPlus_of_product` with the proven
`caseIISigmaAntiDescent_residueDataProvenance`: from the Washington §9.1 cyclotomic-unit form
(`h_form`, discharging the C⁺-membership of piece (i)) together with the Washington Lemma-9.8
residue equations on the canonical descent unit (`h_res`), the full descent-unit provenance
`Cor815RealDescentResidueDataProvenance37` holds.

In particular **piece (i) is now fully discharged** — its realness (`Units.map w = ε₁/ε₂`) is the
unconditional §2 result, and its C⁺-membership is the proven closure of the §9.1 form — so the only
remaining Case-II content is the bare Lemma-9.8 residue equations `(ii′)`. -/
theorem caseIICyclotomicIdentification_residueDataProvenance_of_product
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_form : caseIICyclotomicIdentification_quotient_isCPlusExponentProduct)
    (h_res : caseIISigmaAntiDescent_residueEqns) :
    Cor815RealDescentResidueDataProvenance37 :=
  caseIISigmaAntiDescent_residueDataProvenance
    (caseIICyclotomicIdentification_quotient_in_CPlus_of_product h_form) h_res

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the §9.1 cyclotomic form + Lemma 9.8** (proven, axiom-clean).

Composing `caseIICyclotomicIdentification_quotient_in_CPlus_of_product` with the proven
`caseIISigmaAntiDescent_assumptionII`: **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`) follows from

* `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct` — Washington §9.1's explicit
  `(1-ζ^a)`-form of the descent unit `η_a/η_b` (discharging the C⁺-membership of piece (i));
* `caseIISigmaAntiDescent_residueEqns` — Washington Lemma 9.8's residue equations on the canonical
  descent unit; and
* `Lemma98LocalPower37` — Washington Lemma 9.8's single-index mod-`𝔩` Kummer congruence.

The **realness** of `η_a/η_b = ε₁/ε₂` and its **C⁺-membership** are no longer separate parametric
inputs: realness is the unconditional §2 result of `CaseIISigmaAntiDescent.lean`, and membership is
the proven closure of the §9.1 form. -/
theorem caseIICyclotomicIdentification_assumptionII_of_product
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_form : caseIICyclotomicIdentification_quotient_isCPlusExponentProduct)
    (h_res : caseIISigmaAntiDescent_residueEqns)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIISigmaAntiDescent_assumptionII
    (caseIICyclotomicIdentification_quotient_in_CPlus_of_product h_form) h_res h_localPow

end BernoulliRegular.FLT37.Eichler

end
