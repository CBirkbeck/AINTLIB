import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Main
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Main

/-!
# LV011 / FLT37 final assembly (corrected, parametric)

The Washington 9.5 / Lehmer-Vandiver chain for `p = 37` is parametric on
**five** structural data fields (post-review correction):

- `unique_irregular`: for `p = 37`, the unique irregular index is `32`.
- `local_to_global_real`: lifts the LV004g local certificate (mod `𝔩`)
  to a global non-`p`-th-power statement on the real form
  `pollaczekUnitPlus`.
- `cor8_19_real`: `¬ IsPthPower(pollaczekUnitPlus) → ¬ p ∣ h⁺`
  (Cor 8.19, real form; Sinnott's index formula content).
- `caseI_vandiver1934`: `¬ p ∣ h⁺ → no case I` (Vandiver 1934 Theorem 1;
  Stickelberger annihilation hidden internally).
- `noSecondOrderIrregularPair`: `37³ ∤ B_{32·37}` (Washington 9.4
  precondition).
- `caseII_washington94`: `¬ p ∣ h⁺ + NoSecondOrderIrregular → no case II`
  (Washington Theorem 9.4).

**Removed (post-review)**: the `StickelbergerKBridge` field — it was
mathematically false as previously stated (`¬ p ∣ h⁺ → all p-torsion
trivial` overstates: for irregular `p = 37`, `Cl(K)⁻[p] ≠ 0`).
Stickelberger annihilation is used inside `CaseIBridge` but is no
longer exposed at the bundle boundary.

Each field's construction is deferred to follow-up; once filled, FLT37
is unconditional.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

/-- **FLT37 bridge bundle (corrected, real form)**: convenience structure
packaging all five LV-route bridges into a single object.

The local certificate `local_to_global_real` connects LV004g's bare-form
closure to the real form needed by Cor 8.19. -/
structure FLT37BridgeBundle where
  /-- The real-form local certificate `¬ IsPthPowerModPrime
  pollaczekUnitPlus` mod the LV-prime, derived from LV004g's bare-form
  closure (via either re-decide or bare-to-real transfer). -/
  realLocalCert :
    ¬ IsPthPowerModPrime 37
      (FLT37.lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))
  /-- Cor 8.19 bridge (real form): `¬ IsPthPower(pollaczekUnitPlus) →
  ¬ 37 ∣ h⁺(K)`. -/
  cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32
  /-- Vandiver 1934 case I bridge: `¬ 37 ∣ h⁺ → no case I`. -/
  caseI : CaseIBridge 37 (CyclotomicField 37 ℚ)
  /-- Second-order non-irregularity at (37, 32): `37³ ∤ B_{32·37}`. -/
  noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32
  /-- Washington Theorem 9.4 case II bridge: `¬ 37 ∣ h⁺ + Bernoulli →
  no case II`. -/
  caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32

/-- **FLT37 from bridge bundle**: clean one-shot interface. Once the
bundle is constructed, this delivers `FermatLastTheoremFor 37`. -/
theorem fermatLastTheoremFor_thirtyseven_of_bundle
    (bundle : FLT37BridgeBundle) : FermatLastTheoremFor 37 := by
  -- Step 1: realLocalCert + cor8_19 → ¬ 37 ∣ hPlus K (via LV006).
  have hVan37 : FLT37.Vandiver37PlusCoprime :=
    FLT37.vandiver37PlusCoprime_of_bridge bundle.cor8_19 bundle.realLocalCert
  have h_not_dvd_hPlus :
      ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime hVan37
  -- Step 2: caseI bridge → no case I.
  have h_caseI : ∀ ⦃a b c : ℤ⦄,
      ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
    bundle.caseI.no_caseI_solution h_not_dvd_hPlus
  -- Step 3: caseII bridge + noSecondOrderIrregular → no case II.
  have h_caseII : ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 →
      ({a, b, c} : Finset ℤ).gcd id = 1 →
      ((37 : ℤ) ∣ a * b * c) → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
    bundle.caseII.no_caseII_solution h_not_dvd_hPlus bundle.noSecondOrderIrregular
  -- Step 4: combine via case-decomposition (FltRegular.MayAssume.coprime).
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc heq
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime heq hprod
  let d : ℤ := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : (37 : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact h_caseII hprod' hgcd case e'
  · exact h_caseI case e'

/-- **FLT37 from nonempty bundle**: clean reduction of FLT37 to the
existence of `FLT37BridgeBundle`. -/
theorem fermatLastTheoremFor_thirtyseven_of_nonempty_bundle
    (h : Nonempty FLT37BridgeBundle) : FermatLastTheoremFor 37 :=
  h.elim fermatLastTheoremFor_thirtyseven_of_bundle

end BernoulliRegular

end
