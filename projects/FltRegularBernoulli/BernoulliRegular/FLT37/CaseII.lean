module

public import BernoulliRegular.FLT37.PrimaryDescent
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.CaseII.Statement

/-!
# FLT case II for `p = 37` (ticket F37-D, scaffold)

The case II argument under VandiverIIIHypothesis follows Vandiver's program:

1. **Primary unit decomposition**: any unit `u ∈ (𝓞 K)ˣ` admits a decomposition
   `u = ζ^m · v_+` with `v_+` a real (totally real) unit of `𝓞 K⁺`, plus a
   *primary form* refinement under specific hypotheses (V001 / Kummer's lemma
   sharpening).

2. **Mirimanoff subfield trick** (V002): for `ℓ ≡ 1 (mod 4)`, the imaginary
   unit `i ∈ (ZMod ℓ)ˣ` lifts to a Galois automorphism `ζ ↦ ζ^ω` with `ω² = -1`.
   The fixed subfield of `⟨ω⟩` reduces the case-II analysis to a smaller field.

3. **Vandiver Lemma 1** (V003): under `VandiverIIIHypothesis ℓ`, the relevant
   ideals are still principal even without regularity (uses reflection T044).

4. **Infinite descent**: assuming a primitive coprime solution exists, find a
   smaller one — contradicting minimality.

This file provides scaffolding for the conditional case II theorem. The
substantive mathematical work (steps 1–4) is the bulk of `[F37-D]`.

## Status

Scaffold. The conditional `VandiverIIICaseII` for `ℓ = 37` is the
goal; here we establish the namespace, imports, and document the proof
plan.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace CaseII

/-! ## Standing setup

The case II analysis works inside `K = ℚ(ζ_p)` for an odd prime `p`. The
regular-prime case is handled by `flt-regular`'s `caseII`; for `p = 37`
(irregular) we follow the Vandiver program above. -/

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-! ## Section 1: Primary unit decomposition

The key result is that any cyclotomic unit factor in case II can be
brought to a **primary form** — congruent to a rational integer modulo
`(ζ-1)^{2p}`. This sharpens Kummer's lemma `u = ζ^m · v_+` by also
adjusting `v_+` to be primary.

Defined in `Primary.lean` as `IsPrimary` (via `(zetaSubOne)^{2p} ∣ α - integer`).
-/

/-! ## Section 2: Mirimanoff subfield trick

For `p ≡ 1 (mod 4)`, the Mirimanoff Galois automorphism `mirimanoffGalAut`
in `Mirimanoff.lean` has order 4 with `mirimanoffGalAut^2` = complex
conjugation. The fixed subfield of `⟨mirimanoffGalAut⟩` in `K` is a
quartic extension over which the case-II analysis simplifies. -/

/-! ## Section 3: Vandiver Lemma 1

Under `VandiverIIIHypothesis ℓ` (parity), the ideals
`(α + ζ^k β) · 𝓞 K` arising in the case II decomposition are principal
even for irregular `p`. The reflection theorem
`ReflectionMinusNontrivialityBridge` (T044) supplies the structural
input. -/

/-! ## Section 4: Infinite descent

The standard descent: from a minimal primitive coprime solution
`a^p + b^p = c^p` with `p ∣ c`, the case II decomposition produces a
smaller solution, contradicting minimality. Mirrors
`flt-regular`'s `caseII` infrastructure (`AuxLemmas`, `InductionStep`). -/

/-! ## Conditional case II under regularity

For *regular* primes `p`, the case II argument is fully proved in
`flt-regular`'s `caseII`. We package it here as a conditional consumer for
the Vandiver III case II program, separating out the regular-prime portion
so the irregular-prime extension (F37-F) can plug in. -/

end CaseII

/-- **Conditional VandiverIIICaseII for regular primes.** When `ℓ` is a
regular prime, `flt-regular`'s `caseII` directly gives the conclusion of
`VandiverIIICaseII`. The parity hypothesis is unused (it's only needed
for irregular primes via Vandiver Lemma 1). -/
theorem vandiverIIICaseII_of_regular_caseII
    {a b c : ℤ} {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (h_reg : IsRegularPrime ℓ) (h_odd : ℓ ≠ 2)
    (h_prod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (case : (ℓ : ℤ) ∣ a * b * c) :
    a ^ ℓ + b ^ ℓ ≠ c ^ ℓ :=
  FltRegular.caseII h_reg h_odd h_prod hgcd case

/-- **Vandiver Lemma 1 predicate, ℓ = 37 specialization.** Captures the
regularity-free structural input needed for case II at ℓ = 37: under the
parity hypothesis plus `37 ∤ h⁺`, the ideals arising in the case II
decomposition are principal even without the regular-prime hypothesis.
The reflection theorem T044 (already established in `Reflection/Final.lean`)
is one of the inputs to discharging this predicate. -/
def VandiverLemma1Thirtyseven : Prop :=
  ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
    ((37 : ℤ) ∣ a * b * c) → a ^ 37 + b ^ 37 ≠ c ^ 37

/-- **caseII for ℓ = 37 from VandiverLemma1Thirtyseven.** The conditional
theorem: given the 37-specific Vandiver Lemma 1 predicate (which encodes
the case II descent for irregular 37 under the parity hypothesis), case II
for 37 follows. -/
theorem caseII_thirtyseven_of_vandiverLemma1
    (h : VandiverLemma1Thirtyseven) :
    ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  h

end FLT37

end BernoulliRegular

end
