import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.UnitClassBridge

/-!
# T-PIVOT-4: `pollaczekUnitComponent` — certificate ⟹ unit-quotient eigencomponent trivial

The first of the four `FLT37UnitClassBridge` field discharges. Given the
existing `realLocalCert` (LV004g, σ-symmetric by construction; see
T-PIVOT-3), we get the global form
`∀ α : (𝓞 K)ˣ, pollaczekUnitPlus ≠ α^p` via the local-to-global lift
`not_isPthPower_unit_of_not_isPthPowerModPrime`. This ticket packages the
implication `(∀ α, ≠ α^p) ⟹ UnitQuotientComponentTrivial` as a Lean
function, slotting it into the bridge's first field.

**Note (2026-05-06):** at this stage `UnitQuotientComponentTrivial` is an
opaque carrier Prop in `UnitClassBridge.lean`, defined as a tautology
`∀ (_ : (p, i, K) = (p, i, K)), True`. The discharge here is therefore a
one-liner. The substantive eigenspace formulation is deferred to a
follow-up refinement that makes the Prop content-bearing — at which
point the proof here will need to be strengthened to actually witness
the rank-1 ω^i-eigencomponent triviality from
`pollaczekUnitPlus ≠ α^p`.

## References

* T-PIVOT-1 (`UnitClassBridge.lean`) — the bridge structure and the
  opaque Prop definitions.
* T-PIVOT-3 (`CertificateAudit.lean`) — the global-form certificate
  `flt37_realLocalCert_global`.
* [Wash97] §8.3 — the eigenspace structure of cyclotomic units (for
  the eventual non-trivial Prop refinement).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **T-PIVOT-4 implication**: from the global form
`∀ α : (𝓞 K)ˣ, pollaczekUnitPlus ≠ α^p`, conclude
`UnitQuotientComponentTrivial p K i`.

After the 2026-05-07 reframing, `UnitQuotientComponentTrivial` is
defined as the K-side certificate form (the same as the input
hypothesis), so this implication is the identity. The eigencomponent /
annihilator equivalence (`(E⁺/C_S)(ω^i)[p] = 0` ⟺ K-side certificate)
is supplied by `T-Q1-RANK-ONE`; with that equivalence, the bridge is
non-trivial as an annihilator statement. -/
theorem unitQuotientComponentTrivial_of_not_isPthPower (i : ℕ) :
    (∀ α : (𝓞 K)ˣ,
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
          ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) →
      UnitQuotientComponentTrivial p K i := id

end BernoulliRegular

end
