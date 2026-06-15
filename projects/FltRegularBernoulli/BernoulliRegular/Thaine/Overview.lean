import BernoulliRegular.Thaine.AuxiliaryUnits
import BernoulliRegular.Thaine.AuxiliaryPrimes
import BernoulliRegular.Thaine.KolyvaginDerivative
import BernoulliRegular.Thaine.AnnihilatorDescent
import BernoulliRegular.Thaine.SingleCharacter
import BernoulliRegular.Thaine.HerbrandRibetThirtySeven
import BernoulliRegular.Thaine.UniqueIrregularData
import BernoulliRegular.Thaine.RankOneComponent
import BernoulliRegular.Thaine.CircularUnits
import BernoulliRegular.Thaine.PollaczekRankOne

/-!
# Thaine pivot — overview module

This module imports and re-documents the Thaine-pivot subtree shipped
post-2026-05-06 expert review. Importing this single module makes
every Thaine-route file available downstream.

## Subtree

- `AuxiliaryUnits.lean`: T-THAINE-1 —
  `auxiliaryZetaToInteger`, `auxiliaryCyclotomicUnitOneMinus`.
- `AuxiliaryPrimes.lean`: T-THAINE-2 —
  `IsThaineAuxiliary p n ℓ` predicate; FLT37 witness ℓ = 149.
- `KolyvaginDerivative.lean`: T-THAINE-3 —
  `KolyvaginDerivativeData p n` parametric structure.
- `AnnihilatorDescent.lean`: T-THAINE-4 —
  `ThaineAnnihilatorDescent p` parametric statement.
- `SingleCharacter.lean`: T-THAINE-5 —
  `ThaineSingleCharCorollary p` (Kučera-style).
- `HerbrandRibetThirtySeven.lean`: `not_dvd_bernoulli_thirtyseven_except_thirtytwo` —
  Bernoulli divisibility data for p = 37.
- `UniqueIrregularData.lean`: `UniqueIrregularData p i_irreg` packaging;
  concrete FLT37 instance.
- `RankOneComponent.lean`: T-Q1-RANK-ONE — abstract atomic lemma
  `¬ p ∣ a ⟺ (R/(a))[p] = 0` for PID R, prime p, nonzero a.
- `CircularUnits.lean`: T-Q1-CSINNOTT — `circularSubgroupKplus`
  (Sinnott `C_S` = Washington `C_cl` for prime conductor).
- `PollaczekRankOne.lean`: T-Q1-RANK-ONE specialisation —
  `pollaczek_rankOne_specialisation` parametric theorem connecting the
  K-side certificate to the eigenspace torsion vanishing.

The Thaine pivot's downstream entry point is in
`BernoulliRegular/FLT37/LehmerVandiver/PlusCoprime/Thaine/`:

- `UnitClassBridge.lean`: T-PIVOT-1 + T-PIVOT-1-REFINE — bridge structure +
  content-bearing `cor8_19Bridge_of_componentTrivialities`.
- `PollaczekComponent.lean`, `ReflectionOther.lean`:
  T-PIVOT-4/5 — bridge field discharges (opaque-Prop layer).
- `CertificateAudit.lean`: T-PIVOT-3 — global-form Pollaczek certificate.
- `Bridge.lean`: T-THAINE-6 — `ThaineSingleCharDischarge` +
  `ReflectionOtherDischarge` + `cor8_19Bridge_of_thaineAndReflection`.
- `RegularInstance.lean`: regular-prime instance demonstrating the chain composes.
- `FinalAssembly.lean`: T-FLT37-FINAL —
  `fermatLastTheoremFor_thirtyseven_of_thaine`.

## Open work

The following remain *open* substantive content (research-grade Lean):

* The body of `ThaineSingleCharDischarge.thaine_at_i` — the actual
  Thaine annihilator at single character. Decomposed into
  T-THAINE-3/4/5 sub-pieces, each ~300–600 lines per [Wash97 §15].
* `T-NO-SECOND-ORDER`: `37³ ∤ B_{1184}` — currently blocked on a
  `bernoulli_mod_decide` tactic for fast modular Bernoulli evaluation.
* Stage 2 Kummer's lemma adapted (Case I, existing in_progress) — CFT
  descent on unramified Kummer extensions.

## At the parametric level

The chain is **closed sorry-free + axiom-clean**:
`fermatLastTheoremFor_thirtyseven_of_thaine` produces `FermatLastTheoremFor 37`
parametric on the Thaine pivot inputs + existing CaseI/CaseII bridges.
-/

@[expose] public section

namespace BernoulliRegular.Thaine

/-- Marker theorem ensuring the Thaine pivot subtree composes. -/
theorem thaine_pivot_overview : True := trivial

end BernoulliRegular.Thaine
