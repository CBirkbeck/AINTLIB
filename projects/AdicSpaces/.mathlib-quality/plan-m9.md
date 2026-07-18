# M9 plan — [FJP] Cor 5.5 (strong sheafiness) + Cor 6.1 (the A_d family)

Owner-approved scope (2026-07-18): FULL M9 = M9a → M9b → M9c. Pre-plan audit:
`plan-m9-preplan.md`. Sources: fjp.txt §4 (564-980), §5 (1133-1400), §6 (1440-1490).

## Goal statements (Lean, target forms)

* `IsStronglySheafy (A) … : Prop := ∀ k, IsSheafy (restrictedTateExtension k A)` —
  mirror of `IsStronglyNoetherian` (RestrictedPowerSeries.lean:238).
* `FiniteJet.finiteJet_isStronglySheafy : IsStronglySheafy (JetA F)` ([FJP] Cor 5.5).
* `FiniteJet.JetA_d F d` (d ≥ 2) with the five Cor 6.1 claims + the chart
  `(chartDatum_d).presheafValue ≃+* JetB_d` ([FJP] (6.3)).

## Architecture

**M9a — the abstract machine** (new folder `FJP/Milnor/`, module `«Adic spaces».FJP.Milnor.*`):

* `StrictMilnorSquare.lean`: structure `StrictMilnorSquare k` over a complete
  nonarchimedean `NontriviallyNormedField k`, bundling the paper's §4 interface:
  four complete ultrametric normed `k`-algebras R, B, C, D; bounded square maps
  jB, iC, ρB, ρC with ρB∘jB = ρC∘iC; (4.1) the κ-lifting of the strict surjection
  C → D; (4.2) the ρ-pullback bound for R → B ×_D C (bijectivity onto compatible
  pairs + norm recovery); vertex finiteness data = exactly what the d=2 §4 proofs
  consumed (T30x outputs): `IsNoetherianRing` of the three vertex pods
  `GraphKoszul.P E m`, noetherian unit-ball pods, and strong noetherianity of B, C, D.
  Source: fjp.txt:571-585 ("A strict Milnor square will mean … the equivalent norm
  constants κ, ρ ≥ 1: (4.1) … (4.2)"); vertex condition "assume B, C, D are affinoid
  k-algebras" (Prop 4.5, fjp.txt:911).
* `Localization.lean` (Prop 4.5 abstract): port of FiniteJetStrictLocalization's
  (4.12)-(4.16) chase — parameterized by `(S : StrictMilnorSquare k) (m g f)`.
  The existing proofs are already written "parameter-free" in the datum; the port
  replaces the four concrete rings by S's fields. Output:
  `S.localize α : StrictMilnorSquare k` (the localized square, (4.19)-(4.20)) with
  constants tracked.
* `Naturality.lean` (Lemma 4.6/5.1 abstract): the (4.21) Banach-quotient
  identifications `Eα ≅ PE/IE` and their naturality under refinement — port of the
  graph-bridge layer (T60x) with the concrete jB/iC/ρ-maps replaced by S's.
* `Transfer.lean` (Lemma 5.2 abstract): "If B, C, D sheafy then R sheafy" — port of
  T70x (separation / gluing / embedding) over S. Source: fjp.txt:1190-1200.
* `TateExtension.lean` (Lemma 4.1): `S.tateExtend n : StrictMilnorSquare k` with the
  same constants — coefficientwise lifts (fjp.txt:610-635, one-paragraph proof;
  builds on the V4c restricted-Fubini/isometry vendor).
* Regression instance: `FiniteJetSquare F : StrictMilnorSquare K` + re-derivation
  `isSheafy_JetA' := (FiniteJetSquare F).isSheafy_R …` checked against the existing
  proof (the old concrete chain stays until M9-end cleanup; no statement changes to
  the five Main theorems).

**M9b — strong sheafiness** (`FJP/FiniteJetStronglySheafy.lean`):
pair package on `restrictedTateExtension k A` (Tate/Huber/T2/complete/maximal-plus/
IsRingOfIntegralElements for Tate A — Wedhorn 6.x vendor + M8's HuberLocLift give the
class discharge); `IsStronglySheafy` definition; the extended-square instance
`(FiniteJetSquare F).tateExtend n`; vertices of the extended square strongly
noetherian ("remain strongly noetherian", fjp.txt:1394 — from `IsStronglyNoetherian`'s
∀k form by reindexing k⟨W⟩⟨Z⃗ₙ⟩⟨T⃗ₘ⟩ ≅ k⟨W⟩⟨Z⃗ₙ₊ₘ⟩, the V4c flatten vendor);
`finiteJet_isStronglySheafy` via M9a Transfer.

**M9c — the A_d family** (`FJP/JetTruncated.lean` + `FJP/FiniteJetFamily*.lean`):
truncated jet algebra `TruncatedJet d R := Fin d → R` with truncated-convolution ring
structure + sup norm (generalizes JetDualNumberNorm; `TruncatedJet 2 R ≅ DualNumber R`);
the four rings B_d/C_d/D_d/A_d + support description (6.2); uniform Tate domain
(support monoid S_d, "exactly as in Lemma 2.2", fjp.txt:1448-1455); non-noetherian
(K_d·J_d = Q^{d+1}C_d, J_d/K_dJ_d ≅ k⟨W,W⁻¹⟩, fjp.txt:1475-1489); d-chart (6.3) by
the §3 density pattern (ϖⁿXⁿ-collapse of Q^d·C_d + lower-jet projection + power-bounded
X, Q reverse, fjp.txt:1456-1471); `not_isStablyUniform` via λQ^{d-1} square-zero
(2d−2 ≥ d); square instance `FiniteJetSquare_d F d : StrictMilnorSquare K`; sheafiness
+ strong sheafiness from M9a/M9b machinery. Assembly `finiteJetFamily_*` (five claims
+ (6.3)).

## Milestone/ticketing discipline

M9a is ticketed in detail now (T1001+). M9b/M9c open with their own /develop pass when
M9a lands (established M-milestone pattern). Cleanup cadence per file as always;
CLEANUP-M9-* to the fleet.

## Mathlib inventory (key checks done)

* `TrivSqZeroExt`/`DualNumber` — d=2 only; no truncated-polynomial normed algebra in
  mathlib → `TruncatedJet` is a genuine new def (M9c).
* Restricted multivariate power series + Fubini/isometry/flatten — project vendor
  (V4c) ✓; `restrictedMvPowerSeriesSubring` ✓; `IsStronglyNoetherian` ✓.
* `isSheafy_of_stronglyNoetherian_828b` ✓ generic (Huber's theorem for the vertices).
* M8's `hasLocLiftPowerBounded_huber` + new `IsSheafy` signature ✓ (the pair package
  on extensions must supply the complete-affinoid bundle).
