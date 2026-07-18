# Reply integration — 2026-07-05

Reply received from the external reviewer (senior arithmetic geometer) on 2026-07-05,
forwarded by the project owner; owner approved application of all proposed changes
("yes apply them") after the composability question (see below) was answered.

Brief: `./brief.md` · Reply: `./reply.md` (verbatim).

## Interpretation summary

| # | Reviewer point | Maps to | Type | Applied as |
|---|---|---|---|---|
| 1 | Cartier-incidence representability block (11 tickets) | plan-level | structural addition | `LevelStructure/Incidence.lean` + stream D0 (T-D11–T-D21) |
| 2 | Group law into the record; Abel later | Q1/Q3 | direct answer, reverses D-nobundle | Two-record design (D5); DS2 deleted; `abelEnrichment_*` |
| 3 | Bridge fibre condition as scheme iso; geometric-genus eventual | Q1/Q2 | direct answer | `FibrewiseElliptic` restated via pointed iso with `projModel` |
| 4 | Pinning specs need base-change/naturality; V_ρ via Galois equivalence | Q4 | correction | Register rule amended; DS4/DS5 spec rows extended; T-C2a |
| 5 | Pairing: duality API, norm/divisor backend, char-0 étale first, `N∣M` | Q5 | direct answer | D7; T-C0/T-C1 re-cut; `weilPairingEval_mul` |
| 6 | Silverman normalisation; symplectic + equivariance pins | Q6 | direct answer | D7; `weilPairingEval_symplectic`; T-C4 note |
| 7 | Groupoid-valued internally; set-valued after rigidification | Q7 | strengthening | `Moduli/Groupoid.lean` (D6); T-G1–T-G3 |
| 8 | Integral-statement priority; N-Isog/cyclicity/quotients explicit | Q8 | direct answer | Phase-2 named blocks; streams SG + Q |
| 9 | Y(ρ̄,p) directly as symplectic Isom problem; twist afterwards | Q9 | route change | D8; `rhoLevel_relativelyRepresentable` (T-F6); T-F4 re-routed |
| 10 | fppf cyclicity before any Γ₀ theorem | §7.4 | requirement | T-SG2 gate recorded on the board |
| 11 | Finite-quotient workstream split ×7 | AG-QUOT | expansion | Stream Q (T-Q1–T-Q7) |
| 12 | Do-not-formalize-from-memory: KM 2.3/2.8/4.7/5–7/8–10/12–13 | §7.5 | policy | Binding gate in plan.md + tickets.md |
| 13 | Revised spine A–N | plan | restructure | Adopted in plan.md |
| — | (No unanswered questions: all Q1–Q9 addressed) | | | |

## Changes applied (code — all `lake build`-green, 3295 jobs)

- `EllipticCurve/Basic.lean`: `EllipticCurveGeom` (geometry-only record);
  `FibrewiseElliptic` via pointed scheme isomorphism.
- `EllipticCurve/GroupLaw.lean`: `EllipticCurve extends EllipticCurveGeom` with
  `grp`/`comm`/`one_eq_zero`; **real** `pointEquivOverHom` + `pointAddCommGroup` +
  `Point.restrict` + `Point.asSection`; base change with **real** group data
  (`Over.grpObjMkPullbackSnd`); `abelEnrichment_exists/unique` (deferred project).
- `LevelStructure/Incidence.lean` (new): `sectionVanishingIdeal` (+spec),
  `RelEffCartierDiv.baseChange` (real, via `Scheme.Hom.ker`), `IsSubdivisor`,
  `exists_incidenceLocusLE/EQ`, `exists_subgroupLocus`, `exists_exactOrderLocus`,
  `exists_fullLevelLocus`.
- `Moduli/Groupoid.lean` (new): category of elliptic curves over `S` (pointed
  `S`-morphisms), `isIso_homOver`, `IsoClasses`, `aut_trivial_of_fullLevel`.
- `WeilPairing/Basic.lean`: `weilPairingEval_restrict` (naturality),
  `weilPairingEval_mul` (`N∣M`), `weilPairingEval_symplectic` (convention pin).
- `ModularCurve/YRho.lean`: `rhoLevel_relativelyRepresentable` (T-F6, Isom^symp).
- Root import list extended.

## Changes applied (docs)

- `plan.md`: D5–D8; DS2 removed; register rule + DS4/DS5 specs strengthened;
  amendments section; revised spine A–N; source gate; composability note.
- `tickets.md` v2: T-A6 → canonicity project (dependency un-wiring), T-C0/T-C1/T-F6
  cuts, streams D0/SG/Q/G (24 new tickets), cadence recount (49 work + 17 cleanups),
  start-now set of 8.

## Changes rejected by user

None.

## Decisions recorded but not actioned in code

- Geometric-genus fibre condition as eventual statement of record: waits on AG-COH
  (T-A9), as the reviewer allowed.
- `(L, s)`-interface for divisors (T-D19): blocked on AG-LB, as the reviewer's list
  anticipated.
- Formal pseudofunctor/stack packaging stays T-E8 (reviewer: current packaging
  "honest for the first target" with the groupoid strengthening — applied).

## Owner's follow-up question (answered in-session, recorded in plan.md)

*"Will we be able to get full level N stacks and then any other representable level
from these constructions … without redoing lots of things?"* — Yes: the incidence/
A-structure engine is uniform in the level datum; the groupoid-valued problem is the
stack for every `N` (including the genuinely stacky `N ≤ 2` / level 1 / `Γ₀` cases)
with `Y(N)` (`N ≥ 3`) as presentations; other `H`-levels come via the Q-stream. The
two shortcut-risks that would have forced rework (set-valued-everywhere; naive
fibrewise level definitions) are exactly what D6 + the Drinfeld definitions exclude.
Deferred-not-redone: coarse moduli, char `p ∣ N`, compactification, DM-stack
packaging.
