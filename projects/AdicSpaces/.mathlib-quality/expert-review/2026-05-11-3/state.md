# Expert-review session state

- Generated: 2026-05-11T15:26:00Z
- Audience: ChatGPT Pro (continuing series, session 3)
- Goal of brief: Combined — strategy + soundness + refs. Strategic guidance on the
  T-FLAT-PER-E architectural decision (Route A refactor vs. Route B iterated 2.13),
  soundness check on the new flatness route, and reference recommendation for iterated
  Wedhorn 2.13 if Route B is preferred.
- Scope: Tate acyclicity formalization, specifically the per-E flatness blocker and the
  topological inducing piece of `IsSheafy`.
- Reply received: true (date: 2026-05-11)
- Reply integrated: true (date: 2026-05-11)
- Reviewer: ChatGPT Pro

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Architectural decision for `T-FLAT-PER-E`. The choice between Route A (refactor the per-E covering to use direct E-shape Laurent decompositions) and Route B (build the iterated Wedhorn 2.13 identification at intermediate cover pieces). Which would you recommend, weighing (a) lines of Lean code, (b) mathematical naturalness vs. one-off formalization, (c) reusability of the resulting infrastructure elsewhere in the project? |
| Q2 | Soundness check on Theorem 5.4 / 5.5. Are the B-level canonical-topology hypotheses (continuity of the canonical evaluation map, locale Noetherianity, power-boundedness of T-elements) the right ones for the strongly noetherian Tate setting? Is the `IsNoetherianRing (locSubring ...)` hypothesis genuinely needed, or should it follow from `IsNoetherianRing A` and standard preservation results? |
| Q3 | Power-boundedness on the plus side. Theorem 5.5 (plus-side flatness) requires an explicit `IsPowerBounded (D₀.canonicalMap f)` hypothesis. The minus side doesn't need this. Is the asymmetry mathematically correct, or have we missed a duality that lets the plus side discharge `hT_pb` automatically? |
| Q4 | Reference for iterated Wedhorn 2.13. If Route B is recommended, what is the cleanest published source for the iterated Wedhorn 2.13 identification at depth ≥ 2? Hübner's notes? Bosch? Stacks? Or is the right reference simply "iterate Wedhorn 2.13"? |
| Q5 | Topological side of `IsSheafy` (T-EMBED-TOPO). What's the right toolbox for `Topology.IsInducing` of the product restriction in the strongly noetherian Tate setting (Pettis and non-arch Banach were ruled out in session 2)? Is it Example 6.38 (quotient topology) + Lemma 8.33 (strictness), or a different route? Likely formalizable by a single argument or does it break across cover pieces? |
| Q6 | Critical-path sanity check. After Route A or B closes T-FLAT-PER-E and T-EMBED-TOPO is in place, are there other blockers we haven't identified? Especially: hidden hypotheses in the geometric reduction (Wedhorn 8.34 / Hübner 3.8) that we've under-stated in `hZavyalov_per_E`? |

## Ticket-board snapshot at brief time

DONE this session (post session-2 reframe):
- T-RETIRE-PROP815: annotated misframed `restrictionMap_isLocalization`.
- T-FLAT-VIA-WEDHORN830: `restrictionMap_flat_via_iteratedMinus` (Wedhorn 8.30 + 2.13).
- T-FLAT-PLUS: `restrictionMap_flat_via_iteratedPlus` analog.
- T-COR832-VIA-FLAT: `flat_over_base_tate_laurent` (per session-2 prescription).
- T-COR832-FF-LAURENT: `productRestriction_faithfullyFlat_tate_laurent_of_hSpa_points`.
- T-FLAT-COMBINED: `flat_over_base_tate_laurent_combined` (plus+minus disjunctive).
- T-FF-COMBINED: combined plus+minus FF combinator.
- T-FF-LAURENT-AT-E: FF product over E.1 for `laurentCovering E.1 f` (direct E-shape).
- T-NEW-4: `tateAcyclicityComplete` wrapper (Part 1 + Part 2 abstract suppliers).
- T-NEW-5: `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing` wrapper.

OPEN:
- T-FLAT-PER-E: per-E flatness for the existing `per_E_local_covering` whose pieces are
  iterated `laurent±Datum (C.plusDatum f) f₀` shapes. THE structural blocker.
- T-EMBED-TOPO: topological inducing for product restriction. Open since session 2;
  reviewer ruled out Pettis / non-arch Banach routes.
- T-MATHLIB-COMPLETEDLOC: optional Mathlib contribution. Decoupled.

## Stuck points (from §8 of brief)

1. The per-E shape mismatch: assembly hard-codes iterated `laurent±Datum (C.plusDatum f) f₀`
   pieces, but the new flatness route gives flatness for direct Laurent shapes of the base.
   Faithful descent doesn't apply (intermediate map is not faithfully flat).
2. The topological side of `IsSheafy`: product topology should pull back to base topology.
   Mathematical content is Example 6.38 + Lemma 8.33 strictness, but formalization
   unattempted.

## Reference list (from §2.2 of brief)

- [Wedhorn 2019] arXiv:1910.05934. §8 for acyclicity, §6.38 for the Tate-algebra
  identification, §2.13 for iterated rational localization.
- [Huber 1996] Étale Cohomology of Rigid Analytic Varieties and Adic Spaces.
- [Bosch 2014] Formal and Rigid Geometry. LNM 2105.
- [BGR 1984] Non-Archimedean Analysis. Grundlehren 261.
- [Hübner 2021] The adic tame site. Doc. Math. 26, 873-945. §3 for rational coverings.
- [Zavyalov 2024] Notes on adic geometry. §2.3 Nullstellensatz refinement.
- [Stacks] Tags 00MA, 00HQ, 023N (faithful descent), 04UE.
- [Mathlib4] `RingTheory.Flat.*`, `RingTheory.AdicCompletion.*`,
  `Topology.UniformSpace.Completion`.

## Cross-references to prior briefs

- `.mathlib-quality/expert-review/2026-05-11/` — first brief (overall strategy). Reviewer
  confirmed: Lane B parked, Lane A approach (a), Lane C direct per-E architecture, Wedhorn
  Prop 8.15 as critical residual.
- `.mathlib-quality/expert-review/2026-05-11-2/` — second brief (the Wedhorn 8.15
  reframe). Reviewer (ChatGPT Pro) issued the MAJOR REFRAME: refactor Cor 8.32 to consume
  `Module.Flat` directly, discharge flatness via Wedhorn 8.30 + Lemma 2.13. Retired:
  Pettis, non-arch Banach, naïve `(R[1/x])^∧ ≅ R̂[1/x]`. The work described in this
  brief executes that reframe prescription.
- This (round 3) brief asks the next architectural question that the reframe surfaced:
  *which closure path for T-FLAT-PER-E now that the algebraic infrastructure is in place?*
