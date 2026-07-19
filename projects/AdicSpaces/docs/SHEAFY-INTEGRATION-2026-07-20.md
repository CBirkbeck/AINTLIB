# Sheafy integration campaign — final audit & handover (2026-07-20)

Branch `dev/adic-spaces`, WO0–WO6 on top of `f88fd95e9`. Every axiom column below was
verified by `#print axioms` this session (scratchpad `wo6_axioms.lean`); "clean" means
exactly `[propext, Classical.choice, Quot.sound]`. Source anchors were verified
verbatim against `references/wedhorn.txt`, `references/huber1994.txt`, and the
Kedlaya AWS 2017 notes (extracted this session).

## The headline question (WO6 item 6)

> **Does `IsSheafyTateRing A` now imply that the actual public structure presheaf is
> a sheaf of topological rings with the projective topology intended by the
> sources?**

**Yes — for every completion model and every ring of integral elements of it, by the
following named chain** (each step a Lean theorem, no prose steps):

1. `IsSheafyTateRing A` *(def, `SheafyRing.lean`)* unfolds to: for every pair of
   definition `P` and every `Bplus : RingOfIntegralElements (CompletionModel A P)`,
   `IsSheafyFor (CompletionModel A P) Bplus`.
2. `IsSheafyFor B Bplus` *(def)* is `IsLimitSheaf B` at the pair — separation,
   gluing, and the arbitrary-open-cover topological-embedding condition for
   `limitSections`, the projective-limit presheaf with the **initial topology for
   the rational evaluations** (`limitSections_topology_isInducing`,
   `StructurePresheafLimit.lean` — the projective topology of Wedhorn §8.1 /
   Kedlaya Definition 1.2.3).
3. `isSheafOfTopologicalRings_iff_isLimitSheaf` *(`StructurePresheafBundled.lean`)*:
   `IsLimitSheaf B` is equivalent to **Wedhorn Remark 8.20's own formulation** —
   for *every* topological commutative ring `T`, `V ↦ Hom_cont(T, 𝒪_X(V))` is a
   sheaf of sets.
4. `structurePresheaf_isSheaf` *(`StructurePresheafBundled.lean`)*: `IsLimitSheaf B`
   makes the **bundled public structure presheaf** `structurePresheaf B :
   Presheaf CompleteTopCommRingCat (SpaTop B)` (objects = `limitSections V` with the
   projective-limit topology, coherent category, restriction = `limitRestrict`)
   satisfy mathlib's categorical sheaf condition ([Stacks 00VR] `Hom(E,−)`-by-`E`).
5. On rational opens the presheaf's value is `A⟨T/s⟩` with its canonical topology:
   `structurePresheaf_rational_value` / `limitEval` (+ `limitEval_continuous`,
   `limitEval_symm_continuous`) — Wedhorn (8.1.1). No discrete topology appears on
   any path (the discrete locally-fraction object is quarantined as
   `locallyFractionPresheaf` with no sheaf claim and no public consumer).

Instantiation for the strongly noetherian theorem:
`isSheafyTateRing_of_stronglyNoetherian_completion` (noncomplete `A`, Definition
6.36's hypothesis verbatim) / `isSheafyTateRing_of_stronglyNoetherianTate`
(complete case) feed step 1; steps 2–5 are unconditional bridges.

## Audit table

Scope column: **pair** = fixed `(A, A⁺)`; **cTate** = complete Tate ring;
**Tate** = general (possibly noncomplete) Tate ring; **f-adic** = general f-adic —
*no declaration claims f-adic scope* (see "honest boundaries").

| Declaration | Meaning | Source | Key hypotheses | Axioms | Scope |
|---|---|---|---|---|---|
| `structurePresheaf A` | the public structure presheaf: `V ↦ lim_{R(T/s)⊆V} A⟨T/s⟩`, projective topology, coherent bundled category | Wedhorn §8.1; Kedlaya Def 1.2.3 | Huber + `A⁺` + restriction-map package | clean | pair |
| `IsSheafOfTopologicalRings A` | ∀ topological comm. ring `T`, `Hom_cont(T, 𝒪_X(−))` a sheaf of sets | Wedhorn Rem 8.20 (first form) | as above | (def) | pair |
| `isSheafOfTopologicalRings_iff_isLimitSheaf` | Rem 8.20: representable ⟺ ring-sheaf + cover-product embedding | Wedhorn Rem 8.20 | as above | clean | pair |
| `structurePresheaf_isSheaf` | `IsLimitSheaf → (structurePresheaf A).IsSheaf` (categorical) | [Stacks 00VR]; Rem 8.20 | `IsLimitSheaf A` | clean | pair |
| `structureSheaf A` | the sheaf object | Wedhorn Def 8.21 | complete Tate pair + `IsSheafy` | clean | cTate pair |
| `AffinoidAdicSpace` (+ `.sheaf`) | Def 8.21 with the **faithful field** `sheafy : IsLimitSheaf Ring`; sorry-free sheaf | Wedhorn Def 8.21 | structure fields | clean (no `sorryAx`) | pair |
| `IsLimitSheaf.injective'/.glue'/.isEmbedding'` | cover-index universe reduction (any `ι : Type v`) | elementary | — | clean | pair |
| `IsSheafyFor A Aplus` | pair-level sheafiness, bundled valid pair, genuine presheaf | Wedhorn Def 8.26 (one pair); Kedlaya Def 1.2.8 | complete Tate | (def) | cTate pair |
| `IsSheafyComplete A` | ∀ valid `A⁺`: sheafy pair | Wedhorn Def 8.26 (complete case) | complete Tate | (def) | cTate |
| `IsSheafyTateRing A` | Def 8.26 over every completion model | Wedhorn Def 8.26 (Tate case) | Tate | (def) | Tate |
| `standardSheafCondition_of_isSheafyFor` | **single pair ⟹ `A⁺`-free standard condition** | Kedlaya Rem 1.6.9 (mechanism) | complete Tate, one valid pair | clean | cTate |
| `IsEmbedding.of_comp_isEmbedding` | factorization principle | elementary topology (not from the sources) | — | clean | — |
| `HasStandardRefinements` | **named descent input** = conclusion of Kedlaya Lem 1.6.8 / Wedhorn Lem 7.54 / Huber [Hu3] 2.6 | ibid. | — | (def) | cTate pair |
| `isSheafy_of_standardSheafCondition_at` | standard condition + descent input ⟹ both sheaf axioms for **every** rational covering | Kedlaya Lem 1.6.8 ⟹; Čech refinement | complete Tate, valid pair | clean | cTate pair |
| `isSheafyFor_congr` | **genuine `A⁺`-independence**, conditional on the descent input at each pair; via the `A⁺`-free middle term, *not* `iff_of_true`, *no* noetherianness | Kedlaya Rem 1.6.9 | descent inputs | clean | cTate |
| `isSheafyFor_iff_standardSheafCondition` | all-rational ⟺ standard-cover condition (conditional) | Kedlaya Lem 1.6.8/Rem 1.6.9 | descent input | clean | cTate |
| `isSheafyFor_iff_isSheafyComplete` | one pair ⟺ all pairs (conditional) | Kedlaya Rem 1.6.9 | descent inputs (all pairs) | clean | cTate |
| `completionModelCompare` (+ `_continuous`, `_symm_continuous`, `_canonicalMap`) | any two completion models are compatibly equivalent topological rings, intertwining the maps from `A` | Wedhorn Rem 8.3 | analytic scope (restriction maps) | clean | Tate |
| `completionModel_isStronglyNoetherian` | `A` strongly noeth. (complete) ⟹ model strongly noeth. | Wedhorn Ex 6.38 / p. 56 | complete analytic + strongly noeth. | clean | cTate |
| `isSheafyTateRing_of_stronglyNoetherian_completion` | **the noncomplete wrapper**: completion strongly noetherian (Def 6.36 verbatim, ∀-model form) ⟹ `IsSheafyTateRing A`; **no** `CompleteSpace A`/`PlusSubring A`/`IsNoetherianRing A`/`HasLocLiftPowerBounded A` | Wedhorn Thm 8.28(b) + Def 6.36(i) | Tate + Def 6.36 for the models | clean | Tate |
| `isSheafyTateRing_of_stronglyNoetherianTate` | complete case instantiation | Wedhorn Thm 8.28(b) | complete strongly noeth. Tate (+ current transport scope) | clean | cTate |
| `finiteJet_isSheafyFor` | FJP pair-level sheafiness, public vocabulary | [FJP] Thm 1.3 + bridges | — | clean | cTate pair |
| `finiteJet_isSheafOfTopologicalRings` | FJP presheaf is a sheaf of topological rings (Rem 8.20 form) | [FJP] Thm 1.3 + Rem 8.20 | — | clean | cTate pair |
| `finiteJet_structurePresheaf_isSheaf` / `finiteJet_structureSheaf` | categorical sheaf property / the object | [FJP] Thm 1.3 + [00VR] | — | clean | cTate pair |
| `finiteJet_standardSheafCondition` | the `A⁺`-free standard condition for `𝓐`, **unconditional** — and *not* reachable via noetherianness (`𝓐` non-noetherian) | Kedlaya Rem 1.6.9 mechanism | — | clean | cTate |
| `finiteJet_isSheafyComplete_of_hasStandardRefinements` | all-pairs sheafiness for `𝓐`, conditional on the descent inputs | Kedlaya Lem 1.6.8 | descent inputs | clean | cTate |
| *(regression)* 5 FJP headliners, `isLimitSheaf_of_isSheafy`, `isSheafy_of_isLimitSheaf`, `isSheafy_iff_isLimitSheaf`, `isSheafy_of_stronglyNoetherian_828b` | frozen | — | unchanged | clean | — |

## Honest boundaries (exact blocked declarations)

1. **The descent input** (`HasStandardRefinements`, = Kedlaya Lemma 1.6.8's
   conclusion) is a *hypothesis*, not a theorem, because two named pieces are
   missing:
   * a noetherian-free bridge `CompleteSpace A → IsAdicComplete P.I P.A₀` (the
     completeness input of Wedhorn Cor 7.53 / Prop 7.51 — the project's proven
     forms consume `[IsAdicComplete P.I P.A₀]`, currently discharged only by
     `principalPair_isAdicComplete_of_stronglyNoetherianTate`), needed for the
     whole-space case (`span S = ⊤` from no-common-zero); and
   * a noetherian-free `relativePiece_equiv` (Wedhorn Prop 8.16 / Lemma 2.13
     ring-level keystone), needed for coverings of a general rational base
     (Kedlaya's "every rational subspace of `X` is itself the spectrum of a Huber
     pair" re-basing).
   The generation side of 1.6.8 is fully proved (`StandardRefinement.lean`); the
   engine consuming the input is fully proved (`StandardDescent.lean`).
2. **General f-adic `IsSheafyRing`** is *not defined*: the non-analytic structure
   presheaf (restriction maps beyond the 7.52(2) analytic route) is missing
   infrastructure, and Kedlaya Remark 1.6.10 records that the non-analytic case
   genuinely differs. The Tate-scoped notion is honestly named `IsSheafyTateRing`.
3. **Model-transport of `IsSheafyFor` along `completionModelCompare`** (hence the
   `∃P ↔ ∀P` collapse for `IsSheafyTateRing`, and `IsSheafyTateRing A ↔
   IsSheafyComplete A` for complete `A` via the Remark 8.3 comparison): needs the
   `IsLimitSheaf` transport along compatible topological-ring equivalences — the
   compatible equivalence itself is delivered (`completionModelCompare` + its three
   compatibility theorems).
4. **The `A`-level noncomplete strong-noetherian transport**
   (`IsStronglyNoetherian A → IsStronglyNoetherian (CompletionModel A P)` without
   `CompleteSpace A`): open; the delivered wrapper instead takes Wedhorn Definition
   6.36's hypothesis verbatim (a condition on `Â`), which is the literature's own
   hypothesis shape and requires nothing of noncomplete `A`.
5. `completionModelCompare_canonicalMap` carries `[IsNoetherianRing A] [T2Space A]
   [NonarchimedeanRing A]` inherited from the current section scope of
   `restrictionMapHom_canonicalMap` — no mathematical content; a cleanup candidate.
