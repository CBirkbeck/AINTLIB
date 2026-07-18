# PROJECT OVERVIEW — Y₁(N) chain, ModularCurves (Phase-2 consolidation analysis)

**Scope**: the 20 files of the Y₁(N) chain on `main`, as inventoried by the eight Phase-1
documents in this directory (`YOneAtlasClassify.md`, `YOneHeadline.md`,
`Incidence-IsoTransport.md`, `CartierDivisor.md`, `LevelStructure-Core.md`,
`GroupLaw-Cluster.md`, `AdditionSpecPoints.md`, `NaiveProblems.md`).
**Date**: 2026-07-12, branch `main` @ `c5c15a80f`.
**Ground rules honored throughout**: (a) the 16 code-sorry carriers and their tainted closures
are UNTOUCHABLE (§2); (b) statements of public declarations stay **byte-identical** under every
proposed action — anything that would change a public signature is flagged
`statement-touching (FORBIDDEN in cleanup lanes)` and routed to the coordinator/generalise lane;
(c) **no docstring is ever deleted** — stale ones are REFRESHED (§5).
Every claim below cites its Phase-1 inventory entry and/or the source line verified during this
pass; items that could not be verified are marked **UNVERIFIED**.

---

## 1. Executive summary

The Y₁(N) chain is a **complete, axiom-clean headline** (the T-E7 MASTER
`gammaOneNaive_representable`, `YOneTatePoint.lean:1404`, audits at
`{propext, Classical.choice, Quot.sound}` per its header) sitting on ~21k lines of
producer-fresh proof text. The mathematics is done for the Γ₁ stream; the *presentation* debt
is now the dominant cost, and it is concentrated in five shapes:

1. **Relocation-era relics.** The v10.111/v10.117 relocations (Representability →
   NaiveProblems → YOneTatePoint) left a triple byte-identical MASTER statement
   (`_assembly`/`_closure`/master, one of which — `_closure` — has **zero consumers
   project-wide**), ~11 stale docstrings still describing sorries that are long since proven,
   and pointer prose to a `Moduli/Representability.lean:250` that no longer exists (file is
   206 lines).
2. **Dead scaffolding.** 23 zero-consumer declarations (verified repo-wide by grep: 13 public,
   10 private) plus **three git-tracked editor artifacts**
   (`TorsionUnramifiedFibre.lean.full`/`.tail2`/`.tailbody`, ~96 KB) that should be `git rm`'d.
3. **Provable duplication.** One project lemma (`Scheme.Hom.ker_iso_comp`) is
   **statement-identical to mathlib's `Scheme.Hom.ker_comp_of_isIso`** (verified at the local
   pin); one private helper (`Proj_map_congr`) is byte-identical in two files; one private
   re-derives a `private` ForMathlib lemma it cannot import; a ~90-line proof is duplicated
   near-verbatim inside `Incidence.lean`; and the `sectionsDivisor` `dif_pos` unfolding is
   copy-pasted at three external sites for want of one public `sectionsDivisor_ideal` lemma.
4. **Monolithic proofs.** 103 proofs exceed 30 lines (per the eight inventories); the top of
   the list (`exists_tateAlgLift_core` 305, `yOne_infinitesimal_lifting` 280,
   `pointSharp_add` 254, `kerPrincipalAux_nzd` 227, `sectionsIdealAux_exists_chart` 220) are
   sorry-free and decomposable along seams the inventories already name. One atlas proof
   contains machine-generated source lines up to **3,780 characters** (verified:
   `YOneAtlasClassify.lean:4257`).
5. **A real upstream surface.** ~10 genuinely mathlib-shaped declarations (generic ideal-sheaf
   transport, a clopen agreement-locus file, `Proj` congruence lemmas, a reduced-ring
   separation fact) verified absent from current mathlib by loogle/local search.

**Statistics** (from the eight Phase-1 inventories; line counts re-verified on disk):

| Metric | Value |
| --- | --- |
| Files / lines | 20 files, **21,263 lines** (largest: YOneAtlasClassify 5,905; Incidence 2,753; CartierDivisor 2,964) |
| Declarations | **935** (per-file inventory totals: 298 + 144 + 81 + 68 + 64 + 58 + 51 + 33 + 30 + 20 + 20 + 19 + 12 + 11 + 8 + 5 + 5 + 4 + 3 + 1) |
| Private / public | ~252 / ~683 |
| Code-sorry carriers | **16**, in 6 files (14 of 20 files are code-sorry-free) |
| Explicit tainted closure | 5 decls (CartierDivisor) + import-level tainted chains noted in §2 |
| Proofs > 30 lines | **103** (Atlas 25, CartierDivisor 17, Incidence 13, AdditionSpecPoints 13, GroupLawAxioms 12, YOneTatePoint 8, TorsionUnramifiedFibre 5, GroupLaw 3, others ≤ 2) |
| `set_option` overrides | **0** across all 20 files |
| Missing copyright headers | **13 of 20 files** (§5.13) |
| Dead declarations | 23 (13 public, 10 private) + 3 stray artifact files |
| Doc refresh items | 12 clusters (§5) |

---

## 2. Untouchable surface

The 16 **code-sorry carriers** (actual `sorry` terms; prose mentions do not count — each
verified by the Phase-1 grep discipline). NOTHING below may be edited, golfed, decomposed,
or "fixed" by cleanup lanes; if one blocks an action, the action is deferred or re-scoped.

**`LevelStructure/Basic.lean`** (2) — [LevelStructure-Core.md §1]
1. `ModularCurves.EllipticCurve.fullLevel_divisor_iff_naive_gen` (T-D8-bridge, line 125)
2. `ModularCurves.EllipticCurve.isGammaZero_iff_fppf` (T-D10, line 197)

**`LevelStructure/ExactOrder.lean`** (4) — [LevelStructure-Core.md §2]
3. `ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (BB-DELIGNE, line 115; discharge stream live in `GroupScheme/DeligneOrder.lean`)
4. `ModularCurves.EllipticCurve.Section.HasExactOrder.pull_nsmul_ne_zero` (T-D6b, line 278)
5. `ModularCurves.EllipticCurve.Section.hasExactOrder_of_geometric` (T-D6c, line 290)
6. `ModularCurves.EllipticCurve.Section.orderDivisor_etale_iff_geometric` (T-D7-bridge, line 321)

**`EllipticCurve/Torsion.lean`** (3) — [LevelStructure-Core.md §4]
7. `ModularCurves.EllipticCurve.mulByHom_locallyQuasiFinite` (BB-QF, line 141)
8. `ModularCurves.EllipticCurve.mulByHom_flat` (BB-FLAT, line 147)
9. `ModularCurves.EllipticCurve.mulByHom_finrank` (BB-DEG, line 153)

**`LevelStructure/CartierDivisor.lean`** (3) — [CartierDivisor.md #59/#69/#73]
10. `ModularCurves.RelEffCartierDiv.sliceAux_exists_noetherianStage` (private, line 1979 — Noetherian approximation, Stacks 07RF)
11. `ModularCurves.RelEffCartierDiv.officialAux_exists_finite_chart` (private, line 2567 — KM 1.2.3 fibre isolation)
12. `ModularCurves.IsOfficialCartier.isFinite` (public, line 2742 — KM 1.2.3 (⇒) via ZMT)

**`EllipticCurve/GroupLaw.lean`** (2) — [GroupLaw-Cluster.md §1]
13. `ModularCurves.EllipticCurve.abelEnrichment_exists` (T-A6b, line 76)
14. `ModularCurves.EllipticCurve.abelEnrichment_unique` (T-A6c, line 81)

**`Moduli/NaiveProblems.lean`** (2) — [NaiveProblems.md #7/#9]
15. `ModularCurves.gammaFullNaiveProblem` (`sorry` term at line 211, inside the `map` field — the `IsNaiveFullLevel` membership transport)
16. `ModularCurves.gammaFullNaive_representable` (T-E9, `by sorry` at line 239)

**Explicit sorry-tainted closure — also untouchable** (sorry-free proofs *depending on* the
carriers; CartierDivisor.md File Summary):
- `ModularCurves.nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (#60, tainted via #59)
- `ModularCurves.RelEffCartierDiv.officialAux_away_nzd` (#67)
- `ModularCurves.RelEffCartierDiv.officialAux_exists_away_span` (#68)
- `ModularCurves.RelEffCartierDiv.isOfficial` (#70)
- `ModularCurves.IsOfficialCartier.toRelEffCartierDiv` (#74)

**Import-level tainted chains (treat as untouchable for any semantic action; noted where they
block a recommendation):**
- In `ExactOrder.lean`: the T-D6/T-D7 headline equivalences `hasExactOrder_iff_geometric` /
  `hasExactOrder_iff_etale` consume carriers 4–6 [LevelStructure-Core.md §2 notes].
- The `torsionπ_isFinite` chain (Torsion.lean:165 uses `mulByHom_isFinite` ← carriers 7–9):
  everything downstream of the *unprimed* finiteness — in particular
  `formallyUnramified_torsionπ_of_nIsInvertible` (TorsionUnramifiedFibre:1434) and the
  unprimed `torsionπ_etale`/`mulBy_etale` family — inherits BB-QF
  [GroupLaw-Cluster.md §7 notes; verified at Torsion.lean:165–167]. The primed
  `MulByHomEtale.lean` family is the clean-axiom route and is NOT tainted.

---

## 3. Moral duplications

Each candidate seeded from the inventories was verified at source. Pairwise table:

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
| --- | --- | --- | --- | --- |
| `gammaOneNaive_representable_assembly` (YOneTatePoint:1372) | `gammaOneNaive_representable_closure` (:1386) | **YES** — conclusion verified byte-identical at source (`(gammaOneNaiveProblem R N).Representable ∧ ∀ X …`) | B is `:= A` | **DELETE B** — v10.117 closure-prep relic, zero consumers project-wide [YOneHeadline.md #_closure; verified grep]. Public decl-removal ⇒ coordinator ack. |
| `gammaOneNaive_representable_assembly` (:1372) | `gammaOneNaive_representable` (:1404, THE MASTER) | **YES** (byte-identical conclusion) | master is `:= assembly` | **KEEP BOTH** — master is the T-E7 register name (consumed by `_zInv`); assembly is the named bridge (2 consumers). One-line proofs; cost of keeping ≈ 0. Refresh both docstrings (§5.9). |
| `exists_affineOpen_mem_free` (Incidence:404) | `vanishingLocusAux_exists_basicOpen_free` (Incidence:545, private) | NO — affine-open vs basic-open-in-fixed-affine | **YES in substance** — docstring admits "Same proof, but keeping the ambient affine `U` fixed" (verified at :541–560); ~90 lines duplicated | **EXTRACT SHARED CORE** ("freeness spreads to a basic open + `Module.Free.iff_of_equiv` transport"); both statements unchanged. Proof-only. [Incidence-IsoTransport.md :394–446] |
| `formallyUnramified_torsionπ_of_nIsInvertible'` (MulByHomEtale:37) | `formallyUnramified_torsionπ_of_nIsInvertible` (TorsionUnramifiedFibre:1434) | **YES** — identical hypotheses `(N) (h : NIsInvertible S N)` and conclusion (verified side-by-side) | **YES** — line-for-line identical except one `haveI` (proven vs sorried finiteness) | Real duplicate, **dedup BLOCKED**: the unprimed is import-tainted via `torsionπ_isFinite` (BB-QF) and the split is the *designed* axiom-trail quarantine [GroupLaw-Cluster.md §5 notes]. DEFER to producer until BB-QF retires; then factor both over `[IsFinite (E.torsionπ N)]` and delete one. |
| `Proj_map_congr` (NegModelBaseChange:38, private) | `Proj_map_congr` (GroupLawConstruction:70, private) | **YES** — byte-identical statement (verified side-by-side) | **YES** — `by subst h; rfl` both | **HOIST + DELETE COPY**: NegModelBaseChange already imports GroupLawConstruction; the copy exists only because the original is `private`. Publicise in GroupLawConstruction (or move to `ForMathlib/GradedQuotient`), delete the NegModelBaseChange copy. Privates ⇒ invisible. [GroupLaw-Cluster.md §6] |
| `officialAux_finite_quotient_loc` (CartierDivisor:2382, private) | `stalkDVRAux_finite_quotient_loc` (ForMathlib/StandardSmoothStalkDVR:225, private) | Same content (localized quotient of a finite quotient is finite over a field) | Same route (Artinian + localization surjective + `Module.Finite.trans`) | **PUBLICISE the ForMathlib one, DELETE the CartierDivisor copy** — the CartierDivisor docstring itself flags "not importable because private" (verified :2385). #65 is NOT in the tainted closure (feeds #66, upstream of the taint). Producer-active file ⇒ coordinate. |
| ~14 Z/Y mirror pairs (AdditionSpecPoints: `specPoint_addOn{Z,Y}_family`, `…OnImage_factors(')`, `blOpen{Z,Y}Image_ι_eq`, `mR_isoAway_pieceAway(Z)ι`, `dictionary_{fst,snd,sum}_of_piece{Z,Y}`, `chi_compat_of_piece{Z,Y}`, `descended_law{One,Two}…`, `specPoints_arm_{Z,Y}`) | — | NO (Z = law-1 `lawOneTriple`/`addOnZ`, Y = law-2 `lawTwoTriple`/`addOnY`) | Shape-identical scaffolding; content lemmas genuinely differ (law-1 is *exactly* mathlib `add` — `descended_lawOne_eq_add`; law-2 only *up to a nonzero scalar* — `descended_lawTwo_smul_add`) | **HONEST ASSESSMENT: cross-law parametrization is NOT a cleanup action.** The two Bosma–Lenstra laws differ mathematically (exact vs up-to-scalar; different opens, triples, minor identities), and the Z/Y split originates upstream (AdditionChartGlobal/AdditionChartAway) — a "law datum" bundle is a producer-grade refactor of files outside this sweep. What IS mechanical: (i) the **8 near-verbatim index arms** inside `mulModelHom_specPoints_atlas` (2 laws × 4 members differing only in indices `1 1/1 2/2 1/2 2`) collapse to 2 via an index-generic arm helper [AdditionSpecPoints.md ★ atlas keystone]; (ii) the dead unprimed `factors` mirrors are deleted (§4). |
| `subgroupLocusAux_le_ker_iff` (Incidence:1052, private, 6 users) | Galois step inside `vanishingLocus_le_ker_iff` proof | Same content: `I ≤ f.ker ↔ I.comap f = ⊥` via `(map_gc f).l_eq_bot` | inlined vs named | **MICRO-DEDUP**: reuse the named 3-line private inside `vanishingLocus_le_ker_iff` (hoist it above if needed). Proof-only, tiny win. [Incidence-IsoTransport.md :596–605, Other-notes (4)] |
| `sectionsDivisor` `dif_pos` unfolding — `exactOrderLocusAux_orderDivisor_ideal` (Incidence:1857) ×`fullLevelLocusAux_sectionsDivisor_ideal` (Incidence:2484) × `sectionsDivisor_pointMap_ideal` (IsoTransport:225) | home-file use in `sectionsDivisor_degree` (CartierDivisor:1628, legitimate) | Three external proofs each re-open the `dite` | Same `rw [sectionsDivisor, dif_pos ⟨…⟩]` step (all 4 sites verified by grep) | **ADD public `RelEffCartierDiv.sectionsDivisor_ideal`** in CartierDivisor (`(sectionsDivisor π P).ideal = ∏ᵢ ker (P i).1` under `[IsSeparated π]` + smoothness) and rewrite the three external proofs. Kills the brittleness flag in [Incidence-IsoTransport.md :194]. New public lemma + proof-only rewrites. |
| `Scheme.Hom.ker_iso_comp` (IsoTransport:76) | mathlib `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso` | **YES** — `ker (τ ≫ f) = ker f` for `[IsIso τ]` ≡ mathlib's `ker (f ≫ g) = ker g` for `[IsIso f]` (verified present at the local pin, `.lake/.../IdealSheaf/Basic.lean`) | equivalent one-liners | **MATHLIB-DEDUP**: replace the single use (`torsionIdeal_eq_comap`, IsoTransport:243) with the mathlib name and delete the project lemma. Public decl-removal (zero consumers after rewrite) ⇒ note in PR. |
| `tateRing` (Representability:99) | `tateRingOver` (YOneAssembly) | NO — `ℤ[A,B][Δ⁻¹]` in `Type` vs the `R`-relative `Type u` construction actually consumed by the tower | different | **KEEP BOTH, CROSS-LINK** docstrings (deliberate ring/scheme-level pair, like `NowhereOrderLEThree`/`NowhereGeomOrderLEThree`). Doc-only. [YOneHeadline.md tateRing notes] |
| `specMap_zero_appLE_fromSpec`/`specMap_π_appLE_fromSpec` (TorsionUnramifiedFibre:296/303, private) | same-named privates in KernelDivisibilityChart.lean:206/213 | YES (same shadow identities) | YES | TUF pair is **dead** (0 uses in file; verified) — delete it (§4). KDC's π-version is live (used at KDC:1118) — leave KDC alone (outside sweep). |
| `baseChange_tateA₄/₆/₂/₃` family + `tateP0sol` re-deriving `tateA₄/₆_eq_zero` (YOneAssembly) | — | uniform 4-lemma family | same shape | Micro-dedup candidate: one lemma over the four invariants; `tateP0sol` to call the named lemmas. Proof-only (family statements unchanged if kept as corollaries). LOW priority. [YOneHeadline.md cross-file obs #5] |
| `le_ker_iff_forall` (Incidence:500) | mathlib `Scheme.IdealSheafData.le_ofIdeals_iff` | Thin alias ("exactly mathlib" per inventory) | delegation | **KEEP as named alias** (3 in-file users; the name documents intent) or inline-and-delete — either is fine; flag for the batch worker. [Incidence-IsoTransport.md :405–414] |

---

## 4. Junk / dead code

All "zero consumers" claims below were re-verified by whole-`projects/` grep during this pass
(word-boundary, prime-aware). **Private dead code: delete freely** (invisible to any consumer).
**Public dead code: deletion needs a coordinator/producer ack in the PR** (it is not
statement-*changing*, but it removes API).

### 4.1 Delete now (private, verified 0 uses)
| Declaration | Location | Size | Evidence |
| --- | --- | --- | --- |
| `bcEquiv_nsmul` | YOneTatePoint:653 | 5 | [YOneHeadline.md] + grep: 1 mention repo-wide |
| `projModelVCIso_hom_congrC` / `projModelVCIso_hom_congrW` | YOneAtlasClassify (private lemmas) | small | [YOneAtlasClassify.md summary: "the only two genuinely dead declarations", v10.118 relocation leftovers] + grep: 1 mention each |
| `exactOrderLocusAux_toE_neg_eq` | Incidence:1988 | 7 | [Incidence-IsoTransport.md :1264–1272: "phi_neg/psi_neg inline the same rewrite"] + grep |
| `specMap_zero_appLE_fromSpec` / `specMap_π_appLE_fromSpec` | TorsionUnramifiedFibre:296/303 | 5+4 | [GroupLaw-Cluster.md §7: "declared and never referenced"] + grep (the 2 extra hits are the KDC copies) |
| `pullbackMapBaseChangeOf_fst` / `_snd` | GroupLawAxioms:728/741 | 11+11 | [GroupLaw-Cluster.md: "superseded by pairMapBaseChangeOf_fst/snd"] + grep: 1 mention each |
| `tripleMapBaseChangeOf_fst` / `_snd` (unprimed) | GroupLawAxioms:777/791 | 12+12 | [GroupLaw-Cluster.md: "primed Over-spelled variants are what the proofs use"] + prime-aware grep: 1 mention each |

### 4.2 Delete with producer/coordinator ack (public, verified 0 consumers repo-wide)
**AdditionSpecPoints.lean — 11 declarations** (file has zero privates; all verified at 1
mention repo-wide, prime-aware for the `factors` pair) [AdditionSpecPoints.md summary +
per-decl Notes]:
`specPoint_mulModelHom_of_blOpenZ`, `specPoint_mulModelHom_of_blOpenY` (atlas proof inlines
`blOpen*_ι_mulModelHom` instead), `specPoint_addOnZOnImage_factors`,
`specPoint_addOnYOnImage_factors` (subsumed verbatim by their primed versions),
`addOnZPieceHom_coord`, `addOnYPieceHom_coord` (plan cited in docstring; superseded by the
`chartAwayHomOfTriple_isLocalizationElem` route), `chartPointTriple_self`,
`lift_mulModelHom_comp_baseChangeOf` (re-derived via `mulModelHom_map_eq_BC`),
`lift_pullbackMap_eq_lift` + its only feeders `lift_pullbackMap_fst`/`lift_pullbackMap_snd`
(a 3-decl dead cluster — `mulModelHom_specPoints_of_map` inlines the same `hom_ext` at
:1971–1977).

**GroupLawAxioms.lean — 2 declarations** [GroupLaw-Cluster.md §2]:
- `mulOver_comm_atlas` (:370, 5-line dead wrapper — general `mulOver_comm` goes through
  `mulModelHom_comm`).
- `oneOver_mulOver_atlas` (:377, **72-line dead proof** — general left unit derived by
  braiding). Alternative to deletion: reroute `oneOver_mulOver` through it; producer's call —
  these are T-G3 atlas-level records, so get an explicit ack before removal.

### 4.3 File hygiene (verified)
- **`git rm` the three git-tracked editor artifacts**
  `EllipticCurve/TorsionUnramifiedFibre.lean.full` (73 KB), `.tail2` (12 KB),
  `.tailbody` (11 KB) — verified tracked via `git ls-files`; not built (not `.lean`);
  session leftovers [GroupLaw-Cluster.md §7 notes].

### 4.4 Zero-consumer but KEEP (register/literature anchors — refresh docstrings instead)
- **`tateRing_homEquiv` (Representability:120) — KEEP with refreshed docstring, do NOT
  delete.** Verified: zero code consumers anywhere (only prose citations in YOneTatePoint's
  E5 ledger at :1001/:1010/:1038); the executed tower routes through YOneAtlasClassify's
  `tateRingOverAlgLift` instead. Justification for keeping: (i) it is the **literal
  Loeffler Cor 3.3.5** at ring level — the citation anchor T-E2 for the whole Tate-atlas
  design; (ii) it is the *pinned*-equivalence form recording the canonical evaluation
  `φ ↦ (φA, φB)` — the 2026-07-06 adversarial fix (the bare `Nonempty (≃)` form was a
  cardinality-only claim), and deleting it would orphan that adversarial record; (iii) the
  blueprint/verso layer will want the literature-shaped statement; (iv) cost ≈ 18 sorry-free
  lines. Refresh: state explicitly that the executed route is `tateRingOverAlgLift` and
  cross-link both directions. [YOneHeadline.md #tateRing_homEquiv]
- `tateCurve_isTateNormal` (sanity pin), `isGammaOne_iff_naive` (T-D9 register),
  `sectionVanishingIdeal_eq_span_coord_coord` (T-D27), `Section.hasExactOrder_iff_etale`
  (T-D7 register — also import-tainted, hence untouchable anyway), and the terminal display
  corollaries (`yOne_representable_smooth_affine`, `gammaOneNaive_representable_zInv`,
  `exists_exactOrderLocus*`, `exists_fullLevelLocus`, `torsionIdeal_eq_comap`,
  `HasExactOrder.pointMap`, `sectionDivisor_isOfficial`, `isFullSetOfSectionsAlg_iff_*`, the
  YOneAtlasClassify `tateClassifyingHom*` API surface, `tateMarkedPoint_classifies`, …) are
  **intended leaves / downstream API — not dead code**. No action.

---

## 5. Docstring refresh list (REFRESH, never delete)

1. **`ForMathlib/GeometricFibreComparison.lean` module docstring (lines 5–31)** — verified at
   source: still says "**Shared sorried pin**", "only `map_add'` carries the `sorry`", "every
   consumer's use carries a tracked `sorryAx`". The file has **zero** sorry terms and
   `map_add'` is FILLED (ModelRecord rigidity route) [LevelStructure-Core.md §3]. Rewrite the
   header as the *proven* [T-B6′-IFACE] interface; keep the T-B6 history as a
   "formerly" note.
2. **`YOneAssembly.lean:485–503` — `tateMarkedPoint_pull_factor` GAP docstring** — verified:
   "**GAP [Y1-vi-FACTOR]** — the *only* `sorry` in the vi assembly … Discharge route: …" but
   the proof below is complete (file-wide grep: 0 code sorries). Refresh to record the
   executed discharge (keep the whnf-explosion diagnosis — it documents a real elaboration
   hazard).
3. **`YOneAssembly.lean` header** — three stale layers, all verified at source: (i) L18–19
   "`Moduli/Representability.lean:250`, HELD" (file is 206 lines; target relocated to
   YOneTatePoint:1404); (ii) the "Named gates consumed" register L43–53 still lists
   [T-W7] "A-lane in flight" (landed), [BB-DIFF MASTER] "in flight" (landed as the primed
   MulByHomEtale family), [T-E4-family] "membership sorry, held file" (discharged in
   NaiveProblems) — only [T-A6b] is still accurately sorried; (iii) L54 "planning-only
   skeleton, all leaves `sorry`" (all leaves proven). Also L582: "`map_add'` carries the
   tracked T-B6 `sorry`" — filled (item 1).
4. **`Moduli/Representability.lean` header (L19–21)** — still advertises the Y₁(N)/Y(N)
   representability targets that now live in NaiveProblems/YOneTatePoint; refresh to "T-E1/T-E2
   ring spine + `EllHom.pullSection` kernel" [YOneHeadline.md §3 summary]. Also **add the
   missing copyright header** (file starts at `import`; verified).
5. **`EllipticCurve/MulByHomFlat.lean` header** — verified at source: cites
   `mulByHom_flat_of_kernelNDivisible`, "a name that never materialized" (the chain landed as
   `mulByHom_smooth/flat_of_nIsInvertible` in MulByHomSmooth), and narrates a then-open
   discharge that has since closed. [GroupLaw-Cluster.md §3 note]
6. **`Moduli/NaiveProblems.lean` — header + 2 declaration docstrings** (all verified):
   (i) header L8: "the three parked `sorry`s" — only 2 code-sorries remain
   (`pullSection_add` and the Γ₁ membership are proven); (ii)
   `isNaiveGammaOne_pullSection_iff` docstring (L62–69): still speaks of "the membership
   sorry inside `gammaOneNaiveProblem.map` (held file)" — that sorry is discharged *by this
   very lemma* at L195–196; (iii) `EllHom.pullSection_add` docstring (L27–34): "Every
   moduli-functor `map` below … consumes this lemma" — no in-file `map` code-consumes it.
   [NaiveProblems.md #1/#3 + summary]
7. **`LevelStructure/IsoTransport.lean:42`** — verified: "Main results" bullet advertises
   `Section.HasExactOrder.comp_iso`; the theorem is named `Section.HasExactOrder.pointMap`
   (:288). Fix the bullet (or note the intended rename for the coordinator — renaming the
   *theorem* would be public-API-touching).
8. **`YOneTatePoint.lean`** — (i) `gammaOneNaive_representable_assembly` docstring (:1366–1367)
   stale pointer "`Moduli/Representability.lean:250`" (verified); (ii) the MASTER's docstring
   (:1394) has the doubled-parenthesis typo "— Y1-CLOSER S6)** = Loeffler … Drinfeld
   upgrade)**" (verified); (iii) if `_closure` is deleted (§3 row 1), fold its useful prose
   (the v10.152 axiom-trail record) into the master's docstring rather than losing it.
9. **`Representability.lean` — `tateRing_homEquiv`** docstring refresh per §4.4 (add the
   `tateRingOverAlgLift` cross-link; keep the adversarial-fix record).
10. **`YOneTatePoint.lean:992–1272` (`yOne_infinitesimal_lifting`) E5 EXECUTION LEDGER
    (L1000–1039)** — steps 3–4 no longer match the executed route (core extracted to
    `exists_tateAlgLift_core`) [YOneHeadline.md]. Compress to the executed plan when the
    decompose (§6 #2) lands; same for the 64-line ledger inside `pointSharp_add`
    (TorsionUnramifiedFibre:1031–1094) — move the superseded 6e/6f germ-route history into
    `docs/` [GroupLaw-Cluster.md §7].
11. **`RelEffCartierDiv.sectionsDivisor` (CartierDivisor:1597)** — the file's only
    undocumented public declaration [CartierDivisor.md #39]; write a docstring (with the
    junk-value-`⊤` design note) when adding `sectionsDivisor_ideal` (§7.1).
12. **`ForMathlib/GeometricFibreComparison.lean` vestigial import** — the
    `LevelStructure.ExactOrder` import appears unused [LevelStructure-Core.md §3]; **verify
    with a build before removal** (file-hygiene, not doc).
13. **Copyright headers — 13 of 20 files missing** (verified by header scan; task seeded 2 of
    these): `YOneAtlasClassify`, `Representability`, `NaiveProblems`, `CartierDivisor`,
    `Basic`, `ExactOrder`, `Incidence`, `GeometricFibreComparison`, `Torsion`, `GroupLaw`,
    `GroupLawAxioms`, `TorsionUnramifiedFibre`, `AdditionSpecPoints`. Add the standard
    AINTLIB header block (as in IsoTransport/MulByHom*). Doc-only.

---

## 6. Decompose-proof candidates (top 15, ranked)

Ranking = proof length × consumer weight × sorry-free (tainted proofs excluded — e.g.
`isOfficial` at ~120 lines is skipped as tainted). All are statement-preserving
(`/decompose-proof` extracts private helpers; the public statement is untouched). Suggested
split shapes come from the Phase-1 "How" entries.

| # | Proof | File:lines | Size | Consumers | Suggested split |
| --- | --- | --- | --- | --- | --- |
| 1 | `exists_tateAlgLift_core` (private) | YOneTatePoint:664–970 | **~305** | 1 (`yOne_infinitesimal_lifting`) — but THE E5 core | Split on the inventory's (i)–(v): étale/finite/affine torsion setup; killed-point transport through `torsionPointsEquiv`+`bcEquiv_*`; `exists_section_lift_of_smooth` application; order-≤3 transport via geometric points factor through `Spec(A⧸I)`; classify-and-uniqueness endgame (`tatePoint_classifies` + `Spec.map_injective`). [YOneHeadline.md] |
| 2 | `yOne_infinitesimal_lifting` | YOneTatePoint:992–1272 | **~280** | 1 (`yOneStructMap_smooth`) | Split along its own 6-step ledger: classify `t₀`; coefficient lift mod nilpotents; raw `tateRingOverAlgLift`; core call; naive-structure transport; `factors_yOne_iff` landing. Move the 40-line ledger comment to docs (§5.10). |
| 3 | `pointSharp_add` (private) | TorsionUnramifiedFibre:1019–1272 | **254** (incl. 64-line ledger) | the `point_eq_zero…` rigidity core | Extract 6a (algebra package), 6b (sum through the box), 6c (units off the augmentation prime), 6d (prime lands in chart); tail already hoisted. **CAUTION**: this file manages heartbeats structurally (opaque `AugLocPackage`/`EpsHalf` firewalls, hoisted tail) — decompose must preserve the small-context discipline [GroupLaw-Cluster.md §7]. |
| 4 | `kerPrincipalAux_nzd` (private) | CartierDivisor:405–648 | **~227** | T-D22 workhorse chain | Split: `Localization.Away g` stage; Jacobi–Zariski/`H1Cotangent` formal-smoothness-over-`R[X]` block; flatness ⇒ regularity; binomial `gⁿ = φ((σg)ⁿ) + f·c` endgame. **Producer-active file — coordinate; decl itself is sorry-free & untainted.** [CartierDivisor.md #13] |
| 5 | `sectionsIdealAux_exists_chart` (private) | CartierDivisor:1263–1497 | **~220** | 4 users (the T-D3 quartet) | The 9-step construction is enumerated in [CartierDivisor.md #33]; each of: group-chart assembly, disjointness (`hval`), per-piece affineness, sheaf-gluing (`bijective_restrict_pi_of_pairwise_disjoint`), rank count is a natural helper. Same producer caveat as #4. |
| 6 | `MarkedChartData.gluedTopMap_isPullback` | YOneAtlasClassify | **~180** | key API (glued-chart engine) | Per [YOneAtlasClassify.md]: split the cover-compatibility legs (cf. `coverTopMap_compat` ~140, `test_topMap_agree` ~145 already separate) into per-leg lemmas; the pullback verification is a cocartesian-legs argument. |
| 7 | `pointSharp_add_tail` (private) | TorsionUnramifiedFibre:846–1013 | **168** | 1 (`pointSharp_add`) | Already the hoisted tail; further split 6f (localization factoring) from 6g (defect-kill + unit-cancel). Same heartbeat caution as #3. |
| 8 | `mulOver_assoc_atlas` | GroupLawAxioms:204–366 | **163** | 1 (`mulOver_assoc_of_map`) | Extract the three leg-normalizations (`hπ₁/hπ₂/hπ₃`) and the two `pullback.lift … ≫ mulModelHom` collapses; golf the hundreds of spelled-out `universalWeierstrassLocU.{u}` inside the proof (local `set`/`show`). [GroupLaw-Cluster.md §2] |
| 9 | `exists_affineOpen_ker_principal_nonZeroDivisor` | CartierDivisor:*(#21)* | **~162** | 2 routes (single- & multi-section) | T-D22 workhorse: chart-shrink stage / principality stage / nzd handoff (#13). Producer caveat. |
| 10 | `fullLevelLocusAux_torsionIdeal_baseChange` (private) | Incidence:2312–2468 | **~152** | 1 (`fullLevelLocusAux_P2`) | Longest proof in Incidence, "entirely hand-rolled congrArg/assoc chains": extract the two giant leg computations (`l1…l10`, `m1…m6`) as lemmas and/or golf with `simp only [Category.assoc, pullback.lift_fst/snd]` — the inventory says the raw-typed style was a motive-dodging choice, so verify simp doesn't reintroduce the trap. [Incidence-IsoTransport.md :1426–1435] |
| 11 | `formallySmooth_mulByHom_appLE` | MulByHomSmooth | **150** | the BB-FLAT (LIFT) core | Inventory names the seams: the square-zero-thickening-is-surjective-on-Spec block and the re-algebraization block are self-contained. [GroupLaw-Cluster.md §4] |
| 12 | `officialAux_exists_mem_fibre_principal` (private) | CartierDivisor:2090–2250 | **~145** | 1 (`officialAux_stalk_span`) | Fibre-curve construction / `Ψ` transport / Nakayama descent. Sorry-free, untainted; producer caveat. |
| 13 | `mulModelHom_specPoints_atlas` | AdditionSpecPoints:1618–1776 | **139** | 1 (`…_of_map`) — file keystone chain | **8 near-verbatim arms → 2** via an index-generic arm helper (indices `i j` are the only variation within each law). The biggest structural win of the sweep. [AdditionSpecPoints.md ★] |
| 14 | `subgroupLocusAux_isSubgroup_iff` (private) | Incidence | **117** | Tier-5 keystone | Split the two directions; the membership-dictionary steps repeat `subgroupLocusAux_factors_iff` shapes. [Incidence-IsoTransport.md] |
| 15 | `point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero` | TorsionUnramifiedFibre:1285–1385 | **101** | the L-BC core (public) | Extract the `hscale` scaling induction and the `c = π♯(ζc) + (c − π♯(ζc))` decomposition endgame. Heartbeat caution. |

**Next tier** (do opportunistically inside the same batches): `mulOver_assoc_of_map` 97,
`killedLocus_preimage_isOpen` 94, `dictionary_eq_toAffine` 91,
`exists_affineOpen_mem_free`/`vanishingLocusAux_exists_basicOpen_free` 89+87 (**dedup-first**,
§3), `vanishingLocusAux_le_ker_snd` 86, `kerPrincipalAux_le_span_sup` 86,
`projModelBaseChange_projTateMap` 86 (+ machine lines, §7.6), `projTateMap_eq_of_pointedIso` 84,
`factors_yOne_iff` 82, `invOver_mulOver_of_map` 82, `mulOver_oneOver_atlas` 77,
`descended_lawTwo_smul_add` 75 (h01/h02/h12 minor blocks), `pointBaseChangeFun_add` 75,
`isFullSetOfSectionsAlg_iff_fields` 59 / `_iff_charpoly` 45, `yOneStructMap_smooth` 68,
`Spec_map_pointedIsoAwayHom_awayι` 68, `dictionary_baseChange` 64 (two clean branches),
`mulModelHom_specPoints_of_map` 62 (three π-compat side-goals → helper).

---

## 7. Missing API / helper extractions

1. **`RelEffCartierDiv.sectionsDivisor_ideal` (public, CartierDivisor)** — the single most
   valuable new lemma of the sweep: kills the three external `dif_pos` unfoldings (§3) and
   future-proofs the `dite` definition. Pair with a docstring for `sectionsDivisor` itself
   (§5.11). Consider `@[simp]` after checking the simp-set direction.
2. **Section-is-closed-immersion + `π ∘ z = id` helpers** — `sectionsIdealAux_isClosedImmersion`
   (#23) and `sectionsIdealAux_base_section` (#30) exist as privates but post-date ~5 inline
   re-proofs (`haveI hzc` idiom in #5/#6/#7/#21; inline `hπz` in #21)
   [CartierDivisor.md #23/#30 notes]. Hoist both as file-level (or `ForMathlib`) public
   helpers and use them at the inline sites. Mathlib check (loogle, verified): mathlib has
   `IsClosedImmersion.of_comp` and `IsSeparated.instIsClosedImmersionLiftSchemeId` but **no
   direct "a section of a separated morphism is a closed immersion"** — the hoisted helper is
   itself a small upstream candidate (§8.7). Producer-active file: coordinate.
3. **`torsionι_isClosedImmersion` as instance** — currently a theorem (Torsion.lean:85);
   verified **5 `haveI` consumption sites** (PointVanishingClopen:39, YOneTatePoint:412,
   FullLevelTautSection:94, Incidence:2316, Basic:88) + 1 direct term use (Subgroup:463).
   **Instance-loop risk assessment: LOW** — the head `IsClosedImmersion (E.torsionι N)` is
   structural (both `E` and `N` are determined by the head; the proof discharges via
   `pullback_fst` of `IsClosedImmersion E.zero` and never demands another
   `IsClosedImmersion (torsionι …)`); no premise-instance search. Recommended shape: keep
   the theorem byte-identical and ADD `instance : IsClosedImmersion (E.torsionι N) :=
   E.torsionι_isClosedImmersion N` next to it, then drop the `haveI`s opportunistically.
   **TC-surface-touching ⇒ coordinator-reviewed PR** (new instances can shift elaboration
   downstream), not blind auto-merge.
4. **Spurious binders — statement-touching, FORBIDDEN in cleanup lanes; route to
   generalise/coordinator**: (i) `blOpenZImage_ι_eq` / `blOpenYImage_ι_eq`
   (AdditionSpecPoints:224/284) carry `(k : Fin 3)` immediately shadowed by the `⨆ k` binder
   (verified at source); (ii) `hsm : SmoothOfRelativeDimension 1 π` is passed to
   `exists_incidenceLocusLE` (Incidence:1008) and `exists_incidenceLocusEQ` but unused in
   both proofs (instances suffice) — the inventory hedges "or intentional interface
   uniformity" [Incidence-IsoTransport.md :584], so ask the producer; (iii) the duplicated
   `[IsJacobsonRing R]` binders on `dictionary_sum_of_pieceZ/Y` and the duplicate
   `variable (i j …)` re-declaration at AdditionSpecPoints:90/129 (variable-block hygiene —
   the re-declaration itself is file-hygiene, the binder dedup is statement-touching).
5. **`affinePreimage` unused-in-spirit** — defined, then the same subtype re-spelled literally
   inside `vanishingLocus` [Incidence-IsoTransport.md note (5)]; use the def in the def-body
   (proof/def-body-only change).
6. **Machine-length lines in the atlas** — verified: `YOneAtlasClassify.lean:4257` is 3,780
   chars; :4263 2,606; :4250/:4252 ~2,300; :4237 2,019 (all inside
   `projModelBaseChange_projTateMap`) — fully elaborated eqToHom-calculus terms. Readability
   refactor via hoisted `have`s/`set`s (proof-only). Long lines also flagged at
   AdditionSpecPoints:1466/1472 (>100 chars).
7. **GroupLawAxioms verbose-spelling golf** — `universalWeierstrassLocU.{u}` written out
   hundreds of times inside proofs [GroupLaw-Cluster.md §2 summary]; introduce proof-local
   `set`/`show` abbreviations only (a file-level abbrev/notation would alter statement bytes —
   avoid).

---

## 8. ForMathlib / upstream candidates

Each verified against current mathlib (local pin + loogle) during this pass; "absent" =
no name/statement match found by the stated probe. Full `/mathlibable` runs are the follow-up.

| Candidate | Location | Mathlib status (probe) | Recommendation |
| --- | --- | --- | --- |
| `Scheme.Hom.ker_iso_comp` | IsoTransport:76 | **PRESENT** as `Scheme.Hom.ker_comp_of_isIso` (verified at local pin) | NOT upstream — **dedup-delete** (§3). |
| `Scheme.IdealSheafData.map_hom_eq_comap_inv` (`I.map φ.hom = I.comap φ.inv` for iso `φ`) | IsoTransport:57 | Absent (local_search + the IdealSheaf loogle sweeps show `map_gc`, `comap_comp` but no iso-swap lemma) | **Upstream** (tiny; `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`). |
| `Scheme.Hom.ker_comp_iso` (`ker (z ≫ φ.hom) = (ker z).comap φ.inv`) | IsoTransport:69 | Absent; one-liner over mathlib `ker_comp` + previous row | Upstream together with the previous row (single small PR). |
| `Scheme.IdealSheafData.idealMonoidHom` | ExactOrder:119 | mathlib has the `Mul`/monoid structure + `ideal_mul`/`ideal_top` (loogle-verified) but **not the bundled `MonoidHom`** | **Upstream** the bundle (gives `map_prod`/`map_pow` free; the project's use at ExactOrder:222 is exactly `map_prod`). |
| `specPoint_factors_iSup` (field point of `(⨆ U i).toScheme` factors through a member) | AdditionSpecPoints:20 | No project deps (inventory-verified); no direct probe possible by name — **UNVERIFIED against mathlib content**; plausible gap | `/mathlibable` run; strong candidate (pure `Scheme.Opens` + `IsOpenImmersion.lift`). |
| `Proj_awayι_congr` (eqToHom transport of `Proj.awayι` across generator equality) | AdditionSpecPoints:525 | Absent (loogle sweep of `Proj.awayι` lemmas has no congr) | **Upstream** (tiny), with the companion pair below. |
| `eqToHom_hom_isLocalizationElem` + `isLocalizationElem_congr_right` | AdditionSpecPoints:1786/1800 | Absent (proof-irrelevance transports for `HomogeneousLocalization.Away.isLocalizationElem`) | Upstream with `Proj_awayι_congr` (one small `HomogeneousLocalization` PR). |
| `eq_of_forall_field_hom_eq` (reduced ring: `x = y` if every hom to a field agrees) | CartierDivisor:2795 | Absent (loogle `IsReduced, RingHom, Field` probe: no match) | **Upstream candidate** (`/mathlibable`); relocation out of the producer-active file to `ForMathlib/` first. Sorry-free, untainted. |
| `ForMathlib/AgreementLocusClopen.lean` (`agreementι`, `isOpenImmersion_agreementι`, `isClosedImmersion_agreementι`, `isClopen_range_agreementι`) | 69-line ForMathlib file, present on main (verified; consumer `PointVanishingClopen.lean`) | Absent (loogle `IsClopen × IsEtale`-adjacent probes: none; mathlib has the diagonal facts the file composes) | **Prime upstream candidate** — the classical "locus where two sections of an unramified separated morphism agree is clopen" (EGA I 5.2.5-shaped). `/mathlibable --exhaustive`. |
| `Proj_map_congr` | GroupLawConstruction:70 (+ dup) | Absent (graded `Proj.map` congruence) | After the §3 hoist-dedup, upstream from its single home. |
| `exists_section_lift_of_smooth` (smooth section lifting along nilpotent thickening via Γ–Spec) | YOneTatePoint:553–606 | "fully generic — /mathlibable candidate" [YOneHeadline.md]; **UNVERIFIED** against mathlib `FormallySmooth` API by this pass | `/mathlibable` run. |
| `affine_origin_order_gt_three` | GeometricFibreComparison | "genuinely mathlib-adjacent" [LevelStructure-Core.md §3] — Weierstrass-specific | Low priority; keep project-side until the division-polynomial API stabilises. |
| `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (EGA IV 11.3.10, nzd part) | CartierDivisor:1981 | Absent from mathlib; **sorry-TAINTED via #59** | Future upstream **only after** the producer discharges T-FLAT1-SLICE. Untouchable now. |
| `officialAux_spread` (denominator-clearing spread of stalk principality) | CartierDivisor:2320 | "pure commutative algebra, mathlib-able shape" [CartierDivisor.md #64] | Bundle into the eventual CartierDivisor upstream pass; producer file caveat. |

---

## 9. Recommended action plan

Legend: **[doc]** doc-only · **[proof]** proof-only · **[hyg]** file-hygiene ·
**[decl-rm]** declaration removal (public statements of *surviving* decls untouched; needs ack)
· **[STMT]** statement-touching — **FORBIDDEN for cleanup lanes**, coordinator/generalise only.

### P0 — quick hygiene (half a day total)
1. **[hyg]** `git rm` `TorsionUnramifiedFibre.lean.full`/`.tail2`/`.tailbody` (verified
   tracked). Zero build impact.
2. **[hyg]** Delete the 10 dead **private** decls of §4.1 (YOneTatePoint ×1, Atlas ×2,
   Incidence ×1, TorsionUnramifiedFibre ×2, GroupLawAxioms ×4). Rebuild the touched modules.
3. **[doc]** Add the 13 missing copyright headers (§5.13).

### P1 — docstring refresh wave (one dispatch, ~1 day)
4. **[doc]** Items §5.1–§5.9 (GeometricFibreComparison header; YOneAssembly GAP + header +
   L582; Representability header; MulByHomFlat header; NaiveProblems ×3; IsoTransport bullet;
   YOneTatePoint pointers + typo; `tateRing_homEquiv` keep-and-refresh). No proof lines touched.

### P2 — dedup wave (each item one PR; ~2–4 days)
5. **[proof + decl-rm]** `ker_iso_comp` → mathlib `ker_comp_of_isIso` (rewrite 1 use at
   IsoTransport:243, delete the lemma). Target: IsoTransport.
6. **[proof/hyg]** `Proj_map_congr` hoist: publicise in GroupLawConstruction (or move to
   ForMathlib/GradedQuotient), delete the NegModelBaseChange copy. Targets:
   GroupLawConstruction (outside sweep — trivial visibility change), NegModelBaseChange.
7. **[proof/hyg]** Publicise `stalkDVRAux_finite_quotient_loc`
   (ForMathlib/StandardSmoothStalkDVR:225), delete `officialAux_finite_quotient_loc`
   (CartierDivisor:2382, private, untainted) and rewire `officialAux_fibre_nzd`. **Coordinate
   with the CartierDivisor producer.**
8. **[proof]** New public `sectionsDivisor_ideal` in CartierDivisor + docstring for
   `sectionsDivisor` + rewrite the 3 external `dif_pos` sites (IsoTransport:236,
   Incidence:1863, Incidence:2488). One new public lemma; all existing statements untouched.
9. **[proof]** Extract the shared free-spreading core of `exists_affineOpen_mem_free` /
   `vanishingLocusAux_exists_basicOpen_free` (Incidence; ~90 duplicated lines → 1 core +
   2 thin wrappers; statements unchanged).
10. **[proof]** Micro-dedups: `subgroupLocusAux_le_ker_iff` into `vanishingLocus_le_ker_iff`
    (Incidence); `tateP0sol`/`baseChange_tateA*` family (YOneAssembly); use `affinePreimage`
    inside `vanishingLocus` (Incidence).
11. **[decl-rm]** Dead **public** deletions with producer ack: the 11 AdditionSpecPoints
    decls (§4.2) and the 2 GroupLawAxioms atlas records (offer the reroute alternative for
    `oneOver_mulOver_atlas`). One PR per file, ack recorded in the PR body.
12. **DEFERRED dedups (blocked, do NOT dispatch)**: `formallyUnramified_torsionπ_of_nIsInvertible`
    unprimed/primed (blocked on BB-QF, §3); `gammaOneNaive_representable_closure` deletion —
    dispatchable, but ONLY with the coordinator's ratification called for in
    [YOneHeadline.md cross-file obs #1] (board-doctrine relic).

### P3 — decompose wave (top of §6; ~1–2 weeks of lane work)
13. **[proof]** In dependency-safe order per file: #13 (`mulModelHom_specPoints_atlas`
    index-generic arms — biggest structural win), then #1/#2 (+ ledger moves §5.10), #8,
    #10, #11, #6, #14, #3/#7/#15 (heartbeat caution), #4/#5/#9/#12 (producer-coordinated
    CartierDivisor sub-batch). Verify bar per worker: `lake build` green, zero new `sorry`,
    `#print axioms` unchanged.

### P4 — upstream / generalise queue (coordinator-gated)
14. `/mathlibable` runs for §8 rows marked upstream/UNVERIFIED (AgreementLocusClopen trio
    with `--exhaustive`; `idealMonoidHom`; `map_hom_eq_comap_inv` + `ker_comp_iso`;
    `Proj_awayι_congr` + the isLocalizationElem pair; `eq_of_forall_field_hom_eq`;
    `specPoint_factors_iSup`; `exists_section_lift_of_smooth`).
15. **[STMT — generalise lane only]** Spurious-binder removals (`blOpenZ/YImage_ι_eq`
    `(k : Fin 3)`; `hsm` in `exists_incidenceLocusLE/EQ` — ask producer first;
    `[IsJacobsonRing R]` binder dedup). Each changes a public signature.
16. **[TC-surface — coordinator review]** `torsionι_isClosedImmersion` instance alias (§7.3).
17. **[STMT — deferred]** MulByHomEtale primed-family renames (`'`/`''` → clean names) wait
    until the sorried originals retire [GroupLaw-Cluster.md §5 notes].

### /cleanup dispatch batches (grouping the 20 files)

- **Batch A — Y₁ headline + moduli spine** (`YOneTatePoint`, `YOneAssembly`,
  `Representability`, `NaiveProblems`): P0.2 (bcEquiv_nsmul), P1 items 2/3/4/6/8/9, P2.10
  (tate family), P2.12 (`_closure`, with ratification), P3 #1/#2 + `killedLocus_preimage_isOpen`,
  `factors_yOne_iff`, `yOneStructMap_smooth`. UNTOUCHABLE: NaiveProblems carriers 15–16.
- **Batch B — LevelStructure engine** (`Incidence`, `IsoTransport`, `CartierDivisor`,
  `Basic`, `ExactOrder`): P0.3 headers, P1.7, P2.5/7/8/9/10, P3 #4/#5/#9/#10/#12/#14, §7.1/7.2.
  UNTOUCHABLE: carriers 1–6, 10–12 + the 5-decl closure + T-D6/T-D7 headlines.
- **Batch C — GroupLaw cluster** (`GroupLaw`, `GroupLawAxioms`, `NegModelBaseChange`,
  `MulByHomFlat`, `MulByHomSmooth`, `MulByHomEtale`): P0.2 (4 privates), P1.5, P2.6, P2.11
  (2 atlas records), P3 #8/#11 + next-tier `mulOver_assoc_of_map`/`invOver_mulOver_of_map`,
  §7.7 golf. UNTOUCHABLE: carriers 13–14; unprimed unramified chain (import-tainted).
- **Batch D — fibre & spec-points engines** (`TorsionUnramifiedFibre`,
  `AdditionSpecPoints`): P0.1 (artifacts), P0.2 (2 privates), P2.11 (11 publics), P3
  #3/#7/#13/#15 + `descended_lawTwo_smul_add`/`dictionary_baseChange`/
  `mulModelHom_specPoints_of_map`, §5.10 ledger move, long-line fixes. Heartbeat caution
  throughout TorsionUnramifiedFibre.
- **Batch E — atlas + torsion interface** (`YOneAtlasClassify`, `GeometricFibreComparison`,
  `Torsion`): P0.2 (2 privates), P0.3 headers, P1.1, §5.12 import check, §7.6 machine-line
  refactor, P3 #6 + `test_topMap_agree`/`coverTopMap_compat`/`pt_hord`. UNTOUCHABLE:
  carriers 7–9.
- **Batch F — upstream/generalise queue** (coordinator): P4 items 14–17, plus review of the
  P2.11/P2.12 acks and merge of the generalise-lane PRs.

---

*Phase-2 analyst, 2026-07-12. Every UNVERIFIED marker above denotes a claim taken from a
Phase-1 inventory (or a mathlib-absence judgment) that was not independently re-verified at
source/mathlib during this pass; everything else was spot-checked as cited.*
