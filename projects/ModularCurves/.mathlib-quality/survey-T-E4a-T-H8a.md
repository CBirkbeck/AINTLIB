# [T-E4a/T-H8a SURVEY] — beastmode-A, 2026-07-09 (scoping only, NO held-file edits)

Deliverable for the v10.75 dispatch: inventory the held functor-law/membership sorries, test
NEW-GH's `Point.asSection_add` transport pattern against them, recommend a route + wiring.

## Inventory of held sorries (all in `Moduli/Representability.lean`, held file)

| # | Sorry | Line | Role |
|---|-------|------|------|
| 1 | `EllHom.pullSection_add f (P + Q) = pullSection f P + pullSection f Q` | :207 | **LINCHPIN** — the ℤ-linearity of `pullSection` |
| 2 | `gammaOneNaiveProblem.map` membership (`IsNaiveGammaOne` preserved under `pullSection`) | :214 | T-E4 functor law (Γ₁) |
| 3 | `gammaFullNaiveProblem.map` membership (`IsNaiveFullLevel` preserved) | :229 | T-E4 functor law (Γ(N)) |
| 4 | `gammaOneNaive_representable` | :254 | T-E7 (separate, representability — NOT this survey) |

`map_id`/`map_comp` for #2/#3 are **already proven** via `pullSection_id`/`pullSection_comp` (:155/:168).

## The linchpin: `pullSection_add` un-gates the rest

`EllHom.pullSection_zsmul` (`GammaHRepresentability.lean:946`) is already proven **assuming**
`pullSection_add`: `map_zsmul (AddMonoidHom.mk' (pullSection R f) (pullSection_add R f)) n P`. So
proving #1 immediately gives `pullSection_zsmul` and feeds `pullAlong_glSmul` (:1002) and the
`glSmul`-membership work (:1025). #2/#3 memberships then reduce to order/generation preservation
(which are `pull`/`asSection`-linear once #1 lands). This is the same sorryAx-inheritance chain that
poisons YFULL AFF/FIN and GH1.

## Does NEW-GH's `asSection_add` pattern discharge `pullSection_add`? — PARTIALLY

`Point.asSection_add` (`GammaHRepresentability.lean:966`) route:
```
apply (Point.baseChangeEquiv E g (𝟙 T)).injective
rw [map_add, baseChangeEquiv_asSection ×3, Point.restrict_add]
```
i.e. transport the equality across the **additive** `Point.baseChangeEquiv`, because `Section`/`Point`
addition has *no direct underlying-morphism formula* (can't `pullback.hom_ext` a sum directly).

**Applicability to `pullSection_add`:**
- `EllHom.pullSection f P := ⟨f.isPullback.lift (f.baseHom ≫ P.1) (𝟙 X.base) …, …⟩` — it lives on the
  **EllObj/Section layer** (built from `f.isPullback.lift`), NOT the `Point` layer, so
  `Point.baseChangeEquiv` does not apply verbatim. The *shape* of the argument (transport across an
  additive equiv, never touch the sum's `.1` directly) is correct; the missing ingredient is a
  **Section-layer transport equiv** — either (a) an `EllObj`/`Section` analog of `baseChangeEquiv`
  whose inverse is `pullSection` up to a reindex, or (b) a bridge `pullSection f (⟨P as point⟩) =
  asSection (pull …)` reducing `pullSection` to the already-linear `Point.pull`/`asSection`
  (`pull_add`/`asSection_add`). Route (b) is the more promising: `GammaHRepresentability.lean:853`
  already exhibits `pullSection (pullbackAlongMap g k) (asSection X.curve g P) = …`, i.e. a
  `pullSection∘asSection` formula — generalising that to *every* `Section` (via `Section ≅ Point over 𝟙`)
  reduces `pullSection_add` to `pull_add` + `asSection_add` (both NEW-GH-provided/provable).

## ⚠ CORRECTED VERDICT (after reading `PullSectionAdd.lean` + the board) — the linchpin is T-W7.8-PARKED, not landable

The `asSection_add`/`baseChangeEquiv` transport pattern is **already implemented**:
`pullSection_add_of_isLocallyNoetherian` (`PullSectionAdd.lean:169`) proves exactly #1 via
`transportSection_injective` + `transportSection_add` + `Point.baseChangeEquiv` + `Point.pull_add`
+ the `dict_transportSection_pullSection` bridge — i.e. route (b), realised. **BUT it carries
`[IsLocallyNoetherian X.base]`** (`transportSection_add` :102 needs it).

The **unrestricted** `pullSection_add` (`Representability.lean:207`) is **deliberately PARKED behind
T-W7.8** — its own docstring (`PullSectionAdd.lean:165-168`) says so, and the board confirms
(`tickets.md:3496-3507`): T-W7.8 = arbitrary-`R`-scheme generality via EGA IV §8 spreading-out, a
**blocked-on-mathlib gap**; **OWNER DECIDED 2026-07-08: keep arbitrary bases, functor-law sorries stay
parked behind T-W7.8; "when T-W7.8 lands, swapping [them] in."**

**So there is NO standalone lemma for me to land** — the pattern is done (noetherian branch); the
arbitrary-base branch (#1 unrestricted → #2/#3 via `pullSection_zsmul`) is scope-blocked on a mathlib
gap by explicit owner decision. This is a "verify-before-grind" catch: the v10.75 framing (land
standalone lemmas discharging the T-E4-family) predates / lost track of the 2026-07-08 T-W7.8 parking
decision — like the map_id and T-A3 moot re-dispatches.

## Recommendation

1. **Do NOT re-attempt unrestricted `pullSection_add`** — it is owner-parked behind the T-W7.8 mathlib
   gap, not a provable held sorry. The sorryAx inheritance poisoning YFULL AFF/FIN + GH1 (and the
   Γ₁/Γ(N) functor maps) is fundamentally T-W7.8-gated; it clears when T-W7.8 lands, not before.
2. **Consumers whose base IS locally noetherian** can be re-wired NOW to
   `pullSection_add_of_isLocallyNoetherian` (`PullSectionAdd.lean:169`) — the noetherian branch is
   axiom-clean. Worth checking whether YFULL AFF/FIN / GH1 fibres are noetherian (they often are over a
   noetherian `R`); if so, that re-wire clears their inheritance without T-W7.8. This is a holder task
   (their files), a wiring note not a new lemma.
3. The **vi-gate** inheritance I traced separately (`tateMarkedPoint_pull_fst` → `tateUniversal`/
   `tateMarkedPoint`/`pointSpecPointsEquiv`) is a **different** upstream chain — [T-B6′] territory, not
   the T-W7.8/pullSection branch.

**Net:** the survey's target is not a landable lemma but a scope-parked gap (T-W7.8, owner-decided).
Standing down on it per "wall ⟹ board forensics + stand down." The one actionable follow-up is the
noetherian-rewire check for the specific poisoned consumers — a holder decision, flagged here.

---

# PART 2 — the full [T-H8a] inventory (v10.94 dispatch; scoping only, NO held-file edits)

*Extension 2026-07-09 (post-[Y1-D2] discharge). Supersedes Part 1's verdict where noted: the T-E4
linchpin is no longer "T-W7.8-parked" — it is **collapsed to the one primitive**
`isMonHom_of_one_comp_eq'_of_finitePresentation` (`Moduli/PullSectionCanonicity.lean`, 7dac70553),
which lands at T-W7a (route c) or via the banked route (a).*

## What T-H8a is (code-verified)

**[T-H8a] = the Drinfeld problems' functor laws** (board :3519). Exactly TWO held sorries, both in
`Moduli/GammaH.lean` (GH-lane held file), both `map`-field **memberships** (the `map_id`/`map_comp`
laws are already proven via `pullSection_id`/`_comp`, same pattern as the naive problems):

| # | Sorry | Line | Predicate to transport |
|---|-------|------|------------------------|
| 1 | `gammaFullDrinfeldProblem.map` membership | `GammaH.lean:994` | `IsFullLevel N` under `pullSection` |
| 2 | `gammaOneDrinfeldProblem.map` membership | `GammaH.lean:1008` | `IsGammaOne N` (= `HasExactOrder`) under `pullSection` |

NOT T-H8a: `gammaFullDrinfeld_representable` (:1033) / `gammaOneDrinfeld_representable` (:1046) are
T-H8/T-H9 (representability, `hinv`-hypothesised after the 2026-07-06 adversarial fixes).

⚠ Scope note: the Drinfeld problems are deliberately over **arbitrary `R`** (no `N`-invertibility —
"at primes dividing `N` it is the correct object", :987). The memberships as stated must transport
without `hinv`. The T-D8/T-D9 naive-bridges do NOT discharge them (see Route N-INV below).

## Predicate anatomy → transport requirements

- **`IsGammaOne N P := (P.orderDivisor E N).IsSubgroup E`** (`ExactOrder.lean:104`), with
  `orderDivisor = sectionsDivisor E.π (fun a : Fin N => ((a:ℤ)+1) • P)` (:97) — ℤ-multiples of `P`
  (group data) + a Cartier-divisor subgroup condition.
- **`IsFullLevel N P Q`** (`LevelStructure/Basic.lean:100`) = killing clauses
  `(N:ℤ)•P = 0 ∧ (N:ℤ)•Q = 0` **∧** divisor equality
  `(sectionsDivisor E.π (fun i : Fin (N²) => (i%N:ℤ)•P + (i/N:ℤ)•Q)).ideal = E.torsionIdeal N`.

`pullSection` factors (T-E4a Part-1 dictionary, all proven): across the **pointed comparison iso**
`curveIsoPullback : X.curve.E ≅ pullback Y.curve.π f.baseHom` composed with the **base-change leg**
`Y.curve → Y.curve.baseChange f.baseHom`. So each membership transports in two legs.

## Inventory: what EXISTS (all proven, file:line-verified)

**Leg 1 — base change (COMPLETE, nothing to build):**
- `Section.HasExactOrder.baseChange` (`ExactOrder.lean:188`, T-D6a-ii headline) — exact order is
  preserved by base change, via `orderDivisor_baseChange` + `RelEffCartierDiv.IsSubgroup.baseChange`
  (`ExactOrder.lean:174`).
- `RelEffCartierDiv.baseChange` + `baseChange_ideal` (`CartierDivisor.lean:1644/1653`) — the
  divisor/ideal side. `torsion_baseChange_isPullback` (`TorsionFibre.lean:243`) — `torsionIdeal`.
- `degree_baseChange_eq` (`DeligneOrder.lean:2070`), `generatorSpace_baseChange` (`NIsogeny.lean:278`).

**Group-algebra content (COMPLETE via [Y1-D2] discharge):**
- Killing clauses + the ℤ-linear combinations `(i%N)•P + (i/N)•Q` inside `sectionsDivisor` transport
  by `pullSection_add_of_finitePresentation` + `pullSection_zsmul_of_finitePresentation`
  (`PullSectionCanonicity.lean`) — **the same one primitive, no new gate**.

**Drinfeld ↔ naive bridges (proven, `NIsInvertible` only):**
- `isGammaOne_iff_naive` (T-D9, `Basic.lean:143`), `isFullLevel_iff_naive` (T-D8, `Basic.lean:130`).

## Inventory: what WAS absent — the iso-leg — now ✅ BUILT (2026-07-10, v10.94b dispatch)

**Leg 2 — the comparison-iso leg — DELIVERED, sorry-free + axiom-clean**, hypothesis-funneled
(`hη`/`hμ` as hypotheses, the `transportSection_add_of_isMonHom` pattern):
**`LevelStructure/IsoTransport.lean`**. Contents (all `lean_verify` clean —
propext/Classical.choice/Quot.sound):
1. Generic scheme lemmas: `IdealSheafData.map_hom_eq_comap_inv`, `Scheme.Hom.ker_comp_iso`,
   `Scheme.Hom.ker_iso_comp` (mathlib-shaped; future PR-draft candidates).
2. Postcomp algebra + intertwining: `one/mul/zpow_comp_monHom` (postcomposition with a pointed
   mul-compatible morphism is a `Hom`-group hom), `mulBy_comp_monHom` (`[n]`-intertwining — both
   sides are `e^n` in the Hom-group), `mulByHom_comp_monHom`, `zero_comp_monHom`.
3. `pointAddEquiv : E.Point g ≃+ E'.Point g` at every `g : T ⟶ S` (`pointMapOfHom` + additivity).
4. `sectionsDivisor_pointMap_ideal` — sections-divisor ideal transport (comap along the inverse).
5. `torsionIdeal_eq_comap` — via the `pullback.map` comparison of the two torsion kernels.
6. `RelEffCartierDiv.IsSubgroup.of_ideal_comap` (via `exists_factor_comap_iff`) +
   `Section.HasExactOrder.pointMap` (the `IsGammaOne` iso-leg; needs only `hμ` — pointedness is
   automatic for additive maps).

## Routes (holder = GH lane; coordination per attack-1, no duplication)

- **Route FULL (the genuine discharge, arbitrary `R`):** leg 1 (exists) + leg 2 (the 4 iso-lemmas
  above) + the group-algebra funnel (exists). **Gate: the SAME one primitive** — leg 2's items 2–4
  consume the group-iso property of `curveIsoPullbackOver` exactly as `transportSection_add` does.
  Nothing else gates it. Post-T-W7a this is bounded holder work (or falls-sweep work in my lane if
  dispatched — the 4 lemmas are standalone-stageable in my own file).
- **Route N-INV (short, consumer-scoped — does NOT discharge the held sorries):** for consumers with
  `IsUnit (N:R)` (both T-H8/T-H9 do), Drinfeld membership ↔ naive membership (T-D8/T-D9) + the naive
  transport ([Y1-D2] lemmas). Cannot close the held `map` fields (arbitrary `R`, statement-protected)
  — flag ONLY as the wiring shortcut for `hinv`-carrying consumers.

## Verdict

**T-H8a adds NO new gate.** Same funnel: everything either exists (leg 1, bridges, group algebra) or
is bounded post-primitive work (leg 2, ~4 iso-invariance lemmas). The falls-sweep order at T-W7a:
(1) wire the primitive (route c) → (2) T-E4 family (Y1-D2, YFULL AFF/FIN, GH1) goes clean → (3) the
T-H8a iso-leg lemmas → (4) both Drinfeld memberships close. The held sorries stay held (GH lane);
this inventory + the [Y1-D2] wiring note are the coordination artifacts.
