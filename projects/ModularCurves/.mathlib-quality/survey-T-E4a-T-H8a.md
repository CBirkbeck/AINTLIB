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
