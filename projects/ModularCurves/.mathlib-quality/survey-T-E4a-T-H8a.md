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

**Verdict:** the pattern is the right *strategy* but not a *drop-in*. `pullSection_add` is a focused
~30–50-line transport development (route (b): the `Section ≅ Point` bridge + `pull_add`/`asSection_add`),
NOT a one-line mirror. Its profile — a Section-layer transport lemma at the EllObj boundary — matches
the fresh-full-budget-session doctrine; grinding it at a session tail risks the wrong reduction.

## Recommendation / wiring note (for the holder of Representability.lean)

1. **Land `EllHom.pullSection_add` first** (route (b)): prove the general bridge
   `pullSection f P = asSection_of_pull (pointOfSection P)` (Section↔Point over 𝟙), then
   `pullSection_add := by rw [bridge, bridge, bridge, pull_add, asSection_add]`. Standalone, in a
   beastmode-A ForMathlib/Moduli helper file; holder replaces `:207 sorry` with it.
2. #2/#3 memberships: with #1 landed, `IsNaiveGammaOne`/`IsNaiveFullLevel` preservation under
   `pullSection` follows from order/generation being read off the (now-linear) pulled section.
3. This clears the `pullSection`-branch of the sorryAx inheritance (YFULL AFF/FIN, GH1). The
   *vi-gate* inheritance I traced separately (`tateMarkedPoint_pull_fst` → `tateUniversal`/
   `tateMarkedPoint`/`pointSpecPointsEquiv`) is a **different** upstream chain — [T-B6′] territory,
   not this survey.

Owner-input requested: land route (b) now in a fresh focused block, or defer to the holder? The
Section↔Point bridge is the crux and wants a clean-budget pass.
