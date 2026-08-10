# Development Plan: Strengthenings — strong sheafiness and Čech acyclicity for the two examples

**Campaign 6** (started 2026-08-10, branch `wp/strengthenings`). Consumes the completed
Campaign 4 (finite-jet, `plan-fjp-campaign4-archived-2026-08-10.md`) and Campaign 5
(weighted-parity; terminal board archived in git history at `f368b6917`). Both examples'
headline theorems are comparator-certified on `announce/sheafy-not-stably-uniform`
(tag `sheafy-paper-v1`); this campaign proves the reviewer-proposed strengthenings.

## Goal (strongest-first)

- **A (WP strong sheafiness, honest vocabulary).**
  `IsSheafyComplete ↥(restrictedMvPowerSeriesSubring s (WPA K w))` under the canonical
  `mvTateAlgebraTopology'` — i.e. the project's own Tate-extension object `𝒜⟨V₁,…,Vₛ⟩`
  is sheafy, for every `s`. With the certified `wp_8_1_not_isStablyUniform` this makes
  **"strongly sheafy does not imply stably uniform"** fully formal.
- **B (FJP strong sheafiness).** The same statement for `JetA F`:
  `restrictedMvPowerSeriesSubring n (JetA F)` sheafy for every `n`, by re-running the
  Milnor route with the auxiliary Tate variables carried along (paper §5–§6; the
  corners stay strongly noetherian affinoids).
- **C (rational Čech acyclicity, all degrees).** Upgrade the Lean rendering of Wedhorn
  Lemmas 8.33/8.34 from the separation+gluing content to the full augmented-complex
  `IsAcyclic` (this is what Wedhorn actually proves), then transport to the two
  examples: Milnor LES for `JetA`, coefficientwise `c₀`-primitives for `WPA`.

## References
- [WP-paper] `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex` (local
  revision; the live revision at cbirkbeck.github.io/uniform-sheafy-tate-domains
  renumbers the headline theorems 1.1 / 8.1 and drops the reducedness claim — quotes
  below cite the local tex by line).
  - §5 Milnor localization: `lem:koszul` (l.382), `lem:graph-pullback` (l.464),
    `prop:localized-milnor` (l.521)
  - §6 sheafiness: `lem:sheaf-transfer` (l.576), `thm:sheafy` (l.645)
  - §8 weighted-parity: `prop:coefficientwise-localization` (l.1036),
    `cor:finite-head-presentation` (l.1097), `thm:parity-strongly-sheafy` (l.1131)
    with `eq:strong-sheafy-decomposition` (l.1229)
- [Wedhorn] `refs/AdicSpaces/wedhorn.txt`: Lemma 8.33 (l.4151), Lemma 8.34 (l.4222),
  Prop A.3/A.4 (appendix); these are **all-degree** augmented-Čech statements.
- [Reviewer] the 2026-08-10 referee report (in conversation; §5.1 strong sheafiness,
  §5.2 acyclicity, §4.1 abstract Milnor descent, §4.2 finite-stage criterion).

## Mathlib / project inventory
| Concept | Status | Action |
|---|---|---|
| `𝒜⟨V₁..Vₛ⟩` object | `restrictedMvPowerSeriesSubring` + `mvTateAlgebraTopology'` (MvTateAlgebraTopology.lean, generic over a Tate ring `A`) | USE |
| `𝒜⟨V⟩ ≅ WPA(shiftWeight)` | `tateExtEquiv` (WP/Sheafy.lean:2274) + `tateExtEquiv_bicontinuous` (W24b) | USE |
| sheafiness transport | `isSheafyComplete_congr` (SheafyRingEquivTransport.lean:96) | USE |
| shifted-weight sheafiness | `wp_stronglySheafy` (WP/Sheafy.lean:2421), certified | USE |
| Tate ext of Tate algebra ≅ Tate algebra | `FJP/RestrictedFubini.lean` — 2 sorried Gauss-transport legs | CLOSE (B gate) |
| full Čech complex | `CechCohomology.lean` (`CechCochain`, `cechDiff`, `IsAcyclic`, refinements, product covers) | USE |
| Wedhorn 8.33/8.34, degree-0 form | `wedhorn_lemma_833/834` (WedhornCechAcyclicity.lean) | EXTEND to `IsAcyclic` |
| Milnor row + transfer | FiniteJetSheafTransfer.lean (JetA-concrete) + graph-Koszul stack | PARAMETERIZE / abstract |

## File structure (new)
- `Adic spaces/WP/StrongSheafy.lean` — Campaign A target + headline
- `Adic spaces/FJP/StrongSheafy.lean` — Campaign B headline + first-layer leaves
- `Adic spaces/CechAcyclicityFull.lean` — Campaign C corner upgrades + example headlines

## Generality decisions
- A/B state sheafiness of the **generic** Tate-extension object
  `restrictedMvPowerSeriesSubring n A` at `A = WPA K w` (any weight, not just `id`) and
  `A = JetA F` — maximum generality the existing objects support.
- C upgrades the corner lemmas at Wedhorn's own generality (strongly noetherian Tate
  affinoid), not per-example.
- The reviewer's abstract criteria (§4.1 Milnor descent, §4.2 finite-stage descent) are
  **generalisation endpoints**: B's transfer instantiation is planned through an abstract
  `lem:sheaf-transfer` statement (the paper's own form), so the criterion falls out.

## Dependency graph
```
A1 (letI statement + congr transport)  ──→ A-headline (𝒜⟨V⟩ sheafy ∀s)   [READY NOW]
B-L1,B-L2 (RestrictedFubini legs) ──→ B-L3 (corners affinoid+sheafy)
B-L4 (abstract sheaf-transfer) ──→ B-L5 (⟨V⟩ Milnor row) ──→ B-headline
C-L1 (8.33 all-degree) ──→ C-L2 (8.34 all-degree via A.3 product/refinement)
C-L2 + B-machinery ──→ C-FJP;  C-L2 + §8 coefficientwise ──→ C-WP
```
Campaigns are independent except C-FJP consuming B's row machinery. Priority: A → B → C.
