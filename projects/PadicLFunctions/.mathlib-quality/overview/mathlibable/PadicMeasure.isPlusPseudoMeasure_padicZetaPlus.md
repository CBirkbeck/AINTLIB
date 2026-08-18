# `/mathlibable` report — `PadicMeasure.isPlusPseudoMeasure_padicZetaPlus`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search.

**Target:** `PadicMeasure.isPlusPseudoMeasure_padicZetaPlus`
**Kind:** theorem
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:240`
**Date:** 2026-06-20

---

## FINAL VERDICT: `BORDERLINE-needs-human`

> This theorem is **RJW Corollary 11.4 / §11.1 corollary** — "the Kubota–Leopoldt
> p-adic zeta function `ζ_p` descends to a pseudo-measure on `𝒢⁺ = ℤ_p^×/{±1}`". It is
> a genuine, named, classical result (the plus-part descent of the KL pseudo-measure —
> the foundational object of the Iwasawa Main Conjecture for totally real fields,
> Mazur–Wiles). Mathlib has **none** of the apparatus it is phrased in (no pseudo-measure
> predicate, no Iwasawa algebra of measures, no `padicZeta`, no plus-part quotient), so
> both NO buckets are ruled out (nothing to cite, nothing to compose from). But it is
> also **not a confident YES**: it cannot ship ahead of the entire `padicZeta` /
> pseudo-measure / Iwasawa-algebra foundation it sits atop, and its *parent predicate*
> `IsPlusPseudoMeasure` is itself `YES-but-generalise-first` (the group must be
> abstracted, merging the `ℤ_p^×` and `ℤ_p^×/{±1}` copies). Whether mathlib wants that
> whole foundation, and how the descent corollary should be sequenced/restated against
> the group-abstract predicate, are judgment calls the skill cannot ground in the
> evidence. Hence BORDERLINE, consistent with every sibling headline-`ζ_p` report in
> this project (`dirac_neg_one_sub_one_mul_padicZeta`, `twistedZetaHalf_isTwistedPseudoMeasure`,
> `padicZeta_witness_neg`).

---

## Phase 0 — Doctor / baseline

- **lake build:** **not re-run; reasoned from source** (per task BUILD NOTE — the worktree
  build is stale/slow; the declaration and its full dependency closure were read directly
  from source, exactly as the skill's Phase-0 fallback permits).
- **decl `PadicMeasure.isPlusPseudoMeasure_padicZetaPlus`:** ✓ resolved at
  `ZetaGalois.lean:240`.
- **kind:** theorem.
- **has sorry:** no. `ZetaGalois.lean` is sorry-free (`grep -c "sorry\|admit"` = 0); the
  proof is complete and every dependency it calls is a compiling declaration.
- **module docstring summary:** "ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p" —
  RJW (arXiv:2309.15692) §11.1 corollary + §11.2 (TeX 2992, 3033–3059), on the identified
  Galois side (`𝒢⁺ = GPlus p`).

**Dependency closure (read from source):**
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — `ℤ_p`-valued
  measures on `X`; with convolution this is the Iwasawa algebra `Λ(X)`.
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)` (`Iwasawa/PlusPart.lean:215`) — the
  plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}`.
- `projPlus p : PadicMeasure p ℤ_[p]ˣ →+* PadicMeasure p (GPlus p)` (`PlusPart.lean:224`) —
  the pushforward `Λ(𝒢) ↠ Λ(𝒢⁺)`.
- `QuotientFieldPlus p := FractionRing (PadicMeasure p (GPlus p))` (`ZetaGalois.lean:124`) —
  the total ring of fractions `Q(𝒢⁺)`.
- `IsPlusPseudoMeasure p` (`ZetaGalois.lean:133`) — **the parent predicate** (already
  assessed: `YES-but-generalise-first`, see `PadicMeasure.IsPlusPseudoMeasure.md`).
- `padicZetaPlus p hp2 : QuotientFieldPlus p` (`ZetaGalois.lean:177`) — ζ_p⁺, the descended
  p-adic zeta function, `mk'(projPlus(zetaNum a))/([ā]−[1])`.
- `padicZeta_isPseudoMeasure` (`KubotaLeopoldt/ZetaP.lean:269`, RJW Prop. 4.11) — the
  `ℤ_[p]ˣ`-side analog: ζ_p is a pseudo-measure on `𝒢`. **The 𝒢-side input that is pushed
  forward.**
- `projPlus_padicZeta_witness` (`ZetaGalois.lean:190`) — pushing a 𝒢-side witness forward
  gives the 𝒢⁺-side witness ("ζ_p descends"). **The engine of this proof.**
- `QuotientGroup.mk_surjective` (mathlib) — the surjectivity of `𝒢 ↠ 𝒢⁺`; **the only
  mathlib decl in the proof body.**

## Phase 1 — Comprehend

### Statement

```lean
/-- **RJW §11.1, Corollary (TeX 3033–3039)**: the p-adic zeta function is a
pseudo-measure on `𝒢⁺`. -/
theorem isPlusPseudoMeasure_padicZetaPlus (hp2 : p ≠ 2) :
    IsPlusPseudoMeasure p (padicZetaPlus p hp2) := by
  intro gPlus
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gPlus
  obtain ⟨ν, hν⟩ := padicZeta_isPseudoMeasure p hp2 g
  exact ⟨projPlus p ν, projPlus_padicZeta_witness p hp2 g hν⟩
```
with `variable (p : ℕ) [hp : Fact p.Prime]`.

`isPlusPseudoMeasure_padicZetaPlus` is a theorem stating the following:

Let `p` be an odd prime. The descended p-adic zeta function `ζ_p⁺ := padicZetaPlus p hp2`,
an element of the total fraction ring `Q(𝒢⁺) = Frac(Λ(𝒢⁺))` of the Iwasawa algebra of
the plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}`, is a **pseudo-measure on `𝒢⁺`**: for every
`ḡ ∈ 𝒢⁺` the augmentation-twisted product `([ḡ]−[1])·ζ_p⁺` lies in the image of `Λ(𝒢⁺)`
inside `Q(𝒢⁺)` (i.e. is an honest measure). This is RJW's §11.1 corollary (Corollary 11.4):
because `ζ_p` is c-invariant (`([−1]−[1])·ζ_p = 0`), it descends from `𝒢 = ℤ_p^×` to the
plus-part quotient `𝒢⁺`, and the descended object is again a pseudo-measure.

**Proof outline (Lean side):** lift `ḡ ∈ 𝒢⁺` to a unit `g ∈ ℤ_p^×` via surjectivity of
`𝒢 ↠ 𝒢⁺` (`QuotientGroup.mk_surjective`); take the 𝒢-side witness `ν` of `([g]−[1])·ζ_p`
from `padicZeta_isPseudoMeasure` (RJW Prop. 4.11); push it forward, `projPlus ν`, and invoke
`projPlus_padicZeta_witness` to certify it is the 𝒢⁺-side witness of `([ḡ]−[1])·ζ_p⁺`.

**Variables / typeclasses (Lean side):**
- `(p : ℕ) [hp : Fact p.Prime]` — the prime; fixes the coefficient ring `ℤ_[p]`.
- `(hp2 : p ≠ 2)` — odd prime (the standing §11 hypothesis: the plus/minus splitting and the
  order-2 structure of `⟨−1⟩` require `p` odd, and `2` invertible).

**Hypotheses:** only `(hp2 : p ≠ 2)` beyond the implicit `[Fact p.Prime]`.

**Conclusion (math):** `ζ_p⁺` is a pseudo-measure on `𝒢⁺` (`∀ ḡ, ([ḡ]−[1])·ζ_p⁺ ∈ Λ(𝒢⁺)`).

**Conclusion (Lean):** `IsPlusPseudoMeasure p (padicZetaPlus p hp2)`.

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** It is a **named theorem** — the §11.1 corollary, listed verbatim in the
module docstring's "Main declarations" cluster (`padicZetaPlus` + `isPlusPseudoMeasure_padicZetaPlus`:
"**the corollary of RJW TeX 3033** — ζ_p descends to a pseudo-measure on 𝒢⁺"). It is the
headline output of the file and the named object the §12 Iwasawa-theorem statements consume.
(Literature width is EXHAUSTIVE regardless; BIG/SMALL is framing only.)

### One-line check (Phase 2b)

- **Body line count:** 4 substantive tactic lines (`intro` / two `obtain` / `exact`). Kind is
  theorem, not def.
- **One-liner verdict:** n/a — kind is theorem. Section skipped (the exemption table is for
  `def`/`abbrev`/`instance`).

**Conclusion:** proceed to the exhaustive literature search.

## Phase 3 — EXHAUSTIVE literature search (9 channels)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic zeta function pseudo-measure on Galois group descends quotient plus part Iwasawa Coates Serre ([g]−1)λ" | **yes** | the descent is standard: "The Galois group `Γ⁺ = Gal(F∞⁺/ℚ) = Γ/⟨c⟩` is identified through the cyclotomic character with `ℤ_p^×/{±1}`"; "the p-adic zeta function can be reformulated as a pseudo-measure on the Galois group" | top hits are the source RJW arXiv:2309.15692 and HandWiki/Wikipedia "p-adic L-function"; the plus-part `Γ/⟨c⟩ ≅ ℤ_p^×/{±1}` is exactly `GPlus p`. |
| 2 | WebSearch (general / named) | "Kubota–Leopoldt p-adic L-function pseudomeasure totally real field Deligne–Ribet ([σ]−1) measure Iwasawa main conjecture" | **yes** | *verbatim:* "An element f in the field of fractions of `Λ(G)` is called a pseudomeasure if `(g−1)f` lies in `Λ(G)` for every g in G"; "The pseudomeasure framework is central to the formulation of the Iwasawa main conjecture for totally real fields." | Serre's reading of Deligne–Ribet; Mazur–Wiles proved the resulting Main Conjecture. The descent-to-pseudo-measure is the *foundational object*, not an obscure corollary. |
| 3 | WebSearch (named-after / Coates–Sujatha / unique) | "Serre pseudomeasure zeta function p-adic riemann zeta unique pseudo-measure Q(Γ) Λ Iwasawa algebra theorem statement Coates Sujatha" | **yes** | "there is a unique element in the group algebra that encodes all the ℓ-adic L-functions for characters with open kernel"; "Pseudomeasures (in the sense of Serre) hold the arithmetic properties of the abelian ℓ-adic Artin L-functions over totally real number fields" | Coates–Sujatha, *Cyclotomic Fields and Zeta Values* (Springer 2006) is the standard reference; Serre's pseudomeasure of the Riemann zeta is the prototype. |
| 4 | ChatGPT MCP (math second opinion) | (attempted) "RJW Corollary 11.4 — ζ_p as pseudo-measure on ℤ_p^×/{±1}; descent via c-invariance; standard form; historical evolution; arbitrary group?" | **n/a** | — | the ChatGPT/codex MCP server is **not connected** in this session (no `ask_chatgpt`/codex tool surfaced by ToolSearch). **Compensated** by running a **fourth** WebSearch (row 3) at a different generality level, exceeding the ≥3 bar. The substance ChatGPT would supply (the Serre definition + its 1978 invariance under reformulation, for arbitrary profinite abelian `G`) is independently confirmed verbatim by rows 1–3 and 10. |
| 5 | Local references (`refs/PadicLFunctions/`, `.mathlib-quality/references/`) | grep both | **n/a** | (neither directory present in this worktree; PDFs are local-only, never committed) | the in-file docstring cites **RJW §11.1 corollary, TeX 3033–3039**, and the source paper is arXiv:2309.15692 (now in *Essential Number Theory* 4(1), msp.org/ent/2025/4-1). Recorded n/a with reason. |
| 6 | nLab | `ncatlab.org/nlab/show/Iwasawa+algebra` (WebFetch) | **partial** | nLab *Iwasawa algebra* page defines `Λ(Γ) = ℤ_p[[Γ]] ≅ ℤ_p[[T]]` but has **no** pseudomeasure entry: "this page does not define pseudomeasure ... no discussion of pseudomeasures or p-adic zeta functions" | nLab has the ambient *framework* (Iwasawa algebra) but neither the pseudo-measure predicate nor this descent corollary. `ncatlab.org/nlab/show/pseudomeasure` is a 404 (confirmed in the parent-def report). |
| 7 | nCatLab (categorical) | (same as #6) | **n/a** | — | pseudo-measure / its plus-part descent is an Iwasawa-theory / commutative-algebra notion, not a categorical one; no universal-property reformulation. Recorded n/a with reason. |
| 8 | Stacks Project | total ring of fractions / completed group ring | **n/a** | Stacks has `Q(A) = S⁻¹A` (the ambient ring, relevant only to `QuotientFieldPlus`) but **no** pseudo-measure, Iwasawa-algebra-of-measures, or p-adic-zeta notion | Stacks is alg-geom / comm-alg; the Iwasawa-theory object is out of its scope. Recorded n/a with reason. |
| 9 | MathOverflow / Math.SE | folded into rows 1–3 (result sets surfaced MO/MSE threads on pseudomeasures + plus/minus parts) | **partial** | reaffirms the framework; no thread isolates "ζ_p⁺ is a pseudo-measure on ℤ_p^×/{±1}" as a standalone citable theorem (it is the well-known descent, stated inside the construction) | the descent is textbook Iwasawa theory; no open MO question to resolve. |
| 10 | recent arXiv (≤5 yr) | rows 1–3 surfaced 2309.15692 (2023, the source), 0711.0581, 1004.2578, 1001.2091, 0711.0589, 0908.2178, 0802.2272 | **yes** | all use the identical Serre form "`(g−1)φ ∈ Λ(G)` ∀g"; the *non-abelian* pseudomeasure papers (Ritter–Weiss 1004.2578, Kakde-style 0711.0581) descend/inflate pseudomeasures along quotients `G ↠ G/H` exactly as this corollary does for `𝒢 ↠ 𝒢⁺` | modern work only varies notation / adds non-abelian generality; the abelian plus-part descent here is the classical case. |

### Literature summary (Phase 3)

- **Concept identified as:** the **plus-part descent of the Kubota–Leopoldt p-adic zeta
  pseudo-measure** — RJW Corollary 11.4 (arXiv:2309.15692 §11.1, TeX 3033–3039): "ζ_p
  descends to a pseudo-measure on `𝒢⁺ = ℤ_p^×/{±1}`". The *pseudo-measure* notion is
  Serre (1978), as used by Coates, Coates–Lichtenbaum, Coates–Sujatha (*Cyclotomic Fields
  and Zeta Values*, 2006), and Deligne–Ribet.
- **Sources agree on the standard form:** **yes** — the pseudo-measure definition is
  unanimous and verbatim ("`(g−1)f ∈ Λ(G)` ∀g", for an *arbitrary* profinite abelian `G`),
  and the descent of a pseudo-measure along a Galois quotient `G ↠ G/H` is a standard,
  classical move (it is precisely how one passes to the plus part for the Main Conjecture
  of totally real fields).
- **Most general standard form:** for an **arbitrary** profinite abelian `G`, a quotient
  `π : G ↠ Q`, and a pseudo-measure `λ ∈ Q(Λ(G))`, the pushforward `π_*λ` is a pseudo-measure
  on `Q` (under the relevant invariance — here c-invariance kills the kernel `⟨c⟩`). The
  theorem here is the **single instance** `G = ℤ_p^×`, `Q = ℤ_p^×/{±1}`, `λ = ζ_p`.
- **Generality dimensions where the literature varies:**
  - the group/quotient: `ℤ_p^× ↠ ℤ_p^×/{±1}` here; the general theory descends along *any*
    Galois quotient (and, in Ritter–Weiss/Kakde, non-abelian `G`). That generality is the
    generality of the *whole pseudo-measure apparatus*, which mathlib lacks entirely.
  - the L-function: `ζ_p` here; the analogous descent holds for Dirichlet/Hecke p-adic
    L-functions, again only meaningful once the apparatus exists.
- **Disagreement with the literature:** **none.** The Lean theorem faithfully encodes a true,
  standard, named result (RJW Corollary 11.4).

The literature search returned the *exact* result (a named corollary in the source, an
instance of a classical descent), not nothing. Per the verdicts reference, an empty Phase 3
would push toward BORDERLINE/NO; a *non-empty* Phase 3 that names a real result phrased over
an apparatus mathlib lacks is the "the unit of mathlib-worthiness is the apparatus" situation —
which, combined with the parent def being `YES-but-generalise-first`, drives Phase 7.

## Phase 4 — Generality analysis

Literature-standard form (from Phase 3): descent of a pseudo-measure along a Galois quotient,
for an **arbitrary** profinite abelian `G ↠ Q`; the theorem here fixes `G = ℤ_p^×`,
`Q = ℤ_p^×/{±1}`, `λ = ζ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `(p : ℕ) [Fact p.Prime]`, `(hp2 : p ≠ 2)` | odd prime | odd prime (the whole §11 hypothesis) | **NO** | the plus/minus splitting and the order-2 `⟨−1⟩` structure require `p` odd / `2` invertible; intrinsic, not slack. |
| 2 | the conclusion predicate is `IsPlusPseudoMeasure` over the **fixed** group `GPlus p` | pseudo-measure on `ℤ_p^×/{±1}` | pseudo-measure on an **arbitrary** compact commutative `G` | **yes (inherited)** | the *parent def* `IsPlusPseudoMeasure` is already `YES-but-generalise-first` — it should be the group-abstract `IsPseudoMeasure {G} (q : FractionRing (PadicMeasure p G))`. Once the def is abstracted (merging the `ℤ_p^×` and `ℤ_p^×/{±1}` copies), this theorem is restated against the instantiation `G := GPlus p`. |
| 3 | the descended object is the **specific** `padicZetaPlus` | ζ_p⁺ | the pushforward `π_*λ` of any (c-invariant) pseudo-measure `λ` along a quotient `π` | yes, in principle | the proof structure (`obtain witness; push forward; certify via `projPlus_padicZeta_witness`) is exactly a *general descent-along-a-quotient* lemma specialised to `λ = ζ_p`, `π = projPlus`. The abstract statement "the pushforward of a pseudo-measure along `π : Λ(G) →+* Λ(Q)` whose kernel is killed is a pseudo-measure on `Q`" is strictly more reusable — but it is a **project-internal** abstraction over objects (`PadicMeasure`, `projPlus`, `IsPseudoMeasure`) that **mathlib does not have at all**. |
| 4 | ambient `padicZeta_isPseudoMeasure` (RJW Prop. 4.11) | ζ_p is a pseudo-measure on `𝒢` | (same, arbitrary `G`) | yes (inherited) | the 𝒢-side input shares the same `IsPseudoMeasure` predicate; it is the byte-analogous sibling that the group-abstraction merges with this one. |

**Crucial cross-check — the sibling on `𝒢`.** `padicZeta_isPseudoMeasure`
(`KubotaLeopoldt/ZetaP.lean:269`, RJW Prop. 4.11) is the **identical-shape theorem over
`G = ℤ_[p]ˣ`**: "ζ_p is a pseudo-measure on `𝒢`". The project carries the "ζ is a
pseudo-measure" result twice — once on `ℤ_p^×` (Prop. 4.11) and once on `ℤ_p^×/{±1}`
(this corollary) — mirroring the byte-for-byte duplication the parent-def report flagged
(`IsPseudoMeasure` vs `IsPlusPseudoMeasure`). The group-abstract refactor would let the
descent be a *single* lemma about `π_*` of a pseudo-measure, with both `ζ_p` and `ζ_p⁺` as
instances.

### Generality verdict (Phase 4b)

**The current form is: STRICTLY NARROWER THAN STANDARD** — but the narrowing axes (2/3/4)
are all **inherited from the parent predicate** `IsPlusPseudoMeasure` (whose own verdict is
`YES-but-generalise-first`) and from the absent abstract descent lemma. There is **no
mathlib-targeted generalisation of this theorem in isolation**, because every object it
quantifies over (`padicZetaPlus`, `projPlus`, `IsPlusPseudoMeasure`, `GPlus`) is project-local
and missing from mathlib.

**Number of weakening opportunities found: 1 substantive** (abstract the group + state the
descent for `π_*` of a general pseudo-measure; axes 2/3/4 collapse to this one move) — but it
is a **project-internal** abstraction that presupposes the whole apparatus, not a standalone
mathlib generalisation.

**Cost of the (project-internal) restatement: CHEAP** — the ring, `dirac`, `projPlus`,
`FractionRing` are already general in `G`; abstracting is a signature edit. (Cost does not
affect the bucket per the skill; noted for completeness.)

### Phase 4c — Modern-mathlib-idiom restatement (Bourbaki 2.0 check)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let G be a foo" preamble → typeclass / abstract parameter? | **yes (inherited)** | conclude `IsPseudoMeasure (G := GPlus p) p (padicZetaPlus …)` against the *group-abstract* predicate (the parent-def generalisation) rather than the hard-coded `IsPlusPseudoMeasure` | the descent corollary stops being a `GPlus`-specific theorem; it becomes "`ζ_p⁺` is a pseudo-measure" stated against the one abstract predicate that also covers `padicZeta_isPseudoMeasure`. |
| 2 | sequences/metric → filters/topological? | no | — | the statement is a purely algebraic membership (`([ḡ]−1)·ζ_p⁺ ∈ Λ(𝒢⁺)`); no metric/sequence content. |
| 3 | construct an object → universal-property class? | **partial** | the proof *is* a descent-along-a-quotient construction; the modern form is a general lemma "`π_*` of a pseudo-measure is a pseudo-measure on the quotient (when `ker π_*` is annihilated)", consumed here at `π = projPlus`, `λ = ζ_p` | a reusable `IsPseudoMeasure.map`/`.descend` lemma; but it lives in the (absent) Iwasawa layer, so it is a follow-up *inside* the upstreaming program, not a standalone mathlib idiom realisable today. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no subset/closure predicate in the statement. |
| 5 | vector-space/field-specific → weaken typeclasses? | **yes (inherited)** | the group `GPlus p` is the "field-specific" datum; weakening to abstract `G` is the parent-def move | results proved for abstract `G` specialise to every Galois group with no re-proof. |
| 6 | 1-categorical → higher-categorical? | no | — | no categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary structure? | **yes (inherited)** | `Q = ℤ_p^×/{±1}` (a concrete quotient) → arbitrary quotient `G ↠ Q` | matches the literature's "descend along any Galois quotient" and the non-abelian pseudomeasure papers. |

**Modern-idiom verdict (Phase 4c): yes, but inherited and apparatus-bound.** The real
modernisation (group-abstract predicate + a general `IsPseudoMeasure.descend` lemma) is
genuine and has a concrete downstream (one predicate + one descent lemma covering both
`ζ_p` and `ζ_p⁺`), **but it is owned by the parent def's generalisation and presupposes the
absent Iwasawa-of-measures foundation** — it is not a reformulation this theorem can undergo
on its own against existing mathlib API (there is no existing API). So Phase 4c does **not**
by itself flip this to a clean `YES-but-generalise-first`; it confirms the narrowing is real
but inherited.

## Phase 4.5 — Diamond / defeq risk

**n/a** — declaration kind is **theorem**. It introduces no definitional equalities, no
instances, no typeclass-search targets, no coercions. Phase 4.5 skipped (no `def`/`class`/
`instance`).

## Phase 5 — Mathlib five-method search

Searched on (a) the user's form (ζ_p⁺ is a pseudo-measure on `𝒢⁺`), (b) the literature-standard
form (descent of a pseudo-measure along a Galois quotient, arbitrary `G`), and (c) the ambient
infrastructure (pseudo-measure predicate, Iwasawa algebra `ℤ_p[[G]]` as a measure ring,
completed group ring, p-adic zeta function).

### Mathlib search-status: `PadicMeasure.isPlusPseudoMeasure_padicZetaPlus`

| Method | Query | Result |
|---|---|---|
| [A] Lean-Finder (AI/NL) | "p-adic zeta function is a pseudo-measure on a Galois group quotient", "descend pseudomeasure along group quotient Iwasawa" | **n/a / no hit** — Lean-Finder MCP not available this session; the natural-language target has no mathlib analog (no pseudo-measure theory — see [D]/[E]). |
| [B] Loogle (type pattern) | predicates of shape `IsPseudoMeasure _ (… : FractionRing (PadicMeasure _ _))`; `_ → IsPseudoMeasure _ _` | **n/a / no hit** — Loogle MCP not available; the head symbols (`IsPlusPseudoMeasure`, `padicZetaPlus`, `PadicMeasure`, `GPlus`) are project-local and would return nothing. |
| [C] LeanSearch (NL) | "p-adic L-function as a measure on a Galois group", "pseudomeasure plus part" | **n/a / no hit** — LeanSearch MCP not available; the concept is absent from mathlib (returns measure-theory `Measure`, unrelated). |
| [D] Grep mathlib src | `grep -rli "pseudomeasure\|pseudo_measure\|PseudoMeasure"`; `find -iname "*iwasawa*"`; `grep "completedGroupAlgebra\|CompletedGroupRing"`; `grep "padicZeta"` over `…/packages/mathlib/Mathlib/` | **no hit.** `pseudomeasure`: **0** files. `IsPseudoMeasure`: **0**. `completedGroupAlgebra`/`CompletedGroupRing`: **0**. `padicZeta`: 0. The only `*iwasawa*` file is `GroupTheory/GroupAction/Iwasawa.lean` (the *Iwasawa simplicity criterion* — entirely unrelated). |
| [E] Name pattern (local + mathlib) | `isPlusPseudoMeasure_padicZetaPlus`, `IsPlusPseudoMeasure`, `padicZetaPlus`, `padicZeta_isPseudoMeasure`, `projPlus` | present **only** in this project; **absent** from mathlib. |

**Searched for both forms:** yes — the user's `𝒢⁺` form, the literature-standard
descent-along-a-quotient form, *and* all supporting infrastructure (pseudo-measure predicate /
Iwasawa-of-measures ring / completed group ring / p-adic zeta). Mathlib has **none** of it.

**Concluded: not in mathlib** (all five methods exhausted; the MCP search tools were
unavailable this session but the grep + name-pattern evidence over the full vendored mathlib
tree is conclusive — mathlib has no pseudo-measure theory, no Iwasawa algebra of measures, no
`padicZeta`, no plus-part quotient). There is **no existing decl to specialise from** and **no
`D'` to re-aim at** (the Re-aim rule does not engage, because there is no mathlib parent object).

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `isPlusPseudoMeasure_padicZetaPlus`

- **Internal use count: 0** within `.lean` source *files* (excluding the declaring line); the
  only `.lean` occurrences of the name are the module-docstring "Main declarations" bullet
  (`ZetaGalois.lean:18`) and the declaration itself (`:240`).
- **External-to-file callers: 0** (no other `.lean` file references it yet).
- It *is* the **raison d'être of the parent def** `IsPlusPseudoMeasure` (which exists precisely
  so this corollary can be stated), and the named §11.1 corollary the §12 Iwasawa-theorem
  statements are intended to consume.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| (none in `.lean` source) | the result is the headline corollary; downstream §12 consumers are planned but not yet present in committed source. |

Inline-derivation grep (was the statement re-derived elsewhere without the name?): **none** —
but the **structurally identical** result is the *separate theorem* `padicZeta_isPseudoMeasure`
over `ℤ_[p]ˣ` (`ZetaP.lean:269`), which is the duplication Phase 4 flagged, not an inline bypass.

**What the pattern tells you.** K = 0 current `.lean` call sites would, in isolation, read as a
"dead code / wrong abstraction" signal. **But** unlike the genuinely-orphaned, superseded
`padicZeta_witness_neg` (which has a *used* replacement), this theorem is **not superseded** —
it is the named headline corollary itself (RJW Corollary 11.4), the unique payoff of the
`padicZetaPlus` def and the `IsPlusPseudoMeasure` predicate, the §11.1 result the file is named
for. So the correct reading is **not** "inline/delete"; it is "this is the central result, but
it is stated over an apparatus mathlib lacks and against a predicate that itself needs
generalising first" — which is the BORDERLINE reading, reinforced by the existence of the
`padicZeta_isPseudoMeasure` twin.

### Composition check (Phase 6)

Can `isPlusPseudoMeasure_padicZetaPlus` be **derived from mathlib** in ≤3 chained calls? **No.**

- **Attempt 1 — the proof body as a composition:** the body is
  `intro; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gPlus; obtain ⟨ν, hν⟩ :=
  padicZeta_isPseudoMeasure …; exact ⟨projPlus p ν, projPlus_padicZeta_witness …⟩`. Of these,
  **only `QuotientGroup.mk_surjective` is a mathlib decl**; `padicZeta_isPseudoMeasure` (RJW
  Prop. 4.11) and `projPlus_padicZeta_witness` are **project-local theorems**, each with its
  own nontrivial proof (the latter cancels a unit in the localization and pushes a witness
  identity through `projPlus`). This is "a proof, not a composition" — it composes *project*
  theorems, not mathlib decls.
- **Attempt 2 — mathlib has the predicate / a parent to specialise:** fails. Phase 5 found no
  pseudo-measure notion, no Iwasawa-of-measures ring, no `padicZeta`, no plus-part quotient.
  There is nothing in mathlib to compose *from*.

**Conclusion: NOT-COMPOSABLE** (from mathlib). The result genuinely depends on the project-local
`padicZeta_isPseudoMeasure` and `projPlus_padicZeta_witness`; mathlib supplies only the final
surjectivity lift.

## Phase 7 — Verdict synthesis (gate)

### Verdict: `PadicMeasure.isPlusPseudoMeasure_padicZetaPlus`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Literature search (Phase 3):** the result is **RJW Corollary 11.4** — the plus-part descent
  of the Kubota–Leopoldt p-adic zeta pseudo-measure, an instance of the classical Serre/Coates
  descent of pseudo-measures along a Galois quotient (`Γ/⟨c⟩ ≅ ℤ_p^×/{±1}`), and the
  foundational object of the Iwasawa Main Conjecture for totally real fields. 5 channels hit
  (WebSearch ×3, arXiv, nLab-framework); ChatGPT-MCP/nCatLab/Stacks/MO recorded n/a with reasons.
- **Generality analysis (Phase 4):** **STRICTLY NARROWER THAN STANDARD**, but the narrowing
  (group, descended object, ambient predicate) is **inherited** from the parent def
  `IsPlusPseudoMeasure` (itself `YES-but-generalise-first`) and from an absent abstract
  descent lemma — a *project-internal* generalisation that presupposes the whole apparatus,
  not a standalone mathlib generalisation. A byte-analogous twin `padicZeta_isPseudoMeasure`
  over `ℤ_[p]ˣ` already exists.
- **Mathlib search (Phase 5):** **not in mathlib** under either form; zero pseudo-measure /
  Iwasawa-of-measures / `padicZeta` / plus-part hits — nothing to specialise from, no `D'` to
  re-aim at.
- **Composition check (Phase 6):** **NOT-COMPOSABLE** from mathlib — the proof composes the
  project-local `padicZeta_isPseudoMeasure` + `projPlus_padicZeta_witness`; mathlib supplies
  only `QuotientGroup.mk_surjective`. **Call sites: K = 0** current `.lean` consumers, but the
  theorem is the *named headline corollary* (not superseded, unlike `padicZeta_witness_neg`).

**Rationale.**
This theorem clears the three "real / novel-for-mathlib / not-trivially-composable" bars: it is
a genuine, named, classical result (RJW Corollary 11.4); it is **not** in mathlib (mathlib has
none of the pseudo-measure / Iwasawa-of-measures / p-adic-zeta apparatus it is phrased in); and
it is **not** a 1–3 line mathlib composition (its engine is two project-local theorems). That
rules out both NO buckets: there is no mathlib decl to cite for `NO-mathlib-has-it`, and no
≤3-call mathlib composition for `NO-composable`. So it is a genuine YES-or-BORDERLINE.

It is **not a confident YES**, for two compounding reasons the skill cannot resolve from the
evidence alone. **(i) Apparatus precedence.** The theorem sits atop the entire `padicZeta` /
pseudo-measure / Iwasawa-algebra-of-measures foundation (`PadicMeasure`, `dirac`,
`QuotientField`, `IsPseudoMeasure`, `padicZeta`, `padicZeta_isPseudoMeasure`, `GPlus`,
`projPlus`, `projPlus_padicZeta_witness`), none of which is in mathlib. One cannot ship a
single descent corollary ahead of that foundation; the real "should mathlib have this?" unit is
the *whole apparatus*, a large multi-file upstreaming program — exactly the recurring question
the sibling reports (`dirac_neg_one_sub_one_mul_padicZeta`, `twistedZetaHalf_isTwistedPseudoMeasure`,
`padicZeta_witness_neg`) all surfaced and could not self-resolve. **(ii) Inherited generality
debt.** Even granting the foundation, the theorem's *parent predicate* `IsPlusPseudoMeasure` is
`YES-but-generalise-first` — it must first be abstracted to a single group-abstract
`IsPseudoMeasure {G}` (merging the `ℤ_p^×` and `ℤ_p^×/{±1}` copies), and the descent itself is
most reusably a general `IsPseudoMeasure.descend` lemma with `ζ_p ↦ ζ_p⁺` as one instance. How
to sequence and restate the corollary against that abstracted predicate is a judgment call.
Per the verdict gate: `YES-add-as-is` is rejected because Phase 4b is STRICTLY NARROWER (with
real inherited weakenings); a clean `YES-but-generalise-first` is not assertable either, because
the generalisation is not a self-contained restatement of *this* theorem but a consequence of
generalising the parent def and building an absent abstract descent lemma — and, more
fundamentally, the prior question (does mathlib want the foundation at all?) is unanswered. When
the synthesis of Phases 3–6 hinges on mathlib-scope taste (upstream the KL/Iwasawa tower?) and a
generalisation-sequencing decision that cannot be grounded in the evidence, the bucket is
**BORDERLINE-needs-human**. This is consistent with every sibling headline-`ζ_p` report's verdict.

**Refactor-actionable bar — BORDERLINE-needs-human. Numbered questions (each yes/no or short):**

1. **Is the plan to upstream the project's entire Kubota–Leopoldt / pseudo-measure /
   Iwasawa-algebra-of-measures foundation to mathlib** (`PadicMeasure`, the convolution
   `CommRing`, `dirac`, `QuotientField`, `IsPseudoMeasure`, `padicZeta`,
   `padicZeta_isPseudoMeasure`, `GPlus`, `projPlus`, `projPlus_padicZeta_witness`)? If **no**,
   this corollary is automatically out of scope — it cannot exist in mathlib without that
   foundation — and should stay project-local.

2. If the foundation is upstreamed: it depends on the parent def `IsPlusPseudoMeasure`, which is
   itself `YES-but-generalise-first`. **Should this corollary be restated against the single
   group-abstract `IsPseudoMeasure {G}` predicate** (so that `padicZeta_isPseudoMeasure` on
   `ℤ_p^×` and this result on `ℤ_p^×/{±1}` are two instances of one statement), rather than the
   `GPlus`-specific `IsPlusPseudoMeasure`?

3. **Should the descent be factored as a general, reusable lemma** —
   "`π_*` of a pseudo-measure on `G` is a pseudo-measure on the quotient `Q` (when `ker π_*` is
   annihilated)" — with `isPlusPseudoMeasure_padicZetaPlus` as its `(λ = ζ_p, π = projPlus)`
   instance? This is the literature's native generality (descent along any Galois quotient;
   cf. the non-abelian pseudomeasure papers) and the modern-idiom form Phase 4c identified.

4. **Does mathlib's roadmap actually want Kubota–Leopoldt p-adic L-function / Iwasawa Main
   Conjecture infrastructure at this granularity**, or is this research-frontier material that
   should mature in AINTLIB first? This is a mathlib-community scope/taste call the skill cannot
   make.

**Next action:** user answers (Q1 is pivotal). Likely outcomes:
  - **Foundation not upstreamed (Q1 = no)** → drop from mathlib consideration; keep project-local.
  - **Foundation upstreamed + abstract predicate/descent (Q2/Q3 = yes)** → re-run `/mathlibable`
    with the group-abstract `IsPseudoMeasure.descend` restatement as a Phase-1 input; this corollary
    would then ride along as the `λ = ζ_p` instance, likely `YES-but-generalise-first` *relative to
    the apparatus* (generalise the parent def + factor the descent lemma first).
  - **Foundation upstreamed but corollary kept as the only public payoff** → ships folded into the
    abstract descent lemma; the parent def and the `ℤ_p^×`-side twin are generalised first via
    `/generalise PadicMeasure.IsPlusPseudoMeasure`.

### Pre-PR checklist (only if Q1 = "yes, upstream the foundation")
- [ ] Upstream the KL / pseudo-measure / Iwasawa-of-measures **foundation** as a coherent
      multi-file program (this corollary is a late, headline node — not a standalone PR).
- [ ] First `/generalise PadicMeasure.IsPlusPseudoMeasure` → one group-abstract `IsPseudoMeasure {G}`
      (merge the `ℤ_p^×` / `ℤ_p^×/{±1}` copies), then factor a general `IsPseudoMeasure.descend`.
- [ ] Restate this corollary against the abstract predicate + descent lemma; `/cleanup` before PR.
- [ ] Pick a `Mathlib/NumberTheory/` (Iwasawa-theory) reviewer.

## Phase 8 — Report (this document)

**Five-bucket verdict (final): `BORDERLINE-needs-human`**

- **What it is:** RJW Corollary 11.4 — ζ_p descends to a pseudo-measure on `𝒢⁺ = ℤ_p^×/{±1}`;
  a genuine, named, classical Iwasawa-theory result.
- **Why not a NO:** mathlib has **none** of the apparatus (no pseudo-measure, no Iwasawa-of-measures
  ring, no `padicZeta`, no plus-part quotient) — nothing to cite (`NO-mathlib-has-it` fails) and
  nothing to compose from (`NO-composable` fails; the proof composes two *project* theorems).
- **Why not a confident YES:** (i) it cannot ship ahead of the entire absent KL/Iwasawa foundation
  it sits atop — the real mathlib-worthiness unit is that foundation, a large upstreaming program
  (a recurring, unresolved scope question across all sibling reports); and (ii) its parent predicate
  `IsPlusPseudoMeasure` is itself `YES-but-generalise-first`, so the corollary should be restated
  against a group-abstract predicate + a general descent lemma — a sequencing/taste judgment the
  evidence cannot settle.
- **Risk:** n/a (theorem — Phase 4.5 skipped).
- **Cost:** the (project-internal, apparatus-bound) generalisation is CHEAP; does not affect the bucket.

---

## Next step

User answers the four numbered questions (Q1 — upstream the KL / pseudo-measure / Iwasawa-algebra
foundation at all? — is pivotal; a **no** makes this corollary out of scope). If the foundation is
in scope, first `/generalise PadicMeasure.IsPlusPseudoMeasure` to one group-abstract
`IsPseudoMeasure {G}` and factor a general `IsPseudoMeasure.descend` lemma, then re-run
`/mathlibable` on this corollary as the `λ = ζ_p` instance. Do **not** PR
`isPlusPseudoMeasure_padicZetaPlus` as a standalone `GPlus`-specific theorem ahead of its foundation.
