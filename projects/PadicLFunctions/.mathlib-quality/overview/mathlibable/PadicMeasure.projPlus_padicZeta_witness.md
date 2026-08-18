# `/mathlibable` report — `PadicMeasure.projPlus_padicZeta_witness`

> Mode A (single declaration) — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-20. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> The **mathematics** is classical and canonical: the Kubota–Leopoldt p-adic zeta function `ζ_p`
> **descends to a pseudo-measure on the plus part** `𝒢⁺ = ℤ_p^×/{±1}`. This is *exactly* RJW
> (arXiv:2309.15692) §11.1 — read verbatim: Lemma 11.2 (`Λ(Γ)⁺ ≅ Λ(Γ⁺)`), Lemma 11.3 (the
> odd-moment membership criterion), and **Corollary 11.4** ("The p-adic zeta function is a
> pseudo-measure on `Γ⁺`"). **But this specific Lean theorem — the *compatibility of the descent*:
> pushing a 𝒢-side witness `ν` of `([g]−1)·ζ_p` forward along the natural surjection
> `π_* : Λ(𝒢) → Λ(𝒢⁺)` yields the 𝒢⁺-side witness `([ḡ]−1)·ζ_p⁺ = π_*(ν)` at the image group
> element — is NOT stated anywhere in the literature.** It is the *formalization overhead* of the
> source's one-line proof: RJW "freely identifies `Λ(Γ⁺)` with the submodule `Λ(Γ)⁺` of `Λ(Γ)`"
> (Lemma 11.2) and then asserts Corollary 11.4 in a single line, leaving the witness-pushforward
> compatibility entirely implicit. The Lean development, which works with a genuine *pushforward
> ring hom* `projPlus` rather than the silent identification, has to discharge that compatibility
> explicitly — and that is what this theorem is. It is stated entirely over a project-local Iwasawa
> tower (`PadicMeasure`, `QuotientField`/`QuotientFieldPlus`, `padicZeta`/`padicZetaPlus`, `projPlus`,
> `toQPlus`, `zetaNum`, `dirac`, the augmentation/non-zero-divisor apparatus), **none of which exists
> in mathlib** (confirmed exhaustively by grep over the vendored mathlib tree). So all four mechanical
> buckets fail their gates: nothing in mathlib to specialise from (NO-mathlib-has-it); no ≤3-call
> mathlib composition for the localization-pushforward-cancellation argument (NO-composable — the
> ~40-line proof consumes the whole project tower); and the lemma cannot be shipped ahead of its
> entire foundation (the YES buckets). Unlike its **dead** sibling `padicZeta_witness_neg` (K = 0),
> this lemma is **load-bearing**: K = 2 essential same-file consumers
> (`isPlusPseudoMeasure_padicZetaPlus` = Corollary 11.4 itself, and `zetaIdealPlus_eq_span`). Whether
> the whole foundation should go to mathlib, and whether this compatibility lemma deserves a public
> mathlib home or stays an internal step, are taste/policy judgments the skill cannot ground in the
> evidence. Numbered questions for the user are in Phase 7. This is the **same situation** as the
> sibling reports `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta.md`,
> `PadicMeasure.padicZeta_witness_neg.md`, and `PadicMeasure.padicZeta_odd_moment_eq_zero.md` in this
> directory.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD NOTE —
  `lake build` is stale/slow in this checkout). The declaration and its full dependency chain were
  read directly from source, exactly as the skill's Phase-0 fallback allows.
- decl `PadicMeasure.projPlus_padicZeta_witness`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:190`
- kind:                      theorem
- has sorry:                 **no** — `grep -nE "sorry|admit"` returns nothing for `ZetaGalois.lean`.
  The declaration and every dependency are complete and sorry-free (dependency files
  `Iwasawa/PlusPart.lean`, `KubotaLeopoldt/ZetaP.lean`, `Measure/Basic.lean`,
  `Measure/PseudoMeasure.lean` likewise have no `sorry` in the relevant decls).
- module docstring summary:  "ζ_p as a pseudo-measure on `𝒢⁺` and the ideal `I(𝒢)ζ_p`"
  (RJW arXiv:2309.15692 §11.1 corollary + §11.2, on the identified Galois side `𝒢⁺ = GPlus p`).
  The file proves the odd moments of `ζ_p` vanish, deduces c-invariance `([−1]−[1])·ζ_p = 0`,
  **descends `ζ_p` to a pseudo-measure on `𝒢⁺` — this theorem is the descent-compatibility step** —
  and builds the ideals `I(𝒢)ζ_p` / `I(𝒢⁺)ζ_p`.

```lean
/-- Compatibility of the descents: pushing a 𝒢-side witness forward gives the
𝒢⁺-side witness at the image group element — "ζ_p descends". -/
theorem projPlus_padicZeta_witness (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    toQPlus p (dirac p (QuotientGroup.mk g : GPlus p) - 1) * padicZetaPlus p hp2
      = toQPlus p (projPlus p ν) := by ...
```

Dependency closure read from source (all the carrying symbols):
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — the Iwasawa algebra
  `Λ(X)` as ℤ_p-valued p-adic measures (RJW Def. 3.6). **Project-local.**
- `dirac p x` (`Measure/Basic.lean:64`) — the Dirac/group-like element `[x]`. **Project-local.**
- `QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` (`Measure/PseudoMeasure.lean:804`) — the
  total fraction ring `Q(𝒢) = Q(ℤ_p^×)`. **Project-local.**
- `QuotientFieldPlus p := FractionRing (PadicMeasure p (GPlus p))` (`ZetaGalois.lean:124`) —
  `Q(𝒢⁺)`. **Project-local.**
- `toQPlus p` (`ZetaGalois.lean:129`) — the structure map `Λ(𝒢⁺) → Q(𝒢⁺)` (a named `algebraMap`).
  **Project-local.**
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1)` (`Iwasawa/PlusPart.lean:215`) — `𝒢⁺ = ℤ_p^×/{±1}`.
  **Project-local construction over a mathlib quotient group.**
- `projPlus p : Λ(𝒢) →+* Λ(𝒢⁺)` (`Iwasawa/PlusPart.lean:224`) — the pushforward `π_*` along the
  quotient projection (RJW Lemma 11.2's "natural surjection"). **Project-local.**
- `padicZeta p hp2 : QuotientField p` (`KubotaLeopoldt/ZetaP.lean:252`) — `ζ_p` (RJW Def. 4.10).
  **Project-local.**
- `padicZetaPlus p hp2 : QuotientFieldPlus p` (`ZetaGalois.lean:177`) — `ζ_p⁺`, constructed as
  `IsLocalization.mk' (projPlus(zetaNum a)) ([ā]−1)`. **Project-local (RJW Corollary 11.4 object).**
- `zetaNum p m` (`KubotaLeopoldt/ZetaP.lean:74`), `exists_nat_topological_generator`
  (`:124`), `topGen_pow_ne_one` (`:102`), `dirac_sub_one_mem_nonZeroDivisors`
  (`Measure/PseudoMeasure.lean:788`), `dirac_mk_sub_one_mem_nonZeroDivisors` (`ZetaGalois.lean:140`),
  `projPlus_dirac` (`Iwasawa/PlusPart.lean:242`) — **all project-local.**
- **Mathlib decls actually used** (the only ones): `IsFractionRing.injective`
  (`RingTheory/Localization/FractionRing.lean:137`), `IsLocalization.mk'_spec'` /
  `IsLocalization.mk'_spec` (`RingTheory/Localization/Defs.lean:271`/`:267`),
  `IsLocalization.map_units` (`RingTheory/Localization/Defs.lean:127`), plus generic ring/hom glue
  (`map_mul`, `map_sub`, `map_one`, `ring`, `linear_combination`, `congrArg`, `IsUnit.mul_left_inj`).

---

### Statement (Phase 1)

`PadicMeasure.projPlus_padicZeta_witness` is **a theorem** stating the following:

Let `p` be an odd prime, let `g ∈ ℤ_p^×` (a group element of `𝒢 = ℤ_p^×`), and let `ḡ` be its image
in the plus-part quotient `𝒢⁺ = ℤ_p^×/{±1}`. The Kubota–Leopoldt p-adic zeta function `ζ_p` is a
*pseudo-measure* on `𝒢` — an element of the total fraction ring `Q(𝒢)` of the Iwasawa algebra
`Λ(𝒢)` — and it **descends** to a pseudo-measure `ζ_p⁺` on `𝒢⁺` (RJW Corollary 11.4). The descent is
realised concretely by the pushforward ring hom `π_* = projPlus : Λ(𝒢) → Λ(𝒢⁺)` along the quotient
projection. The theorem asserts the **compatibility of the two descents**: if `ν ∈ Λ(𝒢)` is a witness
of `([g]−[1])·ζ_p` on the 𝒢-side (i.e. `algebraMap(([g]−[1]))·ζ_p = algebraMap ν` in `Q(𝒢)`), then
its pushforward `π_*(ν)` is a witness of `([ḡ]−[1])·ζ_p⁺` on the 𝒢⁺-side:

  `([ḡ]−[1]) · ζ_p⁺ = π_*(ν)`  in `Q(𝒢⁺)`.

In words: "pushing a 𝒢-side witness forward gives the 𝒢⁺-side witness at the image group element" —
the precise sense in which "`ζ_p` descends". The proof: pull the 𝒢-side witness identity and the
defining relation `([u]−1)·ζ_p = zetaNum(m)` back to genuine identities in `Λ(ℤ_p^×)` (via injectivity
of `Λ(𝒢) ↪ Q(𝒢)`), obtaining `([u]−1)·ν = ([g]−1)·zetaNum(m)`; apply the ring hom `π_*`
(`congrArg projPlus`) to get `([ḡ]−1)·π_*(zetaNum m) = ([ū]−1)·π_*(ν)`; then, since `ζ_p⁺` is by
definition `mk'(π_*(zetaNum m))([ū]−1)` and the image of the denominator `([ū]−1)` is a unit in the
localization (`IsLocalization.map_units`), cancel that unit and conclude by `linear_combination` on
the pushed-forward identity. `u` here is the *integer topological generator* packed inside the
definitions of both `padicZeta` and `padicZetaPlus` (`exists_nat_topological_generator`), so the two
denominators match.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime; the whole development is `noncomputable` over `ℚ_[p]`.
- `(hp2 : p ≠ 2)` — odd prime (needed for `padicZeta`'s construction and for the `Λ(Γ) = Λ⁺ ⊕ Λ⁻`
  parity splitting / `⟨−1⟩` order-2 structure — RJW Lemma 11.1).
- `(g : ℤ_[p]ˣ)` — a p-adic unit (group element of `𝒢`).

Hypotheses (Lean side):
- `{ν : PadicMeasure p ℤ_[p]ˣ}` (implicit) — a measure.
- `hν : algebraMap _ (QuotientField p) ([g]−1) · ζ_p = algebraMap _ _ ν` — `ν` witnesses the
  g-twist of `ζ_p` on the 𝒢-side (this is exactly the data the pseudo-measure property supplies).

Conclusion (math): the pushforward `π_*(ν)` is the 𝒢⁺-side witness of `([ḡ]−1)·ζ_p⁺`.

Conclusion (Lean):
`toQPlus p (dirac p (QuotientGroup.mk g : GPlus p) - 1) * padicZetaPlus p hp2 = toQPlus p (projPlus p ν)`,
an equation in the fraction ring `QuotientFieldPlus p = FractionRing (PadicMeasure p (GPlus p))`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: it is a *compatibility / glue lemma* — the descent-compatibility step underpinning the named
result (RJW Corollary 11.4 = `isPlusPseudoMeasure_padicZetaPlus`). It is *not* a new mathematical
structure (no `def`/`class`), and it is not itself a headline `## Main declarations` bullet of the
file (the bullets name `padicZetaPlus`, `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdeal`/`zetaIdealPlus`;
this theorem is the load-bearing infrastructure underneath the first two). The "named result" it
serves — Corollary 11.4 — *is* canonical; this particular pushforward-compatibility lemma is the
formalization scaffolding that makes the descent explicit.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and does
not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: **~40 substantive lines** — a genuine, multi-step proof:
`set m`/`set u` (unpack the packed generator) → `hspec` (defining relation of `padicZeta`) →
`hkey` (pull back to `Λ(ℤ_p^×)` via `IsFractionRing.injective`) → `hkeyP` (`congrArg projPlus`,
push forward) → `set c` (the denominator non-zero-divisor witness) → `hzp` (`padicZetaPlus = mk' … c`,
by `rfl`) → `hcunit` (`IsLocalization.map_units`) → unit-cancellation `rw` chain → `linear_combination hkeyP`.

One-liner verdict: **n/a** — kind is `theorem`/`lemma`, not `def`/`abbrev`/`structure`. The one-liner
exemption table does not apply. Phase 4.5 (diamond/defeq) is likewise n/a.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic zeta function descends pseudo-measure plus part G+ quotient Z_p^times mod ±1 Iwasawa" | yes (framework) | `ζ_p` descends to a pseudo-measure on `Γ⁺ = Γ/⟨c⟩ ≅ ℤ_p^×/{±1}` | top hits = **the source RJW lecture notes** (Warwick PDF) and **arXiv:2309.15692**; framework standard; the *witness-pushforward compatibility* lemma is **not** separately named anywhere |
| 2 | WebSearch (general form) | "pseudo-measure pushforward quotient group well-defined witness Iwasawa algebra fraction field compatibility" | partial | pseudo-measures = elements of `Frac(Λ(G))` (Coates); defined by Mellin transform extended to the fraction field by universality; quotient `Z_p[Γ_n] → Z_p[Γ_n^+]` induced by the projection | Sharifi/Ouyang Iwasawa notes, Venjakob structure theory; **none isolates** "pushing a witness `ν` of `([g]−1)ζ_p` forward gives the `([ḡ]−1)ζ_p⁺` witness" as a stated lemma — it is internal to descent arguments |
| 3 | WebSearch (named-after / aliases) | "Coates Wiles pseudo-measure zeta_p descends quotient Galois group complex conjugation Z_p^× mod ±1 corollary cyclotomic" | yes | **Coates–Sujatha** *Cyclotomic Fields and Zeta Values*: "the p-adic analogue of the zeta function `ζ_K(s)` should be a pseudo-measure on `Gal(K_{ab,p}/K)`"; descent treated as standard background | confirms the descent-to-`Γ⁺` is classical (Coates); the compatibility step is folklore book-keeping, never a citable named result |
| 4 | WebSearch (source-paper locate) | "Rodrigues Jacinto Williams introduction p-adic L-functions section 11 zeta_p descends pseudo-measure Gamma plus corollary witness" | yes | located the source: arXiv:2309.15692, published **Essential Number Theory 4 (2025)**; §11 = "Iwasawa's theorem on the zeros of the p-adic zeta function" | the file's TeX-line citations (2992, 3033–3059) line up with §11.1–11.2 |
| 5 | ChatGPT MCP | (would ask: standard form + generality + historical evolution of the witness-pushforward compatibility / descent-to-`𝒢⁺` lemma) | **n/a** | — | ChatGPT/OpenAI MCP server **not available** in this session (ToolSearch surfaced only `WebSearch`/`WebFetch`; no `ask_chatgpt`/`openai` tool). Recorded n/a per protocol; **over-covered WebSearch with 4 queries** (rows 1–4, exceeding the ≥3 bar) + the verbatim source-paper extraction (below) to compensate. Same limitation noted in all sibling reports. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | — | both directories **absent** (no `references/` under `.mathlib-quality/`; no `refs/` symlink in the checkout — `ls` confirmed). Recorded n/a with reason. (The `--refs=` argument pointed at the plugin's *skill* references, which were read for the verdict rubric — not project source PDFs.) |
| 7 | nLab | fetched ncatlab.org/nlab/show/Iwasawa+theory | **partial → no** | only the abstract framework (Iwasawa algebra; main conjecture: characteristic ideal generated by `g_i` with `g_i(v^s−1) = L_p(ω^{1−i}, s)`) | **explicitly confirmed via WebFetch:** the page has **none** of (1) descent to a quotient by complex conjugation, (2) pseudo-measure witness compatibility under pushforward, (3) the witness-pushforward statement. Framework only. |
| 8 | nCatLab (categorical) | — | **n/a** | — | not a categorical concept; this is a concrete algebraic identity in a localization (`mk'`/fraction ring), no universal-property reformulation to abstract |
| 9 | Stacks Project | — | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; Stacks has no p-adic-L / Iwasawa-algebra / pseudo-measure material |
| 10 | MathOverflow / Math.SE | covered transitively by rows 1–3 (surfaced Coates–Sujatha, Sharifi/Ouyang notes, Grokipedia "Iwasawa theory") | partial | reaffirms pseudo-measure framework + plus/minus descent as standard background | no thread isolates the witness-pushforward compatibility lemma |
| 11 | recent arXiv (≤5y) | rows 1–4 surfaced **arXiv:2309.15692** (2023/2024, the source) repeatedly, plus totally-real / non-commutative main-conjecture papers (0908.2178, 1006.1490, 1204.3878) | yes | source paper §11; the descent is an internal step of its Corollary 11.4 | the compatibility lemma is **inlined** in that paper, not an independently-stated theorem |

**Source paper located and read verbatim.** Channels 1, 3, 4, 11 surfaced **arXiv:2309.15692, "An
introduction to p-adic L-functions" by Joaquín Rodrigues Jacinto and Chris Williams** (the "RJW" of
the file's docstrings). The PDF was fetched and text-extracted; **§11.1 was read verbatim**. The
relevant passages:

> "Similarly, the Galois group `Γ⁺ = Gal(F∞⁺/Q) = Γ/⟨c⟩` is identified through the cyclotomic
> character with `Z_p^×/{±1}`. Observe that `ζp`, which ostensibly is an element of `Q(Γ)`, vanishes
> at the characters `χ^k`, for any odd integer `k > 1`. We will use this fact to show that `ζp`
> actually **descends to a pseudo-measure on `Γ⁺`**."

> "**Lemma 11.2.** — There is a natural isomorphism `Λ(Γ)⁺ ≅ Λ(Γ⁺)`. *Proof.* … there is a natural
> surjection `Z_p[Γ_n] → Z_p[Γ_n⁺]` induced by the natural quotient map on Galois groups. Since this
> must necessarily map `Z_p[Γ_n]⁻` to `0`, this induces a map `Z_p[Γ_n]⁺ → Z_p[Γ_n⁺]`. … We
> henceforth freely identify `Λ(Γ⁺)` with the submodule `Λ(Γ)⁺` of `Λ(Γ)`."

> "**Lemma 11.3.** — Let `µ ∈ Λ(Γ)`. Then `µ ∈ Λ(Γ⁺)` if and only if `∫_Γ χ(x)^k · µ = 0` for all
> odd `k ≥ 1`."

> "**Corollary 11.4.** — The p-adic zeta function is a pseudo-measure on `Γ⁺`. *Proof.* This follows
> from the interpolation property, as `ζ(1 − k) = 0` for odd `k ≥ 1`."

**Decisive observation for this target.** The source's Corollary 11.4 proof is a *single line*. The
witness-pushforward compatibility — *this Lean theorem* — is **never stated**: RJW "freely identify
`Λ(Γ⁺)` with `Λ(Γ)⁺`" (Lemma 11.2) and the descent then drops out without a witness computation. The
Lean development, however, works with an honest pushforward ring hom `projPlus = π_*` (the
inverse-limit-free, measure-functional incarnation of the "natural surjection") **rather than** the
silent submodule identification, so it *must* prove explicitly that `π_*` carries a 𝒢-side witness to
the 𝒢⁺-side witness. That is pure formalization overhead — a true statement, faithful to the source,
but with no independent existence in the mathematical literature.

### Literature summary (Phase 3)

Concept identified as: **the compatibility step in the descent of the Kubota–Leopoldt p-adic zeta
pseudo-measure from `𝒢 = ℤ_p^×` to the plus-part quotient `𝒢⁺ = ℤ_p^×/{±1}`** — specifically, that
the pushforward `π_* : Λ(𝒢) → Λ(𝒢⁺)` along the quotient projection carries the witness `ν` of
`([g]−1)·ζ_p` to the witness `π_*(ν)` of `([ḡ]−1)·ζ_p⁺`. The *ambient* fact (the descent itself, RJW
Corollary 11.4) is classical (Coates; Coates–Sujatha; the descent is standard background in every
Iwasawa-theory account).

Sources agree on the standard form: **yes** for the *descent* (Corollary 11.4 / `ζ_p` is a
pseudo-measure on `Γ⁺`); the *witness-pushforward compatibility lemma* itself is **not separately
named** in any source — it is inlined book-keeping inside the construction (here, RJW §11.1, the
named source, where it is absorbed into the "free identification" of Lemma 11.2 + the one-line
Corollary 11.4 proof).

Most general standard form: there is no "more general standard form" of *this lemma* in the
literature, because the literature does not state the lemma in isolation — it identifies `Λ(Γ⁺)` with
`Λ(Γ)⁺` and asserts the descent directly. The witness-compatibility fact is an inlined consequence of
that identification.

Generality dimensions where the literature varies (all about the *whole apparatus*, not this lemma):
  - the group: `ℤ_p^×` here; the general theory works for any compact p-adic Lie group `G` with a
    closed normal subgroup `H` such that `G/H` carries the relevant structure (and the plus/minus
    decomposition under the order-2 conjugation `c`). That is the generality of the *entire*
    pseudo-measure / descent apparatus, which mathlib does not have at all — not a weakening axis for
    this single compatibility lemma.
  - the L-function: `ζ_p` here; analogous descents hold for Dirichlet/Hecke p-adic L-functions and
    over totally real fields (Deligne–Ribet), again only meaningful once the apparatus exists.

Disagreement with the literature: **none**. The Lean statement faithfully encodes a true,
standard consequence of the descent (RJW Corollary 11.4 / Lemma 11.2). It is *more explicit* than the
source (it proves the witness-pushforward compatibility the source leaves implicit), which is exactly
the difference between a paper proof and a formal one.

---

### Generality analysis — `PadicMeasure.projPlus_padicZeta_witness` (Phase 4)

Literature-standard form (from Phase 3): there is no isolated literature form of *this lemma*; the
fact is "`ζ_p` descends to a pseudo-measure on `Γ⁺`" (RJW Corollary 11.4), with `Λ(Γ⁺)` identified
with `Λ(Γ)⁺` (Lemma 11.2). The Lean lemma is one faithful, explicit packaging of "the pushforward of
a 𝒢-side witness is the 𝒢⁺-side witness".

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `(p : ℕ) [Fact p.Prime]`, `(hp2 : p ≠ 2)` | odd prime | odd prime (the whole §11 hypothesis: `2` invertible for `Λ⁺ ⊕ Λ⁻`, RJW Lem. 11.1) | **NO** | intrinsic: `padicZeta`/`padicZetaPlus` need `p` odd; the plus/minus split and `⟨−1⟩` order-2 structure require `2` invertible. Not slack. |
| 2 | `(g : ℤ_[p]ˣ)` | element of `𝒢 = ℤ_p^×` | element of the ambient group `Γ` | **NO** (within this project) | generalising `ℤ_p^×` to an abstract `G` (with `G/H` quotient) means generalising the *entire* `PadicMeasure`/`padicZeta`/`projPlus`/`GPlus` apparatus — mathlib has none of it, so there is no target to weaken toward. |
| 3 | `ζ_p`/`ζ_p⁺` (`padicZeta`/`padicZetaPlus`) and the pushforward `projPlus`/`toQPlus` | the specific KL p-adic zeta + its plus-descent | "`ζ_p` is a pseudo-measure on `Γ` descending to `Γ⁺`" (Coates) | yes, **in principle** | the proof only uses: (a) the defining relation of `padicZeta`/`padicZetaPlus` as `mk'(num)(denom)` with the *same packed generator*, (b) `projPlus` is a ring hom, (c) localization unit-cancellation. It would hold for *any* pseudo-measure descending along *any* pushforward of localizations sharing the denominator. **But** that abstraction is a *project-internal* refactor over objects (`PadicMeasure`, `QuotientField`, `projPlus`) mathlib lacks entirely — not a literature-standard generalisation and not a route to mathlib. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *for what it is* — within the project's own vocabulary it
is as general as the descent allows (it works for every `g ∈ ℤ_p^×` and every witness `ν`). The one
conceivable "weakening" (axis 3: abstract "pushforward of a pseudo-measure along a localization ring
hom with a shared denominator") is a project-internal abstraction over objects (`PadicMeasure`,
`QuotientField`, `projPlus`, `padicZeta`) that **do not exist in mathlib at all**, so it cannot be a
mathlib-targeted generalisation.

Number of weakening opportunities found: **1** (axis 3), but project-internal, not literature-grounded,
and not a route to mathlib.

Proposed restatement (if STRICTLY NARROWER): **none applicable** — there is no mathlib-targeted
restatement available.

Cost of restatement: **n/a** — no mathlib-targeted restatement exists.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | **no** | — | already typeclass-driven (`Fact p.Prime`); the witness `hν` is genuine data, not a preamble. The pushforward is already a bundled `→+*`. |
| 2 | sequences/metric → filters/topological? | **no** | — | no limits/convergence in the statement; it is a purely algebraic identity in a fraction ring. |
| 3 | construction → universal-property class? | **no** | — | this is an *equality of two given elements* of `Q(𝒢⁺)`, not a construction of an object. (The localization `mk'`/`IsLocalization` *is* already mathlib's universal-property packaging, and the proof uses it via `map_units`/`mk'_spec`.) |
| 4 | set-with-closure-predicate → bundled substructure? | **no** | — | no subset/closure predicate; objects are already bundled (`→ₗ[ℤ_[p]]`, `FractionRing`, `nonZeroDivisors`). |
| 5 | vector-space/metric/field-specific → weaker typeclasses (module/(semi)ring)? | **no** | — | already at the natural level: ℤ_p-linear functionals and `FractionRing`/`IsLocalization` of the Iwasawa algebra; the rings are fixed by the arithmetic. The axis-3 abstraction (over an arbitrary localization pushforward) is project-internal, not a typeclass weakening with a mathlib target. |
| 6 | 1-categorical → higher/∞-categorical? | **no** | — | no categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | **partial-but-moot** | abstract pseudo-measure descending along a quotient `G → G/H` | this is the totally-real-field / general-`G` generalisation of the *whole* descent theory — a separate, larger development, not an idiom swap. Mathlib lacks the base apparatus regardless. The "index" `g` is already an abstract group element within `𝒢`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.

One-line reason: this is a concrete algebraic equality (the pushforward of a witness equals the
downstream witness) proved by unit-cancellation in a localization that *already uses* mathlib's
idiomatic `IsLocalization`/`FractionRing` universal-property API; there is no sequence-to-filter,
construction-to-universal-property, or typeclass-weakening move that improves its *mathlib*
organisation — and its objects are project-local in the first place.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths are
introduced. Skipped per scope.

---

### Mathlib search-status: `PadicMeasure.projPlus_padicZeta_witness` (Phase 5)

[A] **Lean-Finder** — *(would query: "p-adic zeta function descends pseudo-measure plus part
    pushforward witness compatibility")* — **n/a — Lean-Finder MCP server not available in this
    session** (ToolSearch surfaced only `WebSearch`/`WebFetch`; no `lean_*` search tool). Compensated
    with [D]+[E] over the vendored mathlib tree.

[B] **Loogle** — *(would query type patterns for `toQPlus _ (dirac _ (QuotientGroup.mk _) - 1) *
    padicZetaPlus _ _ = toQPlus _ (projPlus _ _)` and `_ * padicZetaPlus _ _ = _`)* — **n/a —
    `lean_loogle` not available** in this session; and the statement's head symbols
    (`padicZetaPlus`, `projPlus`, `toQPlus`, `padicZeta`, `QuotientField`, `dirac`, `PadicMeasure`)
    are **all project-local**, so a type-pattern search would return nothing in any case.

[C] **LeanSearch** — *(would query: "pushing a witness of (g−1)·zeta_p forward along the quotient
    gives the plus-part witness")* — **n/a — `lean_leansearch` not available**; the natural-language
    target has no mathlib analog (mathlib has no pseudo-measure / p-adic-zeta theory — see [D]).

[D] **Grep mathlib src** — Searched `.lake/packages/mathlib/Mathlib/` for `pseudomeasure` /
    `pseudo_measure` / `PseudoMeasure`, `IwasawaAlgebra` / `iwasawa`, `padicZeta`, `kubota`,
    `leopoldt`, `PadicMeasure`, and `augmentationIdeal` / `augmentation_ideal`. **No hits** for any
    of them. The only `iwasawa` file is `GroupTheory/GroupAction/Iwasawa.lean` (Iwasawa's
    **simplicity criterion** for group actions) — entirely unrelated. Confirmed the mathlib decls the
    proof *does* use all exist: `IsFractionRing.injective`
    (`RingTheory/Localization/FractionRing.lean:137`), `IsLocalization.mk'_spec` /
    `mk'_spec'` (`RingTheory/Localization/Defs.lean:267`/`:271`), `IsLocalization.map_units`
    (`Defs.lean:127`). Also checked `RingTheory/Localization/` for any lemma asserting that a
    localization `mk'` commutes with / is preserved by a `RingHom` between the base rings (the
    "pushforward of a fraction-ring witness" shape): the closest is the generic `IsLocalization.map`
    base-change machinery, which is **not** the statement here (this is about a *specific* pushforward
    `projPlus` between two *different* Iwasawa algebras and a *specific* pseudo-measure, not a generic
    functorial map of localizations).

[E] **Name pattern** — grep for `projPlus_padicZeta_witness` / `padicZeta` / `padicZetaPlus` /
    `projPlus` / `pseudoMeasure` / `kubota` as decl-name fragments across the whole repo and mathlib
    → the declaration line `ZetaGalois.lean:190` and its two call sites (`:246`, `:356`) are the
    **only** occurrences; **no mathlib decl** of that or a near name exists.

Searched for both:
  - the user's current form (pushforward-witness compatibility for `ζ_p → ζ_p⁺`) — **not in mathlib**;
  - the literature-standard form ("`ζ_p` descends to a pseudo-measure on `Γ⁺`", RJW Corollary 11.4)
    — the *entire apparatus* (Iwasawa algebra of measures, pseudo-measures, `padicZeta`, the
    plus-part quotient and its pushforward) is **absent from mathlib**.

Concluded: **not in mathlib** (methods D + E exhausted across the full vendored mathlib tree, plus
the name pattern, plus the literature-standard form; the supporting MCP search tools A–C were
unavailable this session and are recorded n/a with reason, but the grep evidence is conclusive —
mathlib has *no* pseudo-measure / Iwasawa-algebra-of-measures / p-adic-zeta / plus-part-pushforward
theory whatsoever).

---

### Call sites — `PadicMeasure.projPlus_padicZeta_witness` (Phase 6.0)

Internal use count: **2** (within the project, **not** counting the declaring line) — **both in the
same file** (`Iwasawa/ZetaGalois.lean`). External-to-file callers (other files / projects): **0**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Iwasawa/ZetaGalois.lean:246` *(same file)* | `exact ⟨projPlus p ν, projPlus_padicZeta_witness p hp2 g hν⟩` — supplies the witness in `isPlusPseudoMeasure_padicZetaPlus` (**RJW Corollary 11.4**, the headline descent result) |
| `Iwasawa/ZetaGalois.lean:356` *(same file)* | `... := projPlus_padicZeta_witness p hp2 a hν` — supplies `hwit` (the 𝒢⁺-side witness identity at `ā`) in `zetaIdealPlus_eq_span` (**RJW Proposition 11.5** / the `Ideal.span` description of `I(𝒢⁺)ζ_p`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - **(none)** — no other site re-derives the pushforward-witness compatibility. Both consumers
    genuinely call this theorem. It is **not** dead and **not** bypassed.

What the call-sites pattern tells you: **K = 2 internal uses (same file), 0 external, no inline
re-derivation.** By the Phase-6.0 signal table this sits between "K ≥ 1 (real API; consumers depend on
it)" and the same-file-only caveat. Both consumers are themselves *headline* results of the file
(Corollary 11.4 and the `I(𝒢⁺)ζ_p` span), so this is a genuine, load-bearing infrastructure lemma —
**materially different from the dead sibling `padicZeta_witness_neg` (K = 0, superseded), which is
exactly the lemma this one supersedes.** The call-site signal therefore reinforces "this is a real,
used descent-compatibility step", which feeds the BORDERLINE policy question (is the *foundation*
going to mathlib, and would this be public or internal?) rather than a mechanical NO.

### Composition check (Phase 6)

Can `PadicMeasure.projPlus_padicZeta_witness` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: cancel the unit denominator and reduce to a pushed-forward base identity —
`IsLocalization.map_units` + `IsLocalization.mk'_spec` + `IsFractionRing.injective`.
  - Mathlib decls used: `IsLocalization.map_units`, `IsLocalization.mk'_spec`,
    `IsFractionRing.injective` (+ generic `map_mul`/`linear_combination`).
  - Result: **fails as a *mathlib* composition.** These mathlib lemmas are the *glue*, but the
    load-bearing content is project-local: (a) `padicZetaPlus`'s defining equality as
    `mk'(projPlus(zetaNum m))([ū]−1)` with the **same packed generator** `u` as `padicZeta`
    (`exists_nat_topological_generator`), (b) producing `hkey : ([u]−1)·ν = ([g]−1)·zetaNum m` by
    pulling the witness identity *and* the `padicZeta` defining relation back to `Λ(ℤ_p^×)`, and
    (c) pushing that forward by the project-local ring hom `projPlus` (`projPlus_dirac` etc.). Each of
    those is a project-local `def`/`theorem`; without them there is nothing in mathlib to chain.
  - Notes: the only genuinely-mathlib steps (`map_units`, `mk'_spec`, `IsFractionRing.injective`,
    `linear_combination`) discharge the localization bookkeeping; they never produce the *content*
    (the matched-denominator pushforward identity), which is the whole point.

Attempt 2: derive directly from a generic mathlib "localization commutes with a ring hom" /
`IsLocalization.map` functoriality lemma.
  - Result: **fails.** Mathlib's `IsLocalization.map` base-change machinery is about a *generic*
    induced map of localizations; here the map is the *specific* pushforward `projPlus` between two
    *different* Iwasawa algebras `Λ(𝒢)` and `Λ(𝒢⁺)`, applied to the *specific* pseudo-measures
    `ζ_p`/`ζ_p⁺` whose denominators must be shown to correspond (the packed-generator matching). That
    is a use of the whole project tower, not a composition of mathlib results — there is no mathlib
    `ζ_p`, no `Q(ℤ_p^×)`, no `projPlus` to instantiate against.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The statement *is* a multi-step proof built from
*project-local* objects (`padicZeta`/`padicZetaPlus` as `mk'`, `projPlus`, `zetaNum`,
`exists_nat_topological_generator`, `dirac_mk_sub_one_mem_nonZeroDivisors`), and mathlib supplies only
the localization glue (`IsLocalization.map_units`/`mk'_spec`, `IsFractionRing.injective`). There is no
≤3-call mathlib path to the stated form.

---

## Verdict: `PadicMeasure.projPlus_padicZeta_witness`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the mathematics — "`ζ_p` **descends to a pseudo-measure on
  `𝒢⁺ = ℤ_p^×/{±1}`**" — is **classical and canonical**, *exactly* RJW §11.1 (Lemma 11.2 + Lemma 11.3
  + **Corollary 11.4**, arXiv:2309.15692, **read verbatim**; Coates / Coates–Sujatha confirm the
  descent as standard background). **But this specific Lean theorem — the witness-pushforward
  *compatibility* — is not stated anywhere in the literature**: RJW "freely identify `Λ(Γ⁺)` with
  `Λ(Γ)⁺`" and prove Corollary 11.4 in one line, leaving the compatibility implicit. It is
  formalization overhead of an honest pushforward `projPlus` vs. the source's silent identification.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for what it is (4b); the one weakening axis
  (abstract "pushforward of a pseudo-measure along a localization ring hom with a shared denominator")
  is a project-internal refactor over objects mathlib lacks. Modern-idiom check (4c): **no**
  mathlib-improving reformulation (the proof already uses mathlib's idiomatic `IsLocalization` API).
- Mathlib search (Phase 5): **not in mathlib** — mathlib has *no* pseudo-measure theory, no Iwasawa
  algebra of measures, no `padicZeta`/`padicZetaPlus`, no plus-part quotient or its pushforward
  (conclusive by grep over the full vendored tree; the only `iwasawa` file is the unrelated
  group-action simplicity criterion). It uses only mathlib's generic localization glue.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (the multi-step proof is built from
  *project-local* objects; mathlib supplies only `IsLocalization.map_units`/`mk'_spec` +
  `IsFractionRing.injective`). **K = 2 essential same-file call sites** (Corollary 11.4 =
  `isPlusPseudoMeasure_padicZetaPlus`, and `zetaIdealPlus_eq_span`), **0 external**, no inline
  re-derivation — load-bearing, not dead.

**Rationale (1–2 paragraphs):**

This is the same archetype as the file's sibling lemmas (`dirac_neg_one_sub_one_mul_padicZeta`,
`padicZeta_odd_moment_eq_zero`, `padicZeta_witness_neg`): the *mathematics* is unambiguously
mathlib-worthy in spirit — "the Kubota–Leopoldt p-adic zeta function descends to a pseudo-measure on
the plus part `𝒢⁺`" is RJW Corollary 11.4, canonical and traceable to Coates — but the *Lean
declaration* cannot be assessed by the mechanical buckets, because it is stated over a foundation that
does not exist in mathlib. Every symbol carrying it (`PadicMeasure`, `QuotientField`/`QuotientFieldPlus`,
`padicZeta`/`padicZetaPlus`, `projPlus`, `toQPlus`, `zetaNum`, `dirac`, the augmentation/non-zero-divisor
apparatus) is project-local and absent from mathlib (Phase 5, exhaustive). Consequently:
`NO-mathlib-has-it` fails its gate (no decl to cite — mathlib has nothing to specialise from);
`NO-composable-from-mathlib` fails its gate (Phase 6 is NOT-COMPOSABLE *from mathlib* — the ~40-line
proof consumes the project tower, and mathlib supplies only localization glue); and the two YES
buckets fail because one cannot ship a single descent-compatibility lemma ahead of the entire
`padicZeta`/pseudo-measure/`projPlus` foundation it depends on (Phase 4 found no in-scope
generalisation and no modern-idiom improvement, so even "YES-but-generalise" has no mathlib target).

What distinguishes *this* lemma from its dead sibling `padicZeta_witness_neg` (K = 0, superseded) is
that it is **the load-bearing descent-compatibility step that the headline results actually use**:
K = 2 essential consumers — `isPlusPseudoMeasure_padicZetaPlus` (RJW Corollary 11.4 itself) and
`zetaIdealPlus_eq_span` (the `I(𝒢⁺)ζ_p` span, RJW Proposition 11.5). And what makes it *not*
literature-grounded as a standalone result is that the source never isolates it: RJW's "free
identification" `Λ(Γ⁺) ≅ Λ(Γ)⁺` (Lemma 11.2) makes the witness-pushforward compatibility automatic on
paper, so the formal proof's explicit treatment of it is scaffolding for the descent, not an
independent theorem. The honest reading is that **the unit of mathlib-worthiness here is the descent
(Corollary 11.4) within the whole apparatus, not this compatibility lemma in isolation.** If the
project's `PadicMeasure`/pseudo-measure/`padicZeta` development is ever upstreamed, this fact would
ride along as an internal step of the descent — quite possibly `private`, or folded into the proof of
`isPlusPseudoMeasure_padicZetaPlus`. Whether that whole foundation should go to mathlib, and whether
this compatibility lemma should be public or internal, are judgment calls the worker cannot ground in
the evidence. Hence BORDERLINE.

**Refactor-actionable bar — BORDERLINE-needs-human:**

Numbered questions for the user (each yes/no or short answer):

1. **Is the plan to upstream the project's p-adic-L / Iwasawa-algebra foundation** (`PadicMeasure`,
   `QuotientField`/`QuotientFieldPlus`, `IsPseudoMeasure`/`IsPlusPseudoMeasure`, `padicZeta`/
   `padicZetaPlus`, `projPlus`, `GPlus`, `dirac`, the augmentation/non-zero-divisor apparatus) to
   mathlib? If **no**, this theorem is automatically out of scope (it cannot exist in mathlib without
   that foundation) and should stay project-local. *(This is the pivotal question — same as in all the
   sibling reports.)*

2. If that foundation is upstreamed: should `projPlus_padicZeta_witness` be a **public** mathlib lemma,
   or — given that its only consumers are the two headline results in the same file
   (`isPlusPseudoMeasure_padicZetaPlus` = Corollary 11.4, `zetaIdealPlus_eq_span` = Prop 11.5) and it
   has **0 external** callers — would you rather mark it `private`/internal (or inline it into the
   proof of the descent), exposing only the headline `isPlusPseudoMeasure_padicZetaPlus`? RJW itself
   never states this compatibility separately (Lemma 11.2's "free identification" absorbs it).

3. Should the statement be **generalised away from `ζ_p` to "any pseudo-measure that descends"** before
   any mathlib consideration — i.e. an abstract lemma that the pushforward `π_*` of a localization
   witness along a quotient ring hom (with the matched-denominator condition) is the downstream witness?
   The proof only uses `padicZetaPlus = mk'(num)(denom)` with the same packed generator and that
   `projPlus` is a ring hom. (This would be a *project-internal* abstraction over objects mathlib lacks,
   so it is only meaningful once the apparatus itself is in scope — and even then might be subsumed by
   mathlib's generic `IsLocalization.map` functoriality rather than a bespoke lemma.)

4. **Does mathlib's roadmap actually want Kubota–Leopoldt p-adic L-functions / Iwasawa-main-conjecture
   infrastructure** at this granularity (descent to the plus part, the `I(𝒢⁺)ζ_p` ideal), or is this
   research-frontier material that should mature in AINTLIB first? This is a mathlib-community
   taste/scope call the skill cannot make.

**Next action:** user answers the questions; re-run
`/mathlibable PadicMeasure.projPlus_padicZeta_witness` to resolve the verdict. Likely outcomes:
  - Foundation **not** upstreamed (Q1 = no) → drop from mathlib consideration; keep project-local.
  - Foundation upstreamed + keep internal (Q2 = private / inline) → **not a standalone mathlib decl**;
    ships (if at all) folded into the descent result `isPlusPseudoMeasure_padicZetaPlus` (RJW
    Corollary 11.4), exactly mirroring how RJW leaves it implicit.
  - Foundation upstreamed + public, abstract form (Q3 = abstract descending-witness lemma) → re-run
    with the abstract restatement as a Phase-1 input; would likely become `YES-but-generalise-first`
    *relative to the apparatus* (generalise the `ζ_p` instance to the abstract pushforward-of-witness
    lemma), with a check first that mathlib's `IsLocalization.map` doesn't already subsume it.

---

## Next step

User answers the four numbered questions above; re-run
`/mathlibable PadicMeasure.projPlus_padicZeta_witness` to resolve the verdict. The pivotal question is
**Q1** (is the p-adic-L / Iwasawa-algebra foundation going to mathlib at all?) — a **no** there makes
this theorem out of scope; a **yes** turns the remaining questions (public vs. private/inline; concrete
`ζ_p` instance vs. abstract descending-witness lemma) into either an internal step of the descent
result or a likely `YES-but-generalise-first`.
