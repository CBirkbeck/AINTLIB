# `/mathlibable` report — `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-20. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> The **mathematics** — the Kubota–Leopoldt p-adic zeta function `ζ_p` is **invariant under
> complex conjugation**, equivalently `([−1]−[1])·ζ_p = 0` in `Q(ℤ_p^×)`, equivalently
> `ζ_p ∈ Λ(𝒢⁺)` (the even part) — is **classical and canonical**. It is *exactly* RJW
> (arXiv:2309.15692) §11.1, the algebraic content of **Lemma 11.3** ("`µ ∈ Λ(Γ⁺)` iff
> `∫ χ(x)^k µ = 0` for all odd `k ≥ 1`") and the input to **Corollary 11.4** ("the p-adic
> zeta function is a pseudo-measure on `Γ⁺`"). The verbatim source statement was located:
> *"Observe that `ζp` ... vanishes at the characters `χ^k`, for any odd integer `k > 1`. We
> will use this fact to show that `ζp` actually descends to a pseudo-measure on `Γ⁺`."*
> **But this specific Lean theorem is stated entirely over a project-local Iwasawa tower**
> (`PadicMeasure`, the fraction ring `QuotientField p = Q(ℤ_p^×)` of the Iwasawa algebra
> `Λ(ℤ_p^×)`, the structure map `algebraMap`, `padicZeta`, the Dirac measures `dirac`, and
> behind the proof the moment apparatus `padicZeta_moments` + `odd_moment_factor_eq_zero` +
> `eq_zero_of_forall_unitsPowCM_eq_zero`), **none of which exists in mathlib** (confirmed
> exhaustively: mathlib has *no* `padicZeta` / `PadicMeasure` / Iwasawa algebra /
> pseudo-measure / augmentation-ideal-of-a-group-algebra / `unitsPowCM` machinery). So all
> four mechanical buckets fail their gates: there is nothing in mathlib to specialise from
> (NO-mathlib-has-it), nothing to compose the `algebraMap`-encoded equation from in ≤3 mathlib
> calls (NO-composable — the proof consumes the entire moment apparatus and the
> `eq_zero_of_forall_unitsPowCM_eq_zero` Mahler argument), and the lemma cannot be shipped
> ahead of its whole foundation (the YES buckets). On top of that it has **`K = 0` external
> consumers** — a single same-file use inside `padicZeta_witness_neg`. Whether that whole
> foundation should go to mathlib at all, and whether this c-invariance theorem deserves a
> mathlib home, are taste/policy judgments the skill cannot ground in the evidence. Numbered
> questions for the user are in Phase 7. This is the **same situation** as the sibling reports
> `PadicMeasure.padicZeta_odd_moment_eq_zero.md` and
> `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure.md` in this directory.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD
  NOTE — `lake build` is stale/slow in this checkout). The declaration and its full dependency
  chain were read directly from source, exactly as the skill's Phase-0 fallback allows.
- decl `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:69`
- kind:                      theorem
- has sorry:                 **no** — `grep -nE "sorry|admit"` returns nothing for
  `ZetaGalois.lean`, `KubotaLeopoldt/ZetaP.lean` (`padicZeta`, `padicZeta_moments`,
  `padicZeta_isPseudoMeasure`), `KubotaLeopoldt/ZetaValues.lean` (`zetaNeg`), and
  `Measure/PseudoMeasure.lean` (`QuotientField`, `IsPseudoMeasure`, `unitsPowCM`,
  `eq_zero_of_forall_unitsPowCM_eq_zero`) / `Measure/Basic.lean` (`PadicMeasure`, `dirac`).
  The declaration and every dependency are complete, sorry-free.
- module docstring summary:  "ζ_p as a pseudo-measure on `𝒢⁺` and the ideal `I(𝒢)ζ_p`"
  (RJW arXiv:2309.15692 §11.1 corollary + §11.2, on the identified Galois side `𝒢⁺ = GPlus p`).
  The file proves the odd moments of `ζ_p` vanish, deduces c-invariance `([−1]−[1])·ζ_p = 0`
  (**this theorem — "the descent input"**), descends `ζ_p` to a pseudo-measure on `𝒢⁺`, and
  builds the ideals `I(𝒢)ζ_p` / `I(𝒢⁺)ζ_p`.

```lean
/-- **The descent input**: `([−1]−[1])·ζ_p = 0` in `Q(𝒢)`, i.e. ζ_p is invariant
under complex conjugation. (The `b = −1` witness has *all* moments zero: even ones by
`(−1)^k − 1 = 0`, odd ones by `padicZeta_odd_moment_eq_zero`.) -/
theorem dirac_neg_one_sub_one_mul_padicZeta (hp2 : p ≠ 2) :
    algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-1 : ℤ_[p]ˣ) - 1)
        * padicZeta p hp2
      = 0 := by
  obtain ⟨ν, hν⟩ := padicZeta_isPseudoMeasure p hp2 (-1)
  have hzero : ν = 0 := by
    refine eq_zero_of_forall_unitsPowCM_eq_zero p ν fun k hk => ?_
    have hm := padicZeta_moments p hp2 (-1) hk ν hν
    have hb : ((-1 : ℤ_[p]ˣ) : ℚ_[p]) = -1 := by push_cast; ring
    rw [hb] at hm
    refine Subtype.coe_injective ?_
    change ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = ((0 : ℤ_[p]) : ℚ_[p])
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, sub_self, zero_mul, zero_mul] at hm
      rw [hm]; norm_num
    · rw [mul_assoc, odd_moment_factor_eq_zero p ho, mul_zero] at hm
      rw [hm]; norm_num
  rwa [hzero, map_zero] at hν
```

---

### Statement (Phase 1)

`PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` is **a theorem** stating the following:

Let `p` be an odd prime. The Kubota–Leopoldt p-adic zeta function `ζ_p` is a *pseudo-measure*
on `ℤ_p^×` — an element of the total fraction ring `Q(ℤ_p^×)` of the Iwasawa algebra
`Λ(ℤ_p^×)`. The theorem asserts that **`ζ_p` is invariant under complex conjugation**: writing
`[g]` for the group-like element of `g ∈ ℤ_p^×` and `c = −1` for complex conjugation (which
acts on `ℤ_p^× ≅ Gal(ℚ(µ_{p^∞})/ℚ)` as inversion / `−1`), one has

  `([−1] − [1]) · ζ_p = 0`  in `Q(ℤ_p^×)`.

Equivalently `c · ζ_p = ζ_p`, equivalently `ζ_p` lies in the even part `Λ(𝒢⁺)` of the
fraction ring (the part fixed by `c`), which is exactly the membership criterion that lets
`ζ_p` **descend to a pseudo-measure on the plus part `𝒢⁺ = ℤ_p^× / {±1}`** (RJW §11.1, Lemma
11.3 + Corollary 11.4). The proof: the `b = −1` witness measure `ν` of `([−1]−[1])·ζ_p` has
**all** moments zero — even `k` by `(−1)^k − 1 = 0`, odd `k` by the interpolation factor
`(1 − p^{k−1})·ζ(1−k) = 0` (`odd_moment_factor_eq_zero`) — so `ν = 0` by
`eq_zero_of_forall_unitsPowCM_eq_zero` (a measure all of whose `x^k`-moments vanish is zero),
hence `([−1]−[1])·ζ_p = algebraMap ν = 0`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; the whole development is `noncomputable` over `ℚ_[p]`.

Hypotheses (Lean side):
- `(hp2 : p ≠ 2)` — odd prime (the construction of `ζ_p`/`padicZeta` needs `p` odd, and the
  `Λ(Γ) = Λ(Γ)⁺ ⊕ Λ(Γ)⁻` parity splitting needs `2` invertible — RJW Lemma 11.1).

Conclusion (math): `ζ_p` is fixed by complex conjugation: `([−1]−[1])·ζ_p = 0`.

Conclusion (Lean):
`algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-1 : ℤ_[p]ˣ) - 1) * padicZeta p hp2 = 0`,
an equation in the fraction ring `QuotientField p = FractionRing (PadicMeasure p ℤ_[p]ˣ)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a *corollary / stepping-stone* — the c-invariance fact obtained by feeding the
`b = −1` case through the moment vanishing (`padicZeta_moments` + `odd_moment_factor_eq_zero`)
and the zero-measure criterion (`eq_zero_of_forall_unitsPowCM_eq_zero`). It is *not* a new
mathematical structure (no `def`/`class`). It sits in the chain that proves a named result (RJW
Corollary 11.4, "ζ_p is a pseudo-measure on `𝒢⁺`"), but is itself the small "descent input"
(`([−1]−[1])·ζ_p = 0`), not the headline. The headline objects in the file are `padicZetaPlus`
and `isPlusPseudoMeasure_padicZetaPlus`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and
does not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (the `obtain`, the nested `have hzero` block with its
`refine`/`rcases`/two-branch `rw`s, and the final `rwa`). Kind is **theorem**, not a `def`.
One-liner verdict: **n/a** — kind is `theorem`/`lemma`, not `def`/`abbrev`/`structure`. The
one-liner exemption table does not apply. Phase 4.5 (diamond/defeq) is likewise n/a.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Kubota–Leopoldt p-adic zeta function invariant under complex conjugation c-invariance pseudo-measure descends plus part" | yes | standard moment formula `∫ x^k ζ_p = (1−p^{k−1})ζ(1−k)`; ζ_p is a pseudo-measure on `ℤ_p^×` | top hit = the source paper arXiv:2309.15692; Coates "On p-adic L-functions"; researchgate "p-adic zeroes of Kubota–Leopoldt" |
| 2 | WebSearch (general / parity form) | "\"p-adic L-function\" totally even part odd part vanishes complex conjugation descends quotient by minus one Iwasawa" | yes | parity/eigenspace decomposition under complex conjugation; even part nontrivial; `c` acts as `−1` on the minus part | Dasgupta–Kakde, Deligne–Ribet totally-real notes; the even/odd split is foundational |
| 3 | WebSearch (named-after / aliases) | "Iwasawa main conjecture cyclotomic field ζ_p invariant complex conjugation `([-1]-[1])` all moments zero even/odd Bernoulli plus part Δ" | yes | main-conjecture eigenspace picture: minus eigenspace ↔ dual of plus eigenspace; χ-eigenspaces related to `L_p` by **parity of χ** | Wikipedia "Main conjecture of Iwasawa theory"; nLab "Iwasawa theory"; confirms the parity split is the canonical framing |
| 4 | WebSearch (Coates–Wiles / descent) | "Coates Wiles pseudo-measure zeta_p invariant complex conjugation descends G+ even part Iwasawa algebra Lambda construction cyclotomic" | yes | **"ζ_p ... descends to a pseudo-measure on the quotient Galois group ... identified ... with `Z_p^× / {±1}`"** | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; this is a verbatim paraphrase of the target's content |
| 5 | ChatGPT MCP | "standard form of: ζ_p invariant under complex conjugation / `([−1]−[1])·ζ_p = 0` / descends to `𝒢⁺`; generality; historical evolution" | **n/a** | — | ChatGPT MCP server **not installed** in this environment (ToolSearch surfaced no `chatgpt`/`openai` tool; only WebSearch/WebFetch + Asana/Design MCPs). Recorded n/a per protocol; channels 1–4 + the source-paper fetch (below) already pin the standard form and its history (Kummer → Kubota–Leopoldt → Iwasawa → Coates–Wiles). |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | — | both directories **absent** (no `references/` under `.mathlib-quality/`; no `refs/` symlink in the checkout). Recorded n/a with reason. |
| 7 | nLab | "Iwasawa theory" page (ncatlab.org/nlab/show/Iwasawa+theory) — fetched | partial | only the passing line "`L_p(ω^{1−i}, s)` is the Kubota–Leopoldt p-adic zeta function" | **no** clean abstract statement of c-invariance / descent to `𝒢⁺`; no `([−1]−[1])·ζ_p = 0` |
| 8 | nCatLab (categorical) | — | **n/a** | — | not a categorical concept; the result is a concrete algebraic vanishing (`([−1]−[1])·ζ_p = 0`), no universal property to abstract |
| 9 | Stacks Project | — | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; Stacks has no p-adic L-function / Iwasawa-algebra material |
| 10 | MathOverflow / Math.SE | covered transitively by queries 1–4 (Wikipedia "Main conjecture", Grokipedia, learning-seminar notes) | yes | confirms parity split + that the even part carries the nontrivial `L_p`; the descent is treated as standard background | the c-invariance is textbook, not a research-level question |
| 11 | recent arXiv (≤5y) | queries 1–4 returned the source arXiv:2309.15692 (2024) repeatedly + Dasgupta–Kakde-style totally-real notes | yes | the source paper §11 is titled **"Iwasawa's theorem on the zeros of the p-adic zeta function"**; §11.1 contains the exact statement | the file's TeX-line citations (2992, 3033–3059) line up with §11.1–11.2 |

**Source paper located and read verbatim.** Channels 1, 4, 11 surfaced **arXiv:2309.15692,
"An introduction to p-adic L-functions" by Joaquín Rodrigues Jacinto and Chris Williams**
(the "RJW" of the file's docstrings). The PDF was fetched and text-extracted; **§11.1 was read
verbatim**. The relevant passages:

> "Observe that `ζp`, which ostensibly is an element of `Q(Γ)`, **vanishes at the characters
> `χ^k`, for any odd integer `k > 1`. We will use this fact to show that `ζp` actually descends
> to a pseudo-measure on `Γ⁺`.**"

> "**Lemma 11.1.** — Let `c ∈ Γ` denote complex conjugation. Let `R` be a ring in which `2` is
> invertible and `M` an `R`-module with a continuous action of `Γ`. Then `M ≅ M⁺ ⊕ M⁻`, where
> `c` acts as `+1` on `M⁺` and as `−1` on `M⁻`."

> "**Lemma 11.3.** — Let `µ ∈ Λ(Γ)`. Then `µ ∈ Λ(Γ⁺)` if and only if `∫_Γ χ(x)^k · µ = 0` for
> all odd `k ≥ 1`."

> "**Corollary 11.4.** — The p-adic zeta function is a pseudo-measure on `Γ⁺`. *Proof.* This
> follows from the interpolation property, as `ζ(1 − k) = 0` for odd `k ≥ 1`."

The target theorem `([−1]−[1])·ζ_p = 0` is precisely the **algebraic c-invariance** statement
that *is* "`ζ_p ∈ Λ(Γ⁺)`" (Lemma 11.3's `µ⁻ = 0`, since `c = −1` and `([c]−[1])·µ = 0 ⟺ µ`
is fixed by `c`), the input to Corollary 11.4.

### Literature summary (Phase 3)

Concept identified as: **"the Kubota–Leopoldt p-adic zeta function is invariant under complex
conjugation"** — equivalently `([−1]−[1])·ζ_p = 0`, equivalently `ζ_p` lies in the even part
`Λ(𝒢⁺)`, the membership criterion (RJW Lemma 11.3) that lets it **descend to a pseudo-measure
on `𝒢⁺ = ℤ_p^× / {±1}`** (RJW Corollary 11.4). Classical, traceable to the parity decomposition
of cyclotomic Iwasawa modules (Kummer's congruences → Kubota–Leopoldt → Iwasawa → Coates–Wiles).

Sources agree on the standard form: **yes**. Every source gives the same picture: `ζ_p` is
nontrivial only on the even part; complex conjugation `c` (acting as `−1`) fixes `ζ_p`; this is
what lets it descend to `𝒢⁺`. The verbatim RJW §11.1 text matches the Lean docstring exactly.

Most general standard form: for the cyclotomic-ℚ (`ℤ_p^×`) setting, `ζ_p ∈ Λ(𝒢⁺)` via
c-invariance. The generalisation is to totally real fields (Deligne–Ribet / Cassou-Noguès
pseudo-measures, Wiles' main conjecture), where the analogous "the pseudo-measure lives in the
totally-even part" holds.

Generality dimensions where the literature varies:
  - base field: `ℚ` (the `ℤ_p^×` setting here) → arbitrary totally real field (Deligne–Ribet).
    The Lean theorem is the `ℚ`/`ℤ_p^×` case only.
  - encoding: "`c · ζ_p = ζ_p`" (Galois action) vs. "`([−1]−[1])·ζ_p = 0`" (Iwasawa-algebra,
    used here) vs. "`ζ_p ∈ Λ(Γ⁺)`" (eigenspace membership). All equivalent (RJW Lemma 11.3).

Disagreement with the literature: **none**. The Lean form `([−1]−[1])·ζ_p = 0` is one faithful
encoding of the standard c-invariance. (The file flags **erratum #13** in a *sibling* lemma
`odd_moment_factor_eq_zero` — the source's one-line proof of Corollary 11.4 cites
"`ζ(1−k) = 0` for odd `k ≥ 1`", which fails at `k = 1` where the carrier is the Euler factor
`1 − p⁰ = 0`; the file repairs this. That is a *correction* of a source proof line, not a
disagreement with the mathematics, and it lives in the factor lemma, not in this theorem, whose
`k = 1` case is handled here by the even branch `(−1)^1 − 1 = 0`.)

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): `ζ_p` (as a pseudo-measure on `ℤ_p^×` in the
cyclotomic-ℚ setting) is fixed by complex conjugation, i.e. `([−1]−[1])·ζ_p = 0`, i.e.
`ζ_p ∈ Λ(𝒢⁺)`. The "more general" forms (totally real fields; abstract `Λ(G)` with a
`2`-invertible coefficient ring and a `Γ`-action — RJW Lemma 11.1) require an entire separate
apparatus that mathlib does not have either.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]`, `hp2 : p ≠ 2` | odd prime | odd prime (`2` invertible, for the `Λ⁺ ⊕ Λ⁻` split — RJW Lem. 11.1) | NO | intrinsic: `padicZeta` needs `p` odd, and the parity decomposition needs `2` invertible |
| 2 | the element `−1` | complex conjugation `c = −1 ∈ ℤ_p^×` | `c ∈ Γ`, the order-2 conjugation | already canonical | `−1` *is* the conjugation under `χ : Γ ≅ ℤ_p^×`; not a packaging choice |
| 3 | `ζ_p = padicZeta p hp2` and the ambient `algebraMap … QuotientField` | the project's pseudo-measure in `Q(ℤ_p^×)` | "ζ_p is a pseudo-measure on `Γ`" (Coates–Wiles) | n/a | this **is** the standard pseudo-measure encoding; the entire `PadicMeasure`/`QuotientField`/`padicZeta` tower it rests on is project-local, not in mathlib |
| 4 | base setting `ℤ_p^×` | cyclotomic ℚ | totally real field (Deligne–Ribet) | yes, in principle | EXPENSIVE and **moot**: mathlib has neither the ℤ_p^× nor the totally-real Iwasawa apparatus, so there is nothing to state the general form against |
| 5 | the statement `([−1]−[1])·ζ_p = 0` | one specific group element `−1` | Lemma 11.3: `∫ χ^k µ = 0 ∀ odd k ⟺ µ ∈ Λ(Γ⁺)` (abstract `µ`) | yes (abstract `µ`) | the file *does* state the abstract odd-moment criterion separately (`padicZeta_odd_moment_eq_zero`, sibling report); this theorem is the concrete `µ = ζ_p`, `c = −1` instance — the "descent input" |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *within the project's cyclotomic-ℤ_p^× setting* (it
is the c-invariance of `ζ_p` at the canonical conjugation `−1`, using the standard
Iwasawa-algebra encoding). The only "more general" axis (totally real fields, or the abstract
`2`-invertible-`R`-module decomposition of RJW Lemma 11.1) is a different, much larger theory
that mathlib does not contain, so it is not a weakening of *this* statement but a separate
project.
Number of weakening opportunities found: **0** (within scope).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the only hypothesis is `Fact p.Prime` + `p ≠ 2`, already typeclass/value driven; no informal preamble to typeclass-ify |
| 2 | sequences/metric → filters/topological? | no | — | a finite algebraic vanishing statement (`x = 0` in a fraction ring); no limit/convergence to filter-ise |
| 3 | construct an object → universal-property class? | no | — | it is a *property* (a product equals `0`), not a construction; nothing to characterise universally |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no subset/closure structure; the objects (`PadicMeasure`, `QuotientField`) are already bundled (`→ₗ[ℤ_[p]]`, `FractionRing`) |
| 5 | vector-space/metric/field-specific → weaker typeclasses? | no | — | already at the natural level (ℤ_p-linear functionals, `FractionRing`/`IsLocalization` of the Iwasawa algebra); the rings are fixed by the arithmetic |
| 6 | 1-categorical → higher-categorical? | no | — | no categorical content |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | partial-but-moot | abstract `Λ(G)`, `c`-invariance for any order-2 `c` with `2` invertible (RJW Lem. 11.1/11.3) | the abstract odd-moment criterion is already separately stated in the project (`padicZeta_odd_moment_eq_zero`); generalising the *group* `ℤ_p^×` is the totally-real-field theory, a separate development, not an idiom swap — and mathlib lacks the base apparatus regardless |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. There is no contemporary mathlib reformulation that improves the
mathematical organisation here — the statement is a concrete c-invariance fact about a
project-local object, already expressed with mathlib-idiomatic bundled linear functionals and
localization (`FractionRing`/`IsLocalization`, `algebraMap`). The genuinely more abstract target
(RJW Lemma 11.1's `R`-module decomposition under an order-2 action, or Deligne–Ribet over
totally real fields) is a separate, larger theory, not an idiom swap; and mathlib lacks even the
base apparatus (`PadicMeasure`, `padicZeta`, pseudo-measures, the group-algebra augmentation
ideal) to state it.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths
are introduced. Skipped per scope.

---

### Mathlib search-status: `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` (Phase 5)

[A] Lean-Finder       (would query: "p-adic zeta function invariant complex conjugation
    pseudo-measure descends plus part") — **n/a — Lean-Finder MCP server not available in this
    environment** (ToolSearch surfaced only WebSearch/WebFetch; no `lean_*` search tool).
[B] Loogle            (would query: type patterns for `algebraMap _ (FractionRing _) (dirac _ (-1) - 1) * _ = 0`
    and `_ * padicZeta _ _ = 0`) — **n/a — `lean_loogle` not available** in this environment.
[C] LeanSearch        (would query: "Kubota–Leopoldt p-adic zeta function invariant under complex
    conjugation, ([-1]-[1]) zeta_p = 0") — **n/a — `lean_leansearch` not available** in this
    environment.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib` for: `padicZeta`, `PadicMeasure`,
    `pseudoMeasure`/`pseudo.measure`/`pseudomeasure`, `kubota`, `leopoldt`, `IwasawaAlgebra`/
    `iwasawa`, `padicLFunction`/`PadicLFunction`, `unitsPowCM`, `augmentationIdeal`,
    `MonoidAlgebra … ker`, plus `mahler`, and listed `NumberTheory/LSeries/` + `NumberTheory/Padics/`.
    **No hits** for any p-adic-L / Iwasawa-algebra / pseudo-measure / group-algebra-augmentation
    name. The only `iwasawa` hits are `GroupTheory/GroupAction/Iwasawa.lean` (Iwasawa's
    *simplicity criterion* for permutation groups) and unrelated PSL/matrix files. Mathlib's
    `NumberTheory/LSeries/` has only the **complex-analytic** L-functions (`RiemannZeta`,
    `Dirichlet`, `Hurwitz*`, `ZetaZeros`); `NumberTheory/Padics/` has `MahlerBasis` (which the
    *project* builds on) but **no** p-adic-measure-as-functional / pseudo-measure / `padicZeta`.
[E] Name pattern      grep for `padicZeta` / `dirac_neg_one` / `pseudoMeasure` / `unitsPow` /
    `augmentation` / `kubota` as decl-name fragments across mathlib → **no hits**.

Searched for both:
  - the user's current form (`([−1]−[1])·ζ_p = 0`, the `algebraMap`-encoded equation) — not in
    mathlib (mathlib has no `ζ_p` and no `PadicMeasure` fraction ring at all);
  - the literature-standard form ("ζ_p invariant under complex conjugation / `ζ_p ∈ Λ(Γ⁺)` /
    ζ_p descends to `𝒢⁺`") — not in mathlib. The complex-analytic shadow (`riemannZeta` trivial
    zeros, `bernoulli_eq_zero_of_odd`) is in mathlib and is what the project's *factor* lemma
    `odd_moment_factor_eq_zero` calls — but that is about `ζ`/`B_k`, not about the c-invariance
    of the p-adic pseudo-measure this theorem is about.

Concluded: **not in mathlib** (methods D + E exhausted across all relevant name/keyword families;
methods A–C unavailable in this environment and recorded n/a with reason). Mathlib has *no* p-adic
L-function / Kubota–Leopoldt / Iwasawa-algebra / pseudo-measure / group-algebra-augmentation
machinery whatsoever — neither the specific c-invariance statement nor the foundation it is
stated over.

---

### Call sites — `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` (Phase 6.0)

Internal use count: **1** (within the project, **not** counting the declaring file's docstring) —
but that one use is **inside the same file** (`ZetaGalois.lean`). External-to-file callers (other
files / projects): **0**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Iwasawa/ZetaGalois.lean:117` *(same file)* | `rw [this, mul_assoc, dirac_neg_one_sub_one_mul_padicZeta p hp2, mul_zero]` — used in `padicZeta_witness_neg` to prove witness symmetry `([−g]−[g])·ζ_p = [g]·(([−1]−[1])·ζ_p) = 0` |
| `Iwasawa/ZetaGalois.lean:16` *(same file, docstring)* | named in the module docstring: "c-invariance `([−1]−[1])·ζ_p = 0` — the descent input" |
| — | *(no callers in any other file or project)* |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - **(none)** — no other site re-derives `([−1]−[1])·ζ_p = 0`. The single consumer
    (`padicZeta_witness_neg`) genuinely calls this theorem rather than re-deriving it. (Note: the
    *odd-moment* half of this proof is shared with the sibling `padicZeta_odd_moment_eq_zero` via
    the common `odd_moment_factor_eq_zero`, but the c-invariance conclusion itself is derived only
    here.)

What the call-sites pattern tells you: **K = 1 internal use, same file, 0 external, no inline
re-derivation.** By the Phase-6.0 signal table, `K = 1 internal use only` leans toward
NO-composable ("possibly the wrong abstraction — could be inlined"). Here, though, the consumer
genuinely depends on the named fact and there is no mathlib alternative to inline against (the
"thing it would compose from" — `padicZeta_moments`, `eq_zero_of_forall_unitsPowCM_eq_zero` — is
itself project-local). So the call-site signal reinforces "this is a project-internal stepping
stone toward the descent (Corollary 11.4)", which feeds the BORDERLINE policy question rather
than a mechanical NO.

### Composition check (Phase 6)

Can `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` be derived from **mathlib** in ≤3 chained
calls?

Attempt 1: `(padicZeta_isPseudoMeasure …).choose_spec ▸ (… eq_zero_of_forall_unitsPowCM_eq_zero …)`
  - Mathlib decls used: only generic glue (`map_zero`, `Subtype.coe_injective`, `mul_assoc`,
    `mul_zero`, `sub_self`, `Even.neg_one_pow`, `norm_num`).
  - Result: **fails as a *mathlib* composition.** The three load-bearing steps —
    `padicZeta_isPseudoMeasure` (ζ_p is a pseudo-measure, so a witness `ν` exists),
    `padicZeta_moments` (the moment formula `∫ x^k ζ_p = (b^k−1)(1−p^{k−1})ζ(1−k)`), and
    `eq_zero_of_forall_unitsPowCM_eq_zero` (a measure with all `x^k`-moments zero is zero, via the
    Mahler-transform argument) — are **project-local theorems**, not mathlib. Without them there
    is nothing in mathlib to chain. The even-`k` branch (`(−1)^k − 1 = 0`) and the odd-`k` branch
    (`odd_moment_factor_eq_zero`, which *itself* wraps `bernoulli_eq_zero_of_odd` + the Euler
    factor) are both glued through the project-local `padicZeta_moments`.
  - Notes: the *genuinely mathlib* part is `Even.neg_one_pow`, `bernoulli_eq_zero_of_odd`, casting
    `ℤ_[p] ↪ ℚ_[p]`, and `norm_num`. None of these, alone or in ≤3 calls, produces the
    `algebraMap`-encoded c-invariance equation.

Attempt 2: derive directly from mathlib's parity/eigenspace API (idempotents `(1±c)/2`).
  - Result: **fails.** Mathlib has `LinearMap`/`Module` idempotent-decomposition lemmas, but
    there is no mathlib object `ζ_p`, no `Q(ℤ_p^×)`, and no `Γ`-action to apply them to. RJW
    Lemma 11.1's decomposition would have to be instantiated on the project-local
    `QuotientField p`, which is not a composition of mathlib results but a use of the whole tower.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The statement *is* a short composition of
*project-local* results (`padicZeta_isPseudoMeasure` + `padicZeta_moments` +
`odd_moment_factor_eq_zero` + `eq_zero_of_forall_unitsPowCM_eq_zero`), but those are not in
mathlib, and mathlib's relevant primitives (`bernoulli_eq_zero_of_odd`, the ζ trivial zeros, the
idempotent decomposition) only discharge fragments, never the moment-to-measure bridge. There is
no mathlib path to the stated form.

---

## Verdict: `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the mathematics is **classical and canonical** — "ζ_p is invariant
  under complex conjugation / `([−1]−[1])·ζ_p = 0` / ζ_p descends to a pseudo-measure on
  `𝒢⁺ = ℤ_p^× / {±1}`", *exactly* RJW §11.1 (Lemma 11.1 + **Lemma 11.3** + **Corollary 11.4**,
  arXiv:2309.15692, read verbatim); 4 converging WebSearch channels (incl. Coates–Sujatha
  paraphrasing the descent) + the located/extracted source paper; nLab has only a passing mention.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL within the cyclotomic-ℤ_p^× setting** (4b);
  **no modern-idiom restatement** improves it (4c). The only larger forms (RJW Lem. 11.1's
  abstract `2`-invertible-module decomposition; Deligne–Ribet over totally real fields) are
  separate theories mathlib also lacks.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has *no* p-adic L-function /
  Kubota–Leopoldt / Iwasawa-algebra / pseudo-measure / `PadicMeasure` / group-algebra-augmentation
  machinery at all (only the unrelated Bernoulli vanishing + ζ trivial zeros, which discharge a
  fragment of the odd-`k` branch).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (the short composition is of
  *project-local* theorems); **K = 1 internal call site (same file), 0 external**, no inline
  re-derivation.

**Rationale (1–2 paragraphs):**

This is the textbook situation where the *mathematics* is unambiguously mathlib-worthy in spirit
but the *Lean declaration* cannot be assessed by the mechanical buckets, because it is stated over
a foundation that does not exist in mathlib. The statement "the Kubota–Leopoldt p-adic zeta
function is invariant under complex conjugation, `([−1]−[1])·ζ_p = 0`" is canonical — the verbatim
RJW §11.1 source (Lemma 11.3 / Corollary 11.4) was located and confirms the Lean docstring exactly
(Phase 3). But every symbol carrying it here — `PadicMeasure` (ℤ_p-linear functionals on
`C(X, ℤ_[p])` = the Iwasawa algebra), `QuotientField` (its fraction ring `Q(ℤ_p^×)`),
`algebraMap`, `padicZeta`, the Dirac measures `dirac`, and behind the proof
`padicZeta_isPseudoMeasure` / `padicZeta_moments` / `odd_moment_factor_eq_zero` /
`eq_zero_of_forall_unitsPowCM_eq_zero` — is **project-local and absent from mathlib** (Phase 5,
exhaustive). Consequently: `NO-mathlib-has-it` fails its gate (Phase 5 found no decl to cite —
mathlib has nothing to specialise from); `NO-composable-from-mathlib` fails its gate (Phase 6 is
NOT-COMPOSABLE *from mathlib* — the only composition is of project-local theorems); and the two
YES buckets fail because one cannot ship a single c-invariance theorem ahead of the entire
`padicZeta`/pseudo-measure foundation it depends on (and Phase 4 found no in-scope generalisation
and no modern-idiom improvement, so even "YES-but-generalise" has no target).

What remains is a genuine **judgment call**: (a) whether the project's whole p-adic-L /
Iwasawa-algebra tower should be upstreamed to mathlib (a large, multi-file effort — *that* is the
real decision, and it is exactly the question raised by the sibling reports
`padicZeta_odd_moment_eq_zero` and `twistedZetaHalf_isTwistedPseudoMeasure`); and (b) even
granting that, whether *this particular* c-invariance lemma deserves a public mathlib home. The
call-site evidence argues it is an internal stepping-stone toward the headline descent
(Corollary 11.4 = `isPlusPseudoMeasure_padicZetaPlus`): **`K = 1` consumer, same file, 0
external** — used once inside `padicZeta_witness_neg`, with no external dependents. So a reasonable
mathlib reviewer might keep it `private`/internal even if the foundation is upstreamed, exposing
only the headline `isPlusPseudoMeasure_padicZetaPlus`. The skill cannot ground either decision in
the evidence; hence BORDERLINE.

**Numbered questions (≤5):**

1. Is the plan to upstream the project's p-adic-L / Iwasawa-algebra foundation (`PadicMeasure`,
   `QuotientField`/`Q(ℤ_p^×)`, `IsPseudoMeasure`, `padicZeta`, `padicZeta_moments`,
   `eq_zero_of_forall_unitsPowCM_eq_zero`, `dirac`, the augmentation ideal) to mathlib? If **no**,
   this theorem is automatically out of scope (it cannot exist in mathlib without that foundation)
   and should stay project-local.

2. If that foundation is upstreamed: should `dirac_neg_one_sub_one_mul_padicZeta` be a *public*
   mathlib lemma, or — given **`K = 1`/same-file/0-external** consumers — would you rather mark it
   `private`/internal and expose only the headline descent result
   (`isPlusPseudoMeasure_padicZetaPlus`, i.e. RJW Corollary 11.4)?

3. In a mathlib home, which is the canonical statement to expose — this **Iwasawa-algebra form**
   (`([−1]−[1])·ζ_p = 0`), the **eigenspace-membership form** (`ζ_p ∈ Λ(𝒢⁺)`, RJW Lemma 11.3's
   `µ⁻ = 0`), or the **Galois-action form** (`c · ζ_p = ζ_p`)? RJW phrases the membership criterion
   (Lemma 11.3) abstractly for any `µ`; the project specialises it to `ζ_p` at `c = −1`.

4. Would the more general, reusable statement be the abstract **RJW Lemma 11.3** ("`µ ∈ Λ(Γ⁺)` iff
   `∫ χ^k µ = 0` for all odd `k`", for any pseudo-measure `µ` and any order-2 `c` with `2`
   invertible — RJW Lemma 11.1) — with `dirac_neg_one_sub_one_mul_padicZeta` left as its
   project-local `µ = ζ_p` consumer? If so the contribution to prioritise is the criterion, not
   this instance.

**Next action:** user answers the questions; re-run
`/mathlibable PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` to resolve the verdict. Likely
outcomes:
  - Foundation not upstreamed (Q1 = no) → drop from mathlib consideration; keep project-local.
  - Foundation upstreamed + keep internal (Q2 = private) → not a standalone mathlib decl; ships
    (if at all) folded into the descent-to-`𝒢⁺` result `isPlusPseudoMeasure_padicZetaPlus`.
  - Foundation upstreamed + public, abstract criterion (Q3/Q4 = Lemma 11.3 form) → re-run with the
    abstract `µ ∈ Λ(Γ⁺) ⟺ odd moments vanish` restatement as a Phase-1 input; would likely become
    `YES-but-generalise-first` (generalise the `c = −1`, `µ = ζ_p` instance to the abstract
    membership criterion, with the totally-real-field axis as a follow-up).

---

## Next step

User answers the four numbered questions above; re-run
`/mathlibable PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta` to resolve the verdict. The
pivotal question is Q1 (is the p-adic-L / Iwasawa-algebra foundation going to mathlib at all?) — a
**no** there makes this theorem out of scope; a **yes** turns the remaining questions (public vs.
private; concrete instance vs. abstract RJW-Lemma-11.3 criterion) into a likely
`YES-but-generalise-first`.
