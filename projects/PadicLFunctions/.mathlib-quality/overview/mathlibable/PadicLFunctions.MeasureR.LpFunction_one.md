# `/mathlibable` report — `PadicLFunctions.MeasureR.LpFunction_one`

**Final verdict: `YES-but-generalise-first`** (LITERATURE-WEAKENING — the proven case `D > 1` is
a sub-case of Leopoldt's theorem; the missing pure-`p`-power case `D = 1` is part of the standard
statement and is already flagged as deferred in the project). See Phase 7 for the full evidence trail.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `lake build`
  is stale/slow in this monorepo; the declaration and its dependency chain were read directly from
  source, which the skill's Phase-0 fallback explicitly allows).
- decl `PadicLFunctions.MeasureR.LpFunction_one`:  ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:1594`
- kind:                      theorem
- has sorry:                 no (the proof body, lines 1594–1801, is sorry-free; `grep -c sorry`
  over the whole file returns 0)
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" —
  the file proves Leopoldt's closed formula for the value of the p-adic L-function at `s = 1`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.LpFunction_one` is a **theorem** stating **Leopoldt's formula for the value
of the Kubota–Leopoldt p-adic L-function at `s = 1`** (the case where the conductor has a non-trivial
tame part `D > 1`).

In standard mathematical notation: let `θ = χη` be a primitive non-trivial Dirichlet character of
conductor `N = D·pⁿ`, where `η` is primitive of tame conductor `D > 1` coprime to `p`, and `χ` is
primitive of `p`-power conductor `pⁿ`. Let `ζ_N = ε` be a primitive `N`-th root of unity (realised as
the split product `ζ·ε_{pⁿ}` of a tame and a wild root), `τ(θ⁻¹) = G` the Gauss sum of `θ⁻¹`, and
`log_p` the (Iwasawa-branch, `log_p p = 0`) p-adic logarithm. Then

> `L_p(θ, 1) = −(1 − θ(p)·p⁻¹) · G⁻¹ · Σ_{c} θ⁻¹(c) · log_p(1 − ε^c)`,

the sum running over `c ∈ {0,…,N−1}` (the non-unit terms vanish, so effectively over `(ℤ/N)ˣ`). This
is RJW Theorem 6.1(ii) — Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions*, ENT
4(1), 2025 — the modern rendering of a theorem of **Leopoldt** (announced 1964), first published with
proof by **Iwasawa** in *Lectures on p-adic L-functions* (Annals of Math. Studies 74, 1972, from his
1969 Princeton lectures); also Washington, *Introduction to Cyclotomic Fields* (GTM 83), Ch. 5.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]` — a complete ultrametric extension of `ℚ_p` holding the values of the characters and
  roots of unity (the coefficient field).
- `D : ℕ`, `[NeZero D]`, `hD1 : 1 < D` — the tame conductor.
- `η : DirichletCharacter (integerRing K) D`, `hη : η.IsPrimitive`, `hD : ¬ p ∣ D` — the tame part.
- `n : ℕ`, `χ : DirichletCharacter (integerRing K) (p ^ n)`, `hχ : χ.IsPrimitive` — the wild part.
- `θK : DirichletCharacter K (D * p ^ n)`, `hθ1 : θK ≠ 1`, `hθK : θK = …changeLevel η * …changeLevel χ`,
  `hprim : θK.IsPrimitive` — the assembled product character `θ = χη`, `K`-valued.
- `ζ, εp, ε, ξ` (with `hζ, hεp, hε, hξ` primitive-root facts and `hsplit : ε = ζ·εp`) — the roots of
  unity; `ε` is the primitive `N`-th root, split into tame `ζ` and wild `εp`.
- `G : K`, `_hG : IsUnit G`, `hGval : G = gaussSum θK⁻¹ (AddChar.zmodChar (D*p^n) hε.pow_eq_one)` —
  the Gauss sum `τ(θ⁻¹)`.

Hypotheses (math): `θ = χη` primitive non-trivial; tame part `η` primitive of conductor `D > 1`
coprime to `p`; wild part `χ` primitive of conductor `pⁿ`; `ε` a primitive `N`-th root with the
tame/wild split; `G` the Gauss sum of `θ⁻¹`.

Conclusion (math): the displayed closed formula for `L_p(θ, 1)`.

Conclusion (Lean):
```
LpFunction p K η hζ hD χ 1
  = -(1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹) * G⁻¹
    * ∑ c ∈ Finset.range (D * p ^ n),
        θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c)
```

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: This is a **main result of the project** (named in the module docstring as "RJW Thm 6.1(ii),
decomposition P6") and a **theorem associated with a named mathematician** (Leopoldt's formula,
Iwasawa's theorem). Both BIG triggers fire.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~210 substantive lines (lines 1594–1801).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. (And it is emphatically not a one-liner:
the proof assembles four "STEP" blocks — the CRT Gauss-product split, the cleared-mass identity T615,
the evaluated trace T616, and a final field-arithmetic combine.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific form) | "p-adic L-function value at s=1 formula L_p(theta,1) Gauss sum logarithm cyclotomic Leopoldt" | yes | `L_p(1,χ)` related to `log_p` of cyclotomic units; Euler factor `(1−χ(p)/p)` | Surfaced the RJW/MSP survey, Williams arXiv 2201.08870, Dasgupta trilogies. "One of the first instances of the p-adic Beilinson conjectures." |
| 2  | WebSearch (general / textbook) | "Washington Introduction Cyclotomic Fields p-adic L-function L_p(1,chi) formula log_p Gauss sum theorem" | yes | Washington Ch. 5 has a section "the value at s=1" | Confirms the formula is standard textbook material (GTM 83). |
| 3  | WebSearch (named-after / attribution) | "Iwasawa Lectures on p-adic L-functions value at s=1 cyclotomic units log formula theorem" | yes | Iwasawa published Leopoldt's formula (announced 1964) with proof in his 1969 Princeton lectures (AM-74) | Nails the attribution: **Leopoldt** (statement), **Iwasawa** (first published proof). |
| 4  | ChatGPT MCP | (intended) "standard form of `L_p(1,χ)`, its generality, historical evolution" | n/a | — | The `chatgpt-math` MCP server is configured but sits in `mcp-needs-auth-cache.json` (unauthenticated); it was NOT surfaced as a callable tool (`ToolSearch "+chatgpt math ask"` → "No matching deferred tools found"). Recorded as attempted-but-unavailable. The three independent literature channels (1–3, 5) more than cover the standard-form + history question this channel would have asked. |
| 5  | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` ; `find … *.pdf` ; `refs/PadicLFunctions/` | n/a | (no references dir; no PDFs; no `refs/` symlink) | Directory absent — recorded n/a. **However** the project docstrings name the source precisely ("RJW", "TeX 1992–1995"), and Phase-3 channel 6 below recovered the source PDF directly. |
| 6  | nLab / direct source (RJW survey) | WebFetch of MSP ENT 4(1) 2025 "An introduction to p-adic L-functions" (Rodrigues Jacinto & Williams) | **yes** | **`L_p(1,χ) = −(1 − χ(p)/p)·(τ(χ̄)/f)·Σ_{a=1}^{f} χ̄(a) log_p(1 − ζ_f^a)`** (their **Theorem 4.3**) | This IS the "RJW" of every project docstring (R.J. + Williams). Verbatim match to the Lean statement up to the project's Gauss-normalisation (`G⁻¹` vs `τ(χ̄)/f`). Hypotheses: χ primitive, non-trivial, **odd** (`χ(−1)=−1`), conductor `f`, `p∤f`. |
| 7  | nCatLab (if categorical) | (judged) p-adic L-value at s=1 | n/a | — | Not a categorical concept (an explicit analytic special-value identity). Brief look at nLab returned no dedicated "Leopoldt formula" entry; the analytic-NT content lives in the survey/textbook channels. |
| 8  | Stacks Project (if alg geom) | (judged) p-adic L-function | n/a | — | Not an algebraic-geometry / scheme-theoretic concept. Stacks has no p-adic L-function material. |
| 9  | MathOverflow / Math.SE | covered transitively by channels 1–3 (which index MO/SE threads on "values of p-adic L-functions / cyclotomic units / Beilinson") | yes (indirect) | same as #1/#6 | The "p-adic Beilinson" framing and the cyclotomic-unit connection appear repeatedly in the indexed discussion; no contradicting variant surfaced. |
| 10 | recent arXiv (last 5 yrs) | "Sum expressions for Kubota–Leopoldt p-adic L-functions" (Williams, arXiv 2201.08870, Proc. Edinburgh Math. Soc.) | yes | A sum expression for `L_p(s,χ)` (incl. `s=1`) without restriction on `p` for non-trivial χ | Confirms the `s=1` value is an actively-cited classical object; this paper re-derives/extends it. The body text was unreadable through WebFetch (compressed PDF), but title + abstract + the survey by the same author pin the content. |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (specific formula,
textbook treatment, attribution/history); the ChatGPT-MCP channel is recorded n/a with an explicit
reason (server unauthenticated/uncallable) and its question is covered by channels 1–3+6; local refs
checked (absent, recorded n/a); nLab/nCatLab/Stacks/MathOverflow/arXiv each checked or n/a-with-reason.
The decisive hit is channel 6 — the **RJW survey itself**, the exact source the project cites.

### Literature summary (Phase 3)

Concept identified as: **Leopoldt's formula for the value of the (Kubota–)Leopoldt p-adic L-function
at `s = 1`** (a.k.a. "the value at s=1", the Iwasawa–Leopoldt special-value formula relating
`L_p(1,χ)` to p-adic logarithms of cyclotomic units).

Sources agree on the standard form: **yes.** RJW Thm 4.3 (= the project's Thm 6.1(ii)), Washington
GTM 83 Ch. 5 "the value at s=1", and Iwasawa AM-74 all give the same identity. The canonical statement is
```
L_p(1, χ) = −(1 − χ(p)/p) · (τ(χ̄)/f) · Σ_{a=1}^{f} χ̄(a) · log_p(1 − ζ_f^a),   χ primitive, odd, nontrivial, conductor f, p∤f.
```

Most general standard form: the formula holds for **every** primitive non-trivial **odd** Dirichlet
character χ of conductor `f` with `p∤f` (the even case is trivial: `L_p(s,χ) ≡ 0` for χ even, so the
formula is vacuous there). Crucially **`f` is allowed to be a pure `p`-power, a pure prime-to-`p`
number, or a product** — the standard statement has **no `D > 1` hypothesis**; that restriction is an
artefact of the project's current proof route, not of the theorem.

Generality dimensions where the literature varies:
- **Conductor structure**: literature states it for arbitrary conductor `f` (writing `f = D·pⁿ` only
  for bookkeeping). The Lean theorem requires the **tame part `D > 1`** (`hD1 : 1 < D`); the pure
  `p`-power case `D = 1` is explicitly **deferred** in the module docstring ("the pure `p`-power case
  `D = 1` is deferred — decomposition R6, replan 4"). This is the one real generality gap.
- **Normalisation of the Gauss factor**: literature writes `τ(χ̄)/f`; the Lean form writes `G⁻¹` with
  `G = τ(θ⁻¹)`. These agree under the project's clearing convention (`G(η⁻¹)·ζ_η` normalisation,
  `LpFunction` divides the Gauss unit back out) — a presentation choice, not a mathematical difference.
- **Odd/non-triviality**: the literature's "odd" hypothesis is implicit in the Lean setup (the
  development targets the non-trivial primitive `θ`; for even θ the value is 0 and the formula trivial).

Disagreement with the literature: **none on the formula.** The only divergence is the temporary
`D > 1` restriction, which the literature does not impose and which the project itself records as a
deferred sub-case.

---

### Generality analysis — `PadicLFunctions.MeasureR.LpFunction_one`

Literature-standard form (from Phase 3): the formula for **all** primitive non-trivial odd χ of
**arbitrary** conductor `f` with `p∤f` — in particular including `f = pⁿ` (the `D = 1` case).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `hD1 : 1 < D` (tame conductor `> 1`) | requires a non-trivial prime-to-`p` part | **no such hypothesis** — `f` arbitrary, incl. `f = pⁿ` | **yes** | The `D = 1` (pure `p`-power conductor) case is part of the same theorem. The project defers it (docstring: "deferred — decomposition R6, replan 4") because the norm-one discharge `‖1 − ε^c‖ = 1` and the CRT Gauss-split argument used here need the tame part. Removing `D > 1` is the genuine generalisation. **EXPENSIVE** — needs the deferred `D=1` proof route. |
| 2 | `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` | a complete ultrametric `ℚ_p`-algebra field | the values live in `ℂ_p` (or `ℚ̄_p`); any complete extension holding the roots/characters | NO (already general) | This is the correct mathlib-idiomatic generality — exactly the right typeclass bundle for "a coefficient field for p-adic L-values". Not a narrowing. |
| 3 | `hη : η.IsPrimitive`, `hχ : χ.IsPrimitive`, `hprim : θK.IsPrimitive` | primitive characters | primitive (standard) | NO | Primitivity is the standard hypothesis (the formula is stated for the primitive character; the Gauss sum requires it). Correct. |
| 4 | `hsplit : ε = ζ·εp` (root split into tame·wild) | factored root of unity | `ζ_f` any primitive `f`-th root | NO (faithful to literature) | The split realises an arbitrary primitive `N`-th root via tame·wild factors (RJW's `ε_N`); it is the CRT bookkeeping, equivalent to the literature's `ζ_f`. Not a narrowing. |
| 5 | `G` passed as a hypothesis (`hGval`, `_hG`) | Gauss sum supplied as a named unit | `τ(χ̄)` intrinsic | borderline | Threading `G` as an explicit argument is a Lean-ergonomics choice; mathlib would likely make it intrinsic (`gaussSum θ⁻¹ …`) rather than a hypothesis. A cleanup detail, not a generality gap. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **1 substantive** (the `D > 1` restriction; row 1) + minor
presentation items (rows 2–5 are already general / are ergonomics).

Proposed restatement (drop the tame-part restriction; cover all conductors including `f = pⁿ`):
```lean
-- the literature-standard target: NO `1 < D` hypothesis; conductor N = D·pⁿ arbitrary (D ≥ 1).
theorem LpFunction_one_general {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hθ1 : θK ≠ 1) (hprim : θK.IsPrimitive)
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) … :
    LpFunction p K η hζ hD χ 1
      = -(1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹) * G⁻¹
        * ∑ c ∈ Finset.range (D * p ^ n),
            θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c) := …
```
(i.e. the same statement with `hD1 : 1 < D` removed and the `D = 1` route filled in).

Cost of restatement: **EXPENSIVE** — the `D = 1` case is a known open sub-task in the project (it is
explicitly deferred); the norm-one discharge and CRT-split steps must be re-engineered for a pure
`p`-power conductor. Per the skill, **EXPENSIVE does not downgrade the verdict** — getting the
full-generality form is exactly mathlib's job.

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently. (4c is run next; it
does not flip the bucket here.)

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partly | Make `G` (the Gauss sum) intrinsic rather than a threaded `hGval`/`_hG` hypothesis pair; possibly bundle the primitive-root split as a structure | Cleaner statement; but this is ergonomics, not new mathematics — defer to `/generalise` + `/cleanup`. |
| 2 | sequences/metric → filters/topological? | no | — | The statement is an algebraic identity of p-adic numbers; the only limits are inside `extLog`/`gaussSum`, already filter-based in mathlib. No filter-isation of the headline statement. |
| 3 | construct an object where a universal property would characterise it? | no | — | `L_p` is genuinely a constructed analytic object (interpolation of Dirichlet L-values); the universal-property framing belongs to the *definition* `LpFunction`, not to this special-value theorem. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No subset/closure predicate here. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no (already done) | — | The coefficient field already sits at the right generality (row 2 of 4a). |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorical statement. |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid? | no | — | The indices (`D`, `pⁿ`, the conductor `N`) are intrinsic to the arithmetic; they are not a spurious concretisation. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no Bourbaki-2.0 reformulation changes the mathematics).
One-line reason: this is a special-value *identity* of p-adic numbers, not a definition or a
limit-of-sequences statement; the only contemporary-idiom improvements (making `G` intrinsic, bundling
the root split) are statement-ergonomics handled by `/generalise`+`/cleanup`, not organisational
re-foundations. The "generalise first" target is therefore the **literature-weakening** of Phase 4b
(drop `D > 1`), not a modern-idiom rewrite.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (theorems introduce no definitional equalities or
typeclass-search paths). Skipped per scope rule.

---

### Mathlib search-status: `PadicLFunctions.MeasureR.LpFunction_one`

[A] Lean-Finder       (n/a — no live Lean-Finder MCP in this session; substituted by exhaustive
                       grep over the local mathlib checkout `.lake/packages/mathlib/Mathlib/`, methods
                       D/E below) — no hits.
[B] Loogle            (n/a — no live Loogle MCP in this session) — the type-pattern target
                       (`LpFunction _ _ _ … 1 = …`) cannot exist because the *constituent symbols*
                       `LpFunction`, `extLog`, and the Iwasawa-branch p-adic log are themselves absent
                       from mathlib (verified by D/E). No type-pattern in mathlib could match.
[C] LeanSearch        (n/a — no live LeanSearch MCP) — natural-language intent ("value of p-adic
                       L-function at 1 as Gauss sum times sum of p-adic logs of cyclotomic units")
                       has no mathlib referent: there is no p-adic L-function in mathlib at all.
[D] Grep mathlib src  Terms tried: `padicLFunction`, `LpFunction`, `Kubota`, `Leopoldt`,
                       `KubotaLeopoldt`, `p-adic L-function`, `padicL`, `padicLog` (p-adic log
                       *function*), `generalizedBernoulli`/Dirichlet-Bernoulli interpolation,
                       `gaussSum … log`. **Results:** NO p-adic L-function (`grep` for
                       `padicLFunction|Kubota|Leopoldt|LpFunction` over all of Mathlib → empty); NO
                       p-adic logarithm *function* (only `PadicVal`/`PadicNorm` valuation material);
                       NOTHING combining `gaussSum` with any `log`. Present-but-unrelated: complex
                       Dirichlet L-function (`LSeries/DirichletContinuation.lean`, with functional
                       equation and values at negative even/odd integers), Gauss sums
                       (`DirichletCharacter/GaussSum.lean`), Mahler basis on ℤ_p (`Padics/MahlerBasis`),
                       cyclotomic fields (`Cyclotomic/PrimitiveRoots`), Witt-vector Teichmüller (not
                       the Teichmüller *character*). None is the result or a more general one.
[E] Name pattern      Terms tried: `LpFunction`, `valueAtOne`, `value_at_one`, `*_one` in this
                       namespace. Closest hit `addChar_of_value_at_one` (`Padics/AddChar.lean`) is
                       about reconstructing an additive character on ℤ_p from its value at 1 via a
                       Mahler series — unrelated to L-values. No mathlib decl named or shaped like this.

Searched for both:
  - the user's current form (`LpFunction … 1 = …`) — **no hit** (`LpFunction` not in mathlib);
  - the literature-standard form (`L_p(1,χ) = −(1−χ(p)/p)·τ(χ̄)/f·Σ χ̄(a) log_p(1−ζ^a)`, all
    conductors) — **no hit**: the entire p-adic-L-function apparatus, the analytic p-adic logarithm,
    and the cyclotomic-unit log-sum are all absent from mathlib.

Concluded: **not in mathlib** (all 5 methods exhausted — live grep over the pinned mathlib for both
the user's form and the literature-standard form, plus every constituent primitive
`LpFunction`/`extLog`/p-adic-`log`/`Kubota`/`Leopoldt`). Mathlib has the *complex* Dirichlet
L-function and Gauss sums, but **no p-adic L-function, no analytic p-adic logarithm, and no special-value
formula of this kind.**

---

### Call sites — `PadicLFunctions.MeasureR.LpFunction_one`

Internal use count: **0** (within the project, not counting the declaring file; the only `grep` matches
in other files / earlier in this file are **docstring/comment references** at `ValuesAtOne.lean:98`,
`:763`, `:1338`, never a term-level application).
External-to-file callers: **0** files use it as a term.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ValuesAtOne.lean:98 | `/-- P6-p9 (the discharge for \`LpFunction_one\`): …` (docstring mention) |
| ValuesAtOne.lean:763 | `… \`LpFunction_one\`; the coprime-guarded form IS discharged there.` (comment) |
| ValuesAtOne.lean:1338 | `… undischargeable in \`LpFunction_one\`; the coprime-guarded …` (comment) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `LpFunction_one`?):
  - (none) — the formula is not re-derived anywhere; this theorem is its single statement.

**Interpretation.** `K = 0` internal uses here is the **expected** signal for a *capstone theorem*,
not a code smell. Per the skill's call-sites table, "K = 0, no inline re-derivation" reads as
"genuinely new / terminal result" — and the structural facts confirm it: this is the project's stated
**main result** (RJW Thm 6.1(ii)), the top of the dependency tree (it *consumes* T615, T616, the
CRT split, the mass identity, etc.), so nothing downstream is expected to consume *it* within the
project. It is a leaf-of-the-DAG headline, exactly the kind of result that is upstreamed rather than
re-used internally. This pushes toward a YES-family verdict (the result is the deliverable), not NO.

---

### Composition check (Phase 6)

Can `PadicLFunctions.MeasureR.LpFunction_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib call yielding `L_p(θ,1) = …`
  - Mathlib decls used: **none available** — mathlib has no `LpFunction`, no `padicLog`/`extLog`,
    no Gauss-sum×log special-value lemma.
  - Result: **fails** — there is nothing to compose. The statement even mentions project-only
    constants (`LpFunction`, `extLog`) that do not exist in mathlib, so no mathlib expression can
    denote, let alone prove, the identity.

Attempt 2: assemble from complex-L-function + Gauss-sum building blocks
  - Mathlib decls used: `ZMod.LFunction`, `gaussSum`, … (complex/finite-field, not p-adic)
  - Result: **fails** — these are about the *complex* L-function and finite-field Gauss sums; bridging
    to the p-adic L-value requires the entire interpolation/measure apparatus the project builds across
    55 files (`MeasureR`, `mahlerTransform`, `zetaEtaCleared`, `Ftilde`, `extLog`, …). That is a
    multi-thousand-line development, the antithesis of a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE.** The proof in the project is ~210 lines orchestrating four major
sub-results (`p_mul_constantCoeff_mahlerK_rhoTheta`, `sum_seriesEval_Ftilde`, `crt_collapse`,
`gaussSum_mul_coprime`) plus `field_simp`/`linear_combination` final algebra — a genuine theorem, not
a composition in disguise.

---

## Verdict: `PadicLFunctions.MeasureR.LpFunction_one`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): identified as **Leopoldt's `s = 1` formula** (Leopoldt 1964 /
  Iwasawa AM-74 / Washington Ch. 5 / RJW Thm 4.3 = the project's Thm 6.1(ii)). Standard form found
  **verbatim** in the RJW survey (the project's own cited source): `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ̄)/f)·Σ
  χ̄(a)log_p(1−ζ_f^a)` for primitive non-trivial odd χ of **arbitrary** conductor `f`, `p∤f`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the Lean theorem carries
  `hD1 : 1 < D`, restricting to a non-trivial tame part; the literature statement has **no such
  hypothesis** and covers the pure `p`-power conductor case `D = 1`, which the project itself records
  as deferred. Phase 4c found **no** modern-idiom reformulation (the bucket is driven by
  literature-weakening, not Bourbaki-2.0).
- Mathlib search (Phase 5): **not in mathlib** — no p-adic L-function, no analytic p-adic logarithm,
  no Gauss-sum×log special-value lemma; searched both the user's form and the literature-standard form.
- Composition check (Phase 6): **NOT-COMPOSABLE** — nothing to compose from (the constituents don't
  exist in mathlib); the actual proof is a ~210-line orchestration over a 55-file development.

**Rationale (two paragraphs):**

This is a genuinely famous theorem that mathlib does not have in any form — indeed mathlib has *none*
of the surrounding p-adic L-function theory (no Kubota–Leopoldt L-function, no Iwasawa-branch p-adic
logarithm, no measure/Mahler-transform apparatus on ℤ_p). The statement is the modern, correctly-typed
rendering (coefficient field = a complete ultrametric `ℚ_p`-algebra, the right generality per Phase 4a
row 2) of Leopoldt's formula relating `L_p(1,χ)` to p-adic logarithms of cyclotomic units — "one of
the first instances of the p-adic Beilinson conjectures". The literature match is not approximate: the
RJW survey the project cites states this identity verbatim as its Theorem 4.3/6.1(ii), and Phase 5
confirms the entire apparatus is absent upstream. So the result is squarely YES-family, not any NO
bucket: there is no mathlib decl to specialise from (rules out NO-mathlib-has-it) and no ≤3-call
composition (rules out NO-composable-from-mathlib).

It is **YES-but-generalise-first** rather than YES-add-as-is for one concrete reason grounded in
Phase 4b: the Lean theorem requires `1 < D` (a non-trivial prime-to-`p` tame conductor), whereas the
standard statement imposes no such restriction and explicitly **includes the pure `p`-power conductor
case `D = 1`**. The project's own module docstring confirms this is a known gap ("the pure `p`-power
case `D = 1` is deferred — decomposition R6, replan 4"): the current proof's norm-one discharge
`‖1 − ε^c‖ = 1` and CRT Gauss-product split genuinely need the tame part, so the narrow form is a
true *sub-case* of the theorem, not the whole theorem. Mathlib's iron rule is to add the maximally
general true statement, so the `D = 1` case should be discharged (filling the deferred sub-task) and
the two cases merged into a single conductor-agnostic `LpFunction_one` before upstreaming. Per the
skill, the EXPENSIVE cost of the `D = 1` route does **not** downgrade the verdict — closing that gap
is precisely the work that earns the result its place in mathlib. (A secondary, cheap cleanup —
making the Gauss sum `G` intrinsic rather than a threaded hypothesis — is a `/generalise`+`/cleanup`
ergonomics item, not the reason for this bucket.)

**Reason for the generalisation:**
- **LITERATURE-WEAKENING** (primary): Phase 4b found the user's form (`1 < D`) strictly narrower than
  the literature-standard form (arbitrary conductor `f`, including `f = pⁿ`). The missing `D = 1` case
  is part of the *same* theorem.
- MODERN-IDIOM: **not applicable** (Phase 4c: no Bourbaki-2.0 reformulation).

**Proposed restatement:**
```lean
-- drop `hD1 : 1 < D`; cover all conductors N = D·pⁿ (D ≥ 1, incl. the deferred pure p-power case).
theorem LpFunction_one_general {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {θK : DirichletCharacter K (D * p ^ n)} (hθ1 : θK ≠ 1) (hprim : θK.IsPrimitive)
    {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) /- + root-split, Gauss-sum data -/ :
    LpFunction p K η hζ hD χ 1
      = -(1 - θK ((p : ZMod (D * p ^ n))) * (p : K)⁻¹) * G⁻¹
        * ∑ c ∈ Finset.range (D * p ^ n),
            θK⁻¹ ((c : ZMod (D * p ^ n))) * extLog p (1 - ε ^ c) := by
  sorry  -- merge the proven D>1 route with the deferred D=1 route
```
Estimated cost of regeneralisation: **EXPENSIVE** (the `D = 1` case is a deferred open sub-task; the
norm-one and CRT-split steps must be re-derived for pure `p`-power conductor). Note: EXPENSIVE does
not downgrade the verdict.

Mathlib downstream this enables (if/when the whole apparatus is upstreamed): a conductor-agnostic
`L_p(1,χ)` formula is the natural consumer-facing statement — it specialises to the
`Q(ζ_p)`/`p`-power-conductor cases that dominate the classical literature (Washington's running
examples) and to the prime-to-`p` cases alike; the split-by-`D` form would force every downstream
user to know which sub-case they are in.

**Next action:** discharge the deferred `D = 1` case in the project (decomposition R6, replan 4), then
run `/generalise PadicLFunctions.MeasureR.LpFunction_one` to merge the two cases into the
conductor-agnostic statement above (tensioning against the RJW Thm 4.3 literature form). This is a
project-internal generalisation step; upstreaming to mathlib is gated on first contributing the
underlying p-adic L-function / p-adic logarithm / Iwasawa-measure apparatus, which mathlib currently
lacks entirely. (`/cleanup` for the intrinsic-`G` ergonomics can ride along.)

---

## Next step

Discharge the deferred `D = 1` (pure `p`-power conductor) case, then run
`/generalise PadicLFunctions.MeasureR.LpFunction_one` to produce the conductor-agnostic
`LpFunction_one_general` matching the literature-standard form (RJW Thm 4.3 / Iwasawa–Leopoldt). The
narrow `D > 1` form is correct and proven but is a strict sub-case of the standard theorem; mathlib
wants the full-generality statement. Upstreaming further depends on first bringing the p-adic
L-function infrastructure (none of which is currently in mathlib) along with it.
