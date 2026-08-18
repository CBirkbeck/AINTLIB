# `/mathlibable` report — `PadicLFunctions.norm_natCast_p`

**Final verdict: `NO-composable-from-mathlib`** — mathlib has the building blocks
(`Padic.norm_p` + `norm_algebraMap'`, glued by `map_natCast`); the statement is a
3-mathlib-call composition, which is exactly the existing 3-line proof body.
Mathlib already performs this same composition inline for `ℂ_p`
(`NumberTheory/Padics/Complex.lean`, `valuation_p`) without extracting a
reusable wrapper. No new mathlib lemma is justified.

This decl is the **equality** sibling of the already-assessed
`PadicLFunctions.norm_natCast_self_lt_one` (verdict `NO-composable-from-mathlib`):
the only differences are `Padic.norm_p` in place of `Padic.norm_p_lt_one`, and
`= (p:ℝ)⁻¹` in place of `< 1`. The verdict is the same; the only material
difference is that this decl has **5 internal call sites** (vs. 1), so it is a
genuinely-used project-local helper — but that bears on the *project's* internal
API, not on mathlib inclusion.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow here; the decl and all its dependencies were read directly from `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean` and `.lake/packages/mathlib/`).
- decl `PadicLFunctions.norm_natCast_p`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:88`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The extended (Iwasawa-branch) `p`-adic logarithm `extLog` (RJW §6, decomposition W6a): extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the exponential ball.

Dependencies read from source (all confirmed present in the pinned mathlib):
- `Padic.norm_p` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:854`, `@[simp]` — `‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹`.
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293`, `@[simp]` — `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
- `NormedDivisionRing.to_normOneClass` — `Mathlib/Analysis/Normed/Field/Basic.lean:62` (priority 900) — every `NormedField` is a `NormOneClass`, so the `norm_algebraMap'` hypothesis on `L` is discharged automatically.
- `map_natCast` (RingHom version) — `Mathlib/Data/Nat/Cast/Basic.lean:140` — used to rewrite `((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p])`.

Exact source (ExtLog.lean:86–91):
```lean
omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The `p`-adic norm of `p` in `L`. -/
theorem norm_natCast_p : ‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) from
      (map_natCast _ p).symm,
    norm_algebraMap', Padic.norm_p]
```

Section context (ExtLog.lean:32–35):
```lean
variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]
```
The theorem `omit`s `[IsUltrametricDist L]` and `[CompleteSpace L]` (line 86), so
its effective hypotheses are the minimal `[NormedField L] [NormedAlgebra ℚ_[p] L]`.

---

### Statement (Phase 1)

`PadicLFunctions.norm_natCast_p` is a theorem stating the following:

> Let `p` be a prime and let `L` be a normed field that is a normed `ℚ_p`-algebra.
> Then the norm in `L` of the image of the natural number `p` equals `1/p` (the
> `p`-adic absolute value of `p`).

Mathematically: in any normed `ℚ_p`-algebra-field `L`, the scalar embedding
`ℚ_p ↪ L` (`algebraMap`) is **norm-preserving** (an isometry, because `‖1‖_L = 1`),
so the absolute value on `L` restricts to the `p`-adic absolute value on the
scalars `ℚ_p`. Consequently `‖p‖_L = ‖p‖_{ℚ_p} = p^{-1} = 1/p`. Equivalently, `p`
is a uniformizer-valued element whose normalized absolute value is `1/p`. This is
the **algebra-map-compatible** normalization of the absolute value — the only one
consistent with `[NormedAlgebra ℚ_[p] L]` — and it is exactly `Padic.norm_p`
transported along the isometric embedding.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime / residue characteristic.
- `L : Type*`, `[NormedField L]` — a normed field (the extension field).
- `[NormedAlgebra ℚ_[p] L]` — `L` is a normed algebra over `ℚ_p`; this forces the
  norm on `L` to extend the `p`-adic norm on the scalar copy of `ℚ_p`. **Essential.**
- `[IsUltrametricDist L]`, `[CompleteSpace L]` — present in the section `variable`
  block but explicitly `omit`-ed for this theorem (line 86). The proof uses
  neither completeness nor the ultrametric inequality.

Hypotheses (Lean side): none beyond the typeclass context (it is a closed
equation about the structure).

Conclusion (math): `‖p‖_L = 1/p`.

Conclusion (Lean): `‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: a one-step helper equation supporting the `extLog` development (used to
read off `‖p‖` whenever a `p`-factor is pulled out of a norm). It is neither a
named-after-a-person theorem, nor a `## Main results` entry (the module is about
`extLog` / `extLogDomain_of_integral_norm_one`; this lemma is plumbing). It
introduces no new structure.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
report framing only; it did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: 1 substantive `rw` chain (three rewrites: `map_natCast`-cast,
`norm_algebraMap'`, `Padic.norm_p`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the Phase 2b
def-exemption table applies only to definitions). Recorded as a one-line note
and skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic absolute value norm of p equals 1/p uniformizer valuation ring maximal ideal" | yes | `\|p\|_p = 1/p`; `p` is a uniformizer of `ℚ_p`; valuation ring `O_K = {\|x\|≤1}`, maximal ideal `m_K = {\|x\|<1}` | MIT 18.785 (Li-Huerta), Cambridge p-adic analysis (Thorne), Wolfram MathWorld, Wikipedia *p-adic valuation*, Koblitz — uniform agreement: `\|p\| = 1/p` is the **definitional normalization** |
|  2 | WebSearch (general form)         | "extension of p-adic field unique norm extending Qp absolute value \|p\| = 1/p complete normed algebra" | yes | a complete field's absolute value extends **uniquely** to any finite/algebraic extension `L/ℚ_p`; the extension stays nonarchimedean and restricts to `\|·\|_{ℚ_p}` on scalars, hence `\|p\|_L = 1/p` | UChicago REU (Turner), Harvard Math 571 (Popa) ch. 3, W&M local-fields notes; **de Frutos-Fernández, "Formalizing Norm Extensions", ITP 2023 (arXiv 2306.17234)** is the relevant Lean-formalization context for norm extensions |
|  3 | WebSearch (named-after / aliases)| "nonarchimedean local field normalized absolute value norm of uniformizer p residue characteristic Serre Neukirch" | yes | for a local field `K/ℚ_p`, the *residue-normalized* value gives `\|ϖ\|_K = q^{-1}` (`q = p^f`); the **scalar/algebra-compatible** normalization restricting `\|·\|_{ℚ_p}` gives `\|p\|=1/p` | Warwick (Browning/Bouyer), Cambridge Part III Local Fields (Johansson), Umich notes; classical (Serre *Local Fields*, Neukirch ch. II). **Distinguishes the two normalizations** — see summary |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of `‖p‖ = 1/p` over a normed `ℚ_p`-algebra") | **n/a** | — | **MCP not configured in this session** (no `mcp__chatgpt*` tool in the deferred-tool list; `~/.claude/mcp-servers` present but no ChatGPT endpoint surfaced). Substituted with two extra WebSearch queries (#2, #3) at differing generality + the nLab fetch (#6), per the skill's documented fallback for an absent channel. |
|  5 | Local references                 | grep `.mathlib-quality/references/` (PadicLFunctions) for "norm p" / "valuation" / "uniformizer" | **n/a** | — | No `.mathlib-quality/references/` directory exists in this checkout, and no `refs/PadicLFunctions/` symlink is present (the references store is gitignored / LOCAL ONLY and unpopulated here). Recorded `n/a`; the fact is in every standard text cited above. |
|  6 | nLab                             | `p-adic number` / `valuation` | yes | nLab: `\|x\|_p = p^{-v_p(x)}`, so `\|p\|_p = p^{-1} = 1/p`; presented as a **definitional** property of the `p`-adic absolute value | Fundamental definitional fact, not a derived theorem |
|  7 | nCatLab (if categorical)         | — | **n/a** | — | Not a categorical concept (a norm equation on a valued field). The abstract statement is already covered by nLab `p-adic number` in #6. |
|  8 | Stacks Project (if alg geom)     | — | **n/a** | — | Not an algebraic-geometry / scheme statement. The underlying DVR / valuation ring appears in Stacks (e.g. tag 00I8), but this specific norm equation is elementary valuation theory fully covered by #1–#3. |
|  9 | MathOverflow / Math.StackExchange| "norm of p in extension of Qp equals 1/p" (covered via the #1–#3 web sweep) | yes | community answers reproduce: extend the valuation uniquely; the algebra-compatible normalization gives `\|p\| = 1/p` | A first-course `p`-adic fact; no research-level subtlety. Not separately tabulated to avoid a duplicate row. |
| 10 | recent arXiv (last 5 years)      | "Qp-algebra norm extension p-adic", "normed Qp-algebra absolute value of p" | n/a (no novel form) | — | The only relevant modern item is the formalization line (de Frutos-Fernández, ITP 2023, arXiv 2306.17234) about *norm-extension infrastructure*, not a new mathematical form of this equation. The mathematics is ~century old. |

Protocol pass check:
- WebSearch ran **3 distinct queries at different generality levels** (specific
  `ℚ_p` form, the general extension-field form, the uniformizer/local-field
  normalization) — ✓.
- ChatGPT MCP: **not available**; substituted with extra WebSearch + nLab, reason
  recorded — handled per fallback ✓.
- Local references checked (`n/a`, reason recorded) — ✓.
- nLab checked (hit) — ✓.
- Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason — ✓.

### Literature summary (Phase 3)

Concept identified as: **the norm of `p` in a nonarchimedean field extending
`ℚ_p`** — equivalently "the scalar absolute value extends the `p`-adic one, so
`‖p‖ = 1/p`". A basic fact of `p`-adic / local-field theory.

Sources agree on the standard form: **yes**. Every source gives `‖p‖ = p^{-1} = 1/p`
in `ℚ_p`, and the unique-extension theorem propagates this to any complete (indeed
any algebraic) normed extension `L/ℚ_p` *under the scalar-compatible
normalization*.

**One normalization nuance, explicitly resolved.** Local-field theory often uses
the *residue-field-normalized* absolute value, where a uniformizer `ϖ` of a
ramified/inertial extension has `‖ϖ‖_K = q^{-1}` with `q = p^f`, so that `‖p‖_K`
can be `p^{-e}`-flavoured depending on ramification. **That is a different
normalization.** The user's statement `‖p‖_L = p⁻¹` is the
**algebra-map-compatible** normalization: the one in which `algebraMap ℚ_[p] L` is
an isometry, i.e. `‖·‖_L` restricts *exactly* to `‖·‖_{ℚ_p}` on the scalar copy.
This is precisely what `[NormedAlgebra ℚ_[p] L]` together with `NormOneClass L`
forces (via `norm_algebraMap'`), and it is the only normalization consistent with
those typeclasses. So there is no disagreement: the user's form is the correct,
standard statement *for the structure it is stated over*, and it is exactly
`Padic.norm_p` transported along the isometric scalar embedding.

Most general standard form: in any normed field `L` whose norm extends the
`p`-adic one on a scalar copy of `ℚ_p` (i.e. any normed `ℚ_p`-algebra field),
`‖p‖_L = 1/p`. At maximal abstraction, the norm of any element of a nonarchimedean
valued field whose value is fixed by a norm-preserving embedding equals its value
in the subfield — `p` being the special case.

Generality dimensions where the literature varies:
- *Base / extension*: from `ℚ_p` itself (`Padic.norm_p`), to `ℤ_p` (`PadicInt.norm_p`),
  to finite extensions `L/ℚ_p` (local-field theory), to `ℂ_p = PadicAlgCl p`
  (mathlib `Padics/Complex.lean`, `valuation_p`), to an arbitrary normed
  `ℚ_p`-algebra field (the user's form).
- *Normalization*: scalar-compatible (`‖p‖ = 1/p`, the user's) vs.
  residue-normalized (`‖ϖ‖ = q^{-1}`). The user's typeclasses pin the
  scalar-compatible one.
- *Abstraction*: stated with an absolute value `|·|` or a valuation `v(p) = 1`;
  same up to `-log`.

Disagreement with the literature: **none**. The user's `L` (normed `ℚ_p`-algebra
field) sits at a natural, standard generality, with the canonical normalization.
The fact is not novel for mathlib in any way — it is the most elementary
consequence of the algebra-map being norm-preserving (`norm_algebraMap'`, already
in mathlib) combined with `‖p‖_{ℚ_p} = 1/p` (`Padic.norm_p`, already in mathlib).

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `‖p‖_L = 1/p` in any nonarchimedean field
whose norm extends the `p`-adic norm on a scalar copy of `ℚ_p` (scalar-compatible
normalization).

### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | normed field | any normed `ℚ_p`-algebra whose unit has norm 1 (so the scalar embedding is isometric) | mildly | The proof needs only `‖1‖ = 1` (`NormOneClass`) plus the `NormedAlgebra ℚ_[p]` structure. One could state it for a `NormedRing`/`NormedAlgebra` with `[NormOneClass L]` instead of a field, but: (a) the consuming file genuinely works with a `NormedField L` throughout, and (b) this is a *framing* change, not a free weakening that produces a strictly more useful statement. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `L` is a normed `ℚ_p`-algebra | the absolute value of `L` extends the `p`-adic one (isometric scalar embedding) | **NO (essential)** | This is exactly the hypothesis that makes `‖p‖_L = ‖p‖_{ℚ_p}` via `norm_algebraMap'`. Cannot be dropped. |
| 3 | `[IsUltrametricDist L]` | ultrametric | — | yes — **already dropped** | The theorem `omit`s it (line 86). Not used. |
| 4 | `[CompleteSpace L]` | complete | — | yes — **already dropped** | The theorem `omit`s it (line 86). Not used. |

The hypotheses actually consumed are the minimal pair `[NormedField L]` +
`[NormedAlgebra ℚ_[p] L]` (`NormedField ⇒ NormOneClass` automatically via
`NormedDivisionRing.to_normOneClass`). The two unused typeclasses are already
`omit`-ed, so the *effective* statement is already lean and at a sensible
generality.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within the normed-`ℚ_p`-algebra
framing). The two non-essential typeclasses are already omitted; the remaining two
are exactly what the one-line content needs. A `NormedRing + NormOneClass`
restatement is a *different framing* (and not what the consuming file uses), not a
strict weakening of this same statement.

Number of weakening opportunities found: 0 that keep this same statement and
improve it.
Proposed restatement: none (already minimal for the chosen framing).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | — | Already fully typeclass-driven (`NormedField` + `NormedAlgebra ℚ_[p]`); nothing to de-bundle. |
|  2 | sequences/metric → filters/topological? | no | — | A pointwise norm equation; no limit/convergence content to filter-ise. |
|  3 | construct an object → universal-property class? | no | — | No object constructed; it is an equation. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No subset/closure here. |
|  5 | vector-space/metric/field-specific → weakened typeclass? | partially | the valuation-theoretic form `v(p) = ...` via mathlib's `Valuation` / `ValuativeRel` layer, or `Valuation.val_map_eq` along an isometric algebra map | This is the *modern* mathlib idiom for "value of `p` in an extension". But it is a **different lemma in a different file**, and the concrete normed-`ℚ_p`-algebra computation does not become a contribution by re-phrasing it valuation-theoretically. It does not turn the user's lemma into something mathlib lacks. |
|  6 | 1-categorical → higher-categorical? | no | — | No categorical content. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | — | `p` is intrinsically a specific prime; generalising the *index* is meaningless for this fact. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (none that would make *this* lemma a mathlib
contribution). The only "more modern" framing — phrasing via mathlib's
`Valuation` / `ValuativeRel` layer — is a distinct, already-supported direction
(mathlib has `norm_extends`/valuation-extension API), not a reformulation that
upgrades the user's lemma into something worth adding. Reason this is not a
modernisation move: the user's lemma is a one-step consequence of two existing
`@[simp]` mathlib lemmas; "modernising" it just rediscovers other existing mathlib
API.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** (No definitional equalities or
typeclass-search paths introduced; the phase is skipped for `theorem`/`lemma`.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.norm_natCast_p`

[A] **Lean-Finder** — n/a: the hosted Lean-Finder Space was not reachable as a
    programmatic endpoint from this session. Substituted with Loogle (B) +
    LeanSearch (C) + grep (D) + name-pattern (E), which converge.

[B] **Loogle** — type-pattern queries:
    - `‖((?p : ℕ) : ?L)‖ = (?p : ℝ)⁻¹` → hits: `Padic.norm_p`
      (`‖(p : ℚ_[p])‖ = (p:ℝ)⁻¹`), `PadicInt.norm_p` (`‖(p : ℤ_[p])‖ = (p:ℝ)⁻¹`).
      **None over a general normed `ℚ_[p]`-algebra `L`.**
    - `‖algebraMap ?k ?L _‖ = ‖_‖` → hits: **`norm_algebraMap'`**
      (`[NormOneClass 𝕜'] : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`), `algebraMap_isometry`.
      Confirms the algebra-map-isometry building block exists generically.

[C] **LeanSearch** — natural-language query: "norm of p equals 1/p in a normed
    Qp-algebra / extension of the p-adic numbers" → returned `Padic.norm_p`,
    `PadicInt.norm_p`, and the `algebraMap` norm lemmas. **No general-`L` lemma.**

[D] **Grep mathlib src** — terms tried over `.lake/packages/mathlib/Mathlib/`:
    `norm_p`, `norm_natCast_p`, `norm_natCast`, `norm_algebraMap'`,
    `algebraMap_isometry`, `NormedAlgebra ℚ_[p]`, `valuation_p`, `norm_extends`.
    Findings:
    - `Padic.norm_p` @ `NumberTheory/Padics/PadicNumbers.lean:854` (`@[simp]`),
      `PadicInt.norm_p` @ `PadicIntegers.lean:234` — the scalar / `ℤ_p` forms.
    - `norm_algebraMap'` @ `Analysis/Normed/Module/Basic.lean:293` (`@[simp]`) —
      the norm-preserving algebra-map lemma; building block.
    - `NormedAlgebra ℚ_[p]` appears in mathlib **only** in
      `NumberTheory/Padics/Complex.lean` (for `ℂ_p = PadicAlgCl p`), where
      **`valuation_p` (line 99) does the EXACT same composition ad hoc**:
      `rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]; … rw [valuation_coe, norm_extends, Padic.norm_p, …]`
      — i.e. mathlib computes `‖(p : ℂ_p)‖` via the same `map_natCast` →
      norm-preserving-embedding → `Padic.norm_p` chain and does **not** extract a
      reusable general-`L` lemma. This is the canonical "building blocks present,
      inlined" signal.
    - Mathlib's general `norm_natCast` (`Analysis/Normed/Module/Basic.lean:75`)
      gives `‖(a:α)‖ = a` only under `[NormOneClass α] [NormSMulClass ℤ α]` — an
      archimedean-flavoured hypothesis that **fails** for a nonarchimedean
      `ℚ_p`-algebra (where `‖p‖ = 1/p ≠ p`), so it is correctly **NOT** a hit.

[E] **Name-pattern** (`lean_local_search` proxy via grep) — terms: `norm_p`,
    `norm_natCast_p`, `valuation_p`, `norm_extends`, `val_map`. Hits:
    `Padic.norm_p`, `PadicInt.norm_p`, `PadicAlgCl.valuation_p`,
    `SpectralNorm.norm_extends` / valuation-extension lemmas. These confirm the
    content is standard and that mathlib has the scalar fact + the
    norm-preserving-embedding fact, but not the packaged general-`L` equation.

Searched for both:
- the user's current form (`‖(p:L)‖ = p⁻¹` over a general normed `ℚ_p`-algebra) —
  **not found** as a single declaration;
- the literature-standard / more-general pieces (`‖p‖_{ℚ_p} = 1/p`; algebra-map
  norm preservation; the `ℂ_p` instance) — **all present** as separate pieces
  (`Padic.norm_p`, `norm_algebraMap'` / `algebraMap_isometry`,
  `PadicAlgCl.valuation_p`).

Concluded: **found building blocks** (`Padic.norm_p`, `norm_algebraMap'`,
`map_natCast`; plus `NormedDivisionRing.to_normOneClass` to discharge
`NormOneClass L` for free) — their composition yields our exact form, and mathlib
itself uses this same composition inline for `ℂ_p`. The packaged general-`L`
statement is **not** in mathlib (all five methods exhausted, plus the
literature-standard form).

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `PadicLFunctions.norm_natCast_p`

Internal use count: **K = 5** (within `PadicLFunctions`, not counting the
declaring line). All resolve to *this* decl (`PadicLFunctions.norm_natCast_p`),
confirmed by reading each line; they are distinct from the unrelated mathlib
`PadicInt.norm_natCast_p_sub_one` and the private `ResidueZeta` helper
`norm_natCast_pow_sub_one_le` (which merely *calls* our decl).
External-to-file callers: **2 distinct files** (`ExtLog.lean` itself —
multiple times — and `ResidueZeta.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:120` | `· rw [hm, Nat.cast_mul, norm_mul, norm_natCast_p p]` (interior `p ∣ choose` term bound, in `norm_pow_p_sub_one_le`) |
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:267` | `rw [hcoe, norm_mul, norm_natCast_p p]` (pushing `z^j − z^i = p·s` to a norm bound, in `exists_pow_sub_one_norm_le`) |
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:296` | `rw [norm_natCast_p p]; have := hp.out.pos; positivity` (proving `(p:L) ≠ 0` in `natCast_p_ne_zero`) |
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:318` | `rwa [norm_mul, norm_mul, norm_zpow, norm_zpow, norm_natCast_p p, …]` (matching `p`-valuations in `extLog_witness_smul_eq`) |
| `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:1454` | `rw [hK, norm_mul, norm_natCast_p p]` (Fermat-bound step `‖(a:K)^{p−1} − 1‖ ≤ p⁻¹` in `norm_natCast_pow_sub_one_le`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`norm_natCast_p`?): **none** found within the project — but note mathlib itself
re-derives the same `‖p‖` computation inline for `ℂ_p` in
`NumberTheory/Padics/Complex.lean:99` (`valuation_p`, via `map_natCast` +
`norm_extends` + `Padic.norm_p`), which is exactly the pattern this lemma packages.

Call-sites signal (per the Phase 6.0.1 table): **K = 5 internal uses, no inline
re-derivation → "Real API; consumers depend on it."** This is the strongest
positive composability signal in the table — a genuinely-used helper across two
files. *However*, this signal governs whether the project should keep it
**locally**, not whether **mathlib** should receive it: the relevant mathlib
question is the composition check below, and mathlib's own `ℂ_p` code shows the
established mathlib practice is to inline this very chain rather than ship a
wrapper.

### Composition check (Phase 6)

Can `norm_natCast_p` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the project's own proof, which *is* the composition):
```lean
example : ‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) from (map_natCast _ p).symm,
    norm_algebraMap', Padic.norm_p]
```
- Mathlib decls used: `map_natCast` (rewrite `(p:L) = algebraMap ℚ_[p] L (p:ℚ_[p])`),
  `norm_algebraMap'` (drops to `‖(p:ℚ_[p])‖`, with `NormOneClass L` free via
  `NormedDivisionRing.to_normOneClass`), `Padic.norm_p` (`= (p:ℝ)⁻¹`).
- Result: **succeeds** — this is literally the 3-rewrite proof body in
  `ExtLog.lean:89–91`.
- Notes: per the Phase 6b heuristics, a single `rw [...]` chaining one cast
  normalisation + two named mathlib rewrites is a clean composition. It is **not**
  a "proof in disguise": no `have`-chains, no `nlinarith`/`ring_nf`/`aesop`, no
  case analysis. Both `norm_algebraMap'` and `Padic.norm_p` are `@[simp]`, so even
  `by simp [map_natCast]` (modulo cast direction) would close it.

Attempt 2 (even tighter): `‖(p:L)‖` rewrites by `norm_algebraMap'` to `‖(p:ℚ_[p])‖`,
then `Padic.norm_p` finishes; the only glue is the `map_natCast` cast which
`simp`/`norm_cast` handles.

Conclusion: **COMPOSABLE** (exactly 3 mathlib calls; the project's own proof is
the witness, and mathlib's `valuation_p` for `ℂ_p` is the same composition).

---

## Verdict: `PadicLFunctions.norm_natCast_p`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the fact `‖p‖ = 1/p` in a nonarchimedean field
  extending `ℚ_p` (scalar-compatible normalization) is a fundamental,
  century-old definitional fact (Koblitz, Serre, Neukirch; nLab calls it
  definitional). Standard form confirmed across ≥3 channels; the only nuance —
  scalar-compatible vs. residue-normalized absolute value — is resolved in the
  user's favour by the `[NormedAlgebra ℚ_[p] L]` typeclass.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the chosen framing (the two
  unused typeclasses are already `omit`-ed); Phase 4c "no" — no modern-idiom
  upgrade turns it into a contribution.
- Mathlib search (Phase 5): not present as a single decl over a general normed
  `ℚ_[p]`-algebra, but **all** building blocks are present — `Padic.norm_p`
  (`@[simp]`), `norm_algebraMap'` (`@[simp]`, `+ NormedDivisionRing.to_normOneClass`),
  `map_natCast`; mathlib even performs the same inline composition for `ℂ_p` in
  `Padics/Complex.lean` (`valuation_p`).
- Composition check (Phase 6): COMPOSABLE — the project's own 3-rewrite proof is
  the ≤3-call composition; K = 5 internal call sites across 2 files, no external
  (downstream-library) consumer.

**Rationale (synthesis):**

This theorem is a thin wrapper around two `@[simp]` mathlib lemmas: the scalar
fact `Padic.norm_p` (`‖p‖_{ℚ_p} = 1/p`) and the norm-preserving algebra-map
identity `norm_algebraMap'` (`‖algebraMap ℚ_[p] L x‖ = ‖x‖`, whose `NormOneClass L`
hypothesis is automatic for the `NormedField L` here via
`NormedDivisionRing.to_normOneClass`). The cast bookkeeping
`(p:L) = algebraMap ℚ_[p] L (p:ℚ_[p])` is just `map_natCast`. The decisive
evidence is that **mathlib already performs this very composition ad hoc** when it
needs `‖(p : ℂ_p)‖` in `NumberTheory/Padics/Complex.lean` (`valuation_p`, line 99):
it rewrites along `map_natCast (algebraMap ℚ_[p] _)`, then applies `norm_extends`
and `Padic.norm_p` — the same three-step chain — and pointedly does **not** extract
a reusable general-`L` wrapper. That is the right mathlib call: the composition is
short, the hypotheses are exactly the ambient typeclass context, and the more
abstract statement (value of `p` under an isometric extension) is already covered
by mathlib's valuation/`norm_extends` layer. Nothing here is novel for mathlib, the
generality is already correct, and the proof is a 3-call composition rather than a
genuine new lemma — so this is `NO-composable-from-mathlib`, not a YES bucket. (It
is *not* `NO-mathlib-has-it`: there is no single mathlib decl that states this over
a general normed `ℚ_p`-algebra; Phase 5 found only the scalar/`ℤ_p`/`ℂ_p`
specializations, hence the composable verdict over the has-it verdict.)

This verdict is consistent with the already-filed sibling
`PadicLFunctions.norm_natCast_self_lt_one` (`‖(p:L)‖ < 1`, verdict
`NO-composable-from-mathlib`): the present decl is its equality form, swapping
`Padic.norm_p_lt_one`→`Padic.norm_p` and `< 1`→`= p⁻¹`. The one material
difference — K = 5 internal uses here vs. K = 1 there — strengthens the case for
**keeping it as a project-local helper**, but does not change the mathlib verdict:
mathlib should not receive the wrapper.

**WHY not (refactor-actionable detail):** Mathlib has the building blocks; the
user's form is an exactly-3-mathlib-call composition (and the project's own proof
already *is* that composition). No new mathlib lemma is justified.

Mathlib building blocks:
- `Padic.norm_p` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:854` (`@[simp]`) —
  `‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹`.
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293` (`@[simp]`) —
  `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
- `NormedDivisionRing.to_normOneClass` — `Mathlib/Analysis/Normed/Field/Basic.lean:62`
  (priority 900) — supplies `NormOneClass L` from `NormedField L` automatically.
- `map_natCast` — `Mathlib/Data/Nat/Cast/Basic.lean:140` — for the cast
  normalisation `((p:ℕ):L) = algebraMap ℚ_[p] L ((p:ℕ):ℚ_[p])`.

Composition sketch (≤3 lines — this is the existing proof body):
```lean
example : ‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : L) = algebraMap ℚ_[p] L ((p : ℕ) : ℚ_[p]) from (map_natCast _ p).symm,
    norm_algebraMap', Padic.norm_p]
```

Call sites in our project (from Phase 6.0): **K = 5** — `ExtLog.lean:120, 267,
296, 318` and `ResidueZeta.lean:1454`.

Refactor plan (for *mathlib-inclusion* purposes): do **not** open a mathlib PR.
The wrapper would be inlinable at each of the 5 call sites by substituting the
3-rewrite composition above — concretely, at each `... norm_natCast_p p ...`
occurrence, replace the reference with the inline chain
`rw [show ((p:ℕ):L) = algebraMap ℚ_[p] L ((p:ℕ):ℚ_[p]) from (map_natCast _ p).symm, norm_algebraMap', Padic.norm_p]`
(adjusting the surrounding `rw` list accordingly; note 4 of the 5 sites already
sit inside a `norm_mul`/`norm_zpow` `rw` chain, so the `Padic.norm_p`/`norm_algebraMap'`
rewrites can be folded directly into that chain).

**Caveat (project-local nuance, NOT a blocker for the verdict).** Because the
same expression `‖((p:ℕ):L)‖` recurs at 5 sites across two files in this
development, keeping `norm_natCast_p` as a **named, project-local helper is good
engineering** — arguably better than inlining the 3-rewrite chain five times. The
verdict `NO-composable-from-mathlib` is strictly about **mathlib inclusion**:
mathlib should not receive this wrapper (its own `ℂ_p` code shows the convention
is to inline). The project may, and probably should, retain it locally. That is an
internal-API decision, not a mathlib contribution.

Next action: do **not** open a mathlib PR for this lemma. Either inline the
≤3-call composition (`Padic.norm_p` + `norm_algebraMap'` via `map_natCast`) at its
5 call sites, or — recommended, given K = 5 — **retain it as a project-local
helper** unchanged. When mathlib needs the general fact it already has the
`norm_extends` / valuation-extension API plus the scalar `Padic.norm_p`; no
upstreaming is warranted here.

---

## Next step

Do not open a mathlib PR. The statement is an exactly-3-mathlib-call composition
(`Padic.norm_p` + `norm_algebraMap'`, glued by `map_natCast`) — the same chain
mathlib already inlines for `ℂ_p` in `Padics/Complex.lean` (`valuation_p`). Given
its 5 internal call sites, retaining `norm_natCast_p` as a project-local helper is
the recommended engineering choice; mathlib inclusion is not justified, as mathlib
has both the building blocks and (in its `norm_extends`/valuation layer) the more
abstract fact.
