# `/mathlibable` report — `PadicLFunctions.MeasureR.norm_pow_sub_one_eq_one_of_unit`

**Final verdict: `BORDERLINE-needs-human`** (the substantive mathematical content is
mathlib-worthy and should be generalised first; *this specific declaration* is a
project-narrow `N = D·p^n` bookkeeping wrapper with one internal call site — the
right grain for mathlib is its sub-lemma, not the wrapper, and that is a human call).

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — Phase 0 fallback.
- decl `PadicLFunctions.MeasureR.norm_pow_sub_one_eq_one_of_unit`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:104`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  computes the p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), Leopoldt); this decl is the §6 "norm-one discharge" (P6-p9) feeding the headline value theorem.

---

### Statement (Phase 1)

`norm_pow_sub_one_eq_one_of_unit` is a **theorem** stating the following:

Let `K` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra
(`[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] …`). Let `D > 1` be
prime to `p`, let `n ≥ 0`, and let `ε ∈ K` be a primitive `(D·pⁿ)`-th root of unity.
If `c` is a natural number whose residue is a **unit** in `ℤ/(D·pⁿ)` (equivalently
`gcd(c, D·pⁿ) = 1`), then the p-adic absolute value `‖εᶜ − 1‖ = 1`.

Mathematically: the tame part of a root of unity, raised to an exponent coprime to
the order, stays a unit of the ring of integers after subtracting 1. The `pⁿ` (wild)
part of the order contributes a factor `(εᶜ)^{pⁿ}` whose order is the prime-to-`p`
integer `D`, and *that* difference is the genuine norm-one fact (Φ_D(1) = 1); the
ultrametric then lifts norm-one from the `pⁿ`-power back to `εᶜ − 1` itself.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K` — complete ultrametric normed `ℚ_p`-algebra (a `ℂ_p`-like coefficient field).
- `D : ℕ`, `[NeZero D]`, `hD1 : 1 < D`, `hD : ¬ p ∣ D` — the **tame** conductor.
- `n : ℕ` — the wild (p-power) exponent; `N = D·pⁿ`.
- `ε : K`, `hε : IsPrimitiveRoot ε (D · pⁿ)` — a primitive root of the full order.
- `c : ℕ`, `hcu : IsUnit ((c : ZMod (D·pⁿ)))` — coprimality of the exponent.

Hypotheses (Lean side):
- `hD1 : 1 < D` — used to force `¬D∣c` from `Coprime c D` (rules out `D = 1`).
- `hD : ¬ p ∣ D` — the tame condition (so `Φ_D(1) = 1`, not `= p`).
- `hε : IsPrimitiveRoot ε (D·pⁿ)` — pinned order.
- `hcu : IsUnit (c : ZMod (D·pⁿ))` — coprimality of `c` and `N`.

Conclusion (math): `‖εᶜ − 1‖ = 1`.
Conclusion (Lean): `‖ε ^ c - 1‖ = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/discharge lemma (docstring tags it "P6-p9 the discharge for
`LpFunction_one`"). Not a named theorem, not a `## Main results` entry; it is the
mixed-modulus specialisation of the genuinely-substantive `IsPrimitiveRoot.norm_pow_sub_one_eq_one`.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded only
for framing.)

### One-line check (Phase 2b)

Body line count: ~17 substantive lines (a real proof with `have` bookkeeping).
One-liner verdict: **n/a** (kind is theorem, and the body is multi-line). Section skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic norm of root of unity minus one prime to p is a unit valuation"                                | yes  | for `ord(ζ)` coprime to `p`, `v_p(1−ζ) = 0` (i.e. `‖1−ζ‖ = 1`); for the `p`-power part `v_p(1−ζ_{pˡ}) > 0` | dpmms Cambridge & kconrad p-adic notes; Wikipedia p-adic valuation; explicit: prime-to-`p` roots are units, only the wild part lowers valuation |
|  2 | WebSearch (general form, local fields) | "norm valuation 1 minus zeta_n root of unity non-archimedean local field tamely ramified general"  | yes  | tame ⇔ `p ∤ ramification`; `n` coprime to `p` ⇒ μ_n unramified, so `1 − ζ_n` is a unit | PAWS 2024 (Hsu) local-fields notes; Browning/Bouyer Local Fields; Crew LCFT — the *most general* setting is any complete DVF / non-arch local field |
|  3 | WebSearch (named-after / mechanism) | "cyclotomic polynomial value at 1 equals 1 for non-prime-power 1-zeta unit Phi_n(1)"                | yes  | **`Φ_n(1) = 0` if `n=1`; `= p` if `n = pᵉ`; `= 1` otherwise**; via `n = ∏_{d∣n, d>1} Φ_d(1)` | Wolfram MathWorld; arXiv 1611.06783; `Φ_n(1)=e^{Λ(n)}` (von Mangoldt) — this is the exact mechanism the project proof uses (`prod_one_sub_pow_eq_order`) |
|  4 | WebSearch (cyclotomic / tame)    | "cyclotomic field prime to p root of unity 1 - zeta unit ramification tame"                            | yes  | tame χ-cyclotomic units `N(ζ_{nf} − 1)` for `n` prime to `p`; Eisenstein only in the wild prime-power case | kconrad cyclotomic.pdf; arXiv 0905.4382 (Rubin); IITB ramification notes |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                           | n/a  | directory absent                  | `references/` not present in the project; `refs/` symlink also absent. Recorded `n/a`. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/cyclotomic+field`                                                      | no   | nLab "cyclotomic field" page is a stub (one-line definition) | no p-adic/valuation content; nLab does not carry this analytic fact |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                 | not a categorical concept — it is a metric/valuation statement about a specific element |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                 | not a scheme-theoretic statement; the relevant content (DVR ramification of `ℤ[ζ]`) is classical local-field theory, covered by channels 2 & 4 |
|  9 | MathOverflow / Math.StackExchange| folded into #1/#3 (valuation of `1 − ζ`, `Φ_n(1)` value)                                                | yes  | same as #1, #3 (standard exercise: `v_p(1−ζ_m)=0` for `p∤m`)  | the result is folklore/textbook-exercise level; many MO/MSE threads, no canonical single citation |
| 10 | recent arXiv (last 5 years)      | (covered by #1 explicit p-adic Hodge / Stickelberger refs; #3 cyclotomic-at-roots-of-unity)            | yes  | confirms #1/#3; no *new* formulation | arXiv math/0303226 (Stickelberger for p-adic Gauss sums) uses exactly "ε_D^c − 1 is a p-adic unit" as a standing fact |
| 11 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of `‖1−ζ‖` for tame roots")              | n/a  | server unavailable                | `plugin:mathlib-quality:chatgpt-math` **failed to connect** (configured for a different machine's home path `/home/chris/...`). Compensated by 5 web channels + nLab. |

The protocol passed: WebSearch ran **4** distinct queries across generality levels
(specific p-adic form / general local-field form / cyclotomic-`Φ_n(1)` mechanism /
tame-ramification framing); local refs checked (`n/a`, absent); nLab checked (stub,
no content); Stacks / nCatLab recorded `n/a` with reasons; MathOverflow/arXiv folded
in. ChatGPT MCP was unavailable (recorded `n/a` with the connection-failure reason)
and was over-compensated by the five web channels.

### Literature summary (Phase 3)

Concept identified as: **the p-adic (non-archimedean) absolute value of `1 − ζ` for a
root of unity `ζ` of order coprime to the residue characteristic `p`** — the
"tame-part unit" fact. Mechanism: the cyclotomic value `Φ_D(1) = 1` for `D > 1` not a
prime power, i.e. `∏_{c}(1 − ζ_D^c) = ±1`, so each ultrametric factor `‖1 − ζ_D^c‖`
is forced to be exactly 1. The mixed case `N = D·pⁿ` reduces to the tame `D`-case by
raising to the `pⁿ` power.

Sources agree on the standard form: **yes**. The canonical statement is "`v_p(1 − ζ_m) = 0`
whenever `p ∤ m`" (equivalently `‖1 − ζ_m‖ = 1`), with the wild-part exception
`v_p(1 − ζ_{pˡ}) = 1/(pˡ⁻¹(p−1)) > 0`.

Most general standard form: over **any non-archimedean field / complete DVF of residue
characteristic `p`** (not just `ℚ_p` or `ℂ_p`): for any root of unity `u` whose order is
coprime to `p`, with `u ≠ 1`, `‖u − 1‖ = 1`. No "primitive `D`-th root + `IsPrimitiveRoot`
+ `D·pⁿ` factoring" packaging appears in the literature — that is a Lean-side reduction,
not a mathematical statement.

Generality dimensions where the literature varies:
- **Coefficient field**: literature states it for *any* non-arch local field / complete
  DVF (the project pins `NormedAlgebra ℚ_[p] K` + `IsUltrametricDist`). The project form
  is essentially maximal among ℚ_p-algebras but the literature is broader (any DVF).
- **Element**: literature is "any root of unity of order coprime to `p`"; the project
  uses `εᶜ` with `ε` a primitive `(D·pⁿ)`-th root and `c` coprime — a re-indexing that
  *introduces the unnecessary wild `pⁿ` factor* and then strips it back off.

Disagreement with the literature: the literature uses the *clean tame statement*
("order coprime to `p` ⇒ `‖u−1‖=1`"); the project's wrapper carries an extra `pⁿ`
factor in the order purely to match the `N = D·pⁿ` modulus of the surrounding
`L_p(θ,1)` proof. The genuine content is captured one level down, in the project's own
`IsPrimitiveRoot.norm_pow_sub_one_eq_one`.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): *for `u` a root of unity of order coprime to
`p` in a non-archimedean field of residue characteristic `p`, `u ≠ 1` ⇒ `‖u − 1‖ = 1`.*

### 4a. Generality status table — `norm_pow_sub_one_eq_one_of_unit`

| # | Parameter / hypothesis                       | Current Lean form                       | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------------------|-----------------------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` | complete ultrametric `ℚ_p`-algebra | any complete DVF / non-arch local field of residue char `p` | yes (broader) | the proof uses only: `‖·‖` ultrametric, `‖ζ‖=1` for finite-order, and `Φ_D(1)` having norm 1 via `p ∤ D`. `CompleteSpace` is **omitted** (`omit` line 96) — already not used. The `ℚ_p`-algebra is used only through `Padic.norm_natCast_eq_one_iff` in the sub-lemma; a general DVF restatement is possible but is mathlib-infrastructure work. |
| 2 | order `= D·pⁿ` with `ε` primitive, `c` coprime | mixed modulus `N = D·pⁿ`, `IsUnit (c:ZMod N)` | order coprime to `p` (no `pⁿ` factor) | **yes** (this is the wrapper's whole reason to exist) | the `pⁿ` factor is artificial: the proof immediately raises to the `pⁿ` power (`hεD : ε^{pⁿ}` is primitive `D`-th) to *remove* it, then lifts back. The literature element has order coprime to `p` outright. |
| 3 | `hD1 : 1 < D`                                 | `D > 1`                                 | `D > 1` (else `Φ_1(1)=0`, no root `≠1`) | NO | genuinely needed: `D = 1` means the only "tame root" is `1`, where `‖1−1‖=0≠1`. Matches the literature `n > 1` exclusion. |
| 4 | `hD : ¬ p ∣ D`                                | tame condition                          | order coprime to `p`              | NO | this IS the tameness hypothesis; it is exactly the literature condition. Cannot weaken (the wild case gives `‖·‖<1`). |
| 5 | `hcu : IsUnit (c : ZMod (D·pⁿ))`              | `gcd(c, D·pⁿ)=1`                         | `D ∤ c` (after stripping `pⁿ`)    | yes (re-expressible) | the proof derives `¬D∣c` from this (`hDc`); the sub-lemma only needs `¬D∣c`. The `ZMod`-unit phrasing is downstream-convenience, not the natural hypothesis. |

### 4b. Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along axes 1, 2, 5).
Number of weakening opportunities found: **3** (broaden coefficient field; drop the
artificial `pⁿ` factor; replace the `ZMod`-unit hypothesis with the natural `¬D∣c` /
"order coprime to `p`").

Proposed restatement (the literature-standard / already-in-project clean form):

```lean
-- this is ESSENTIALLY the project's existing sub-lemma, the genuinely-reusable result:
theorem IsPrimitiveRoot.norm_pow_sub_one_eq_one
    {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
    {ζ : L} {D : ℕ} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {c : ℕ} (hc : ¬ D ∣ c) : ‖ζ ^ c - 1‖ = 1
-- (and, for a true mathlib PR, the maximally-general DVF restatement:
--   `u` a root of unity, `orderOf u` coprime to `p`, `u ≠ 1` ⇒ `‖u − 1‖ = 1`,
--   over any complete non-archimedean field of residue characteristic `p`.)
```

Cost of restatement: **CHEAP** for the project-internal `D`-form (it already exists —
`IsPrimitiveRoot.norm_pow_sub_one_eq_one` in `Coefficients.lean:211`); **MODERATE→EXPENSIVE**
for the maximally-general DVF form (needs a residue-characteristic-coprime ⇒ unit
norm fact stated over `IsDiscreteValuationRing`/`Valued` instead of `Padic`, plus the
`prod_one_sub_pow_eq_order` ultrametric-pinning argument re-homed off `Padic.norm_natCast_eq_one_iff`).

The target `norm_pow_sub_one_eq_one_of_unit` is **STRICTLY NARROWER** than even the
project's own sub-lemma: it adds an artificial `pⁿ` factor and a `ZMod`-unit hypothesis
on top, purely to fit the `N = D·pⁿ` modulus of the headline `L_p(θ,1)` proof.

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let `K` be a foo" preambles → typeclasses?                                                               | no       | already fully typeclass-driven (`NormedField`/`NormedAlgebra`/`IsUltrametricDist`) | — |
|  2 | sequences/metric where filters/topological would generalise?                                             | no       | a single norm equality; no limit/convergence structure to filter-ise | — |
|  3 | construct an object where a universal property would characterise it?                                    | no       | a proposition about a fixed element, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy (modules / pseudometric / (semi)ring)?   | **yes**  | state over a general complete non-archimedean field / DVF (residue char `p`) instead of a `ℚ_p`-algebra; the only `ℚ_p`-specific input is `Padic.norm_natCast_eq_one_iff` | unifies with mathlib's `Valued`/`IsDiscreteValuationRing` API; the result becomes usable for *any* tame cyclotomic local computation, not just `ℚ_p`-coefficients |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive groups/monoids?                                              | partial  | the exponent indices are intrinsic to "root of unity of given order"; the natural generalisation is the *order-coprime-to-`p`* form (axis 2 in 4a), already captured by the restatement | folds the `D·pⁿ`/`ZMod`-unit bookkeeping into the clean "order coprime to `p`" statement |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (row 5 / row 7).
  - Proposed mathlib-idiomatic restatement: the maximally-general DVF form —
    `for u a root of unity of order coprime to p in a complete non-archimedean field
    of residue characteristic p, u ≠ 1 ⇒ ‖u − 1‖ = 1`.
  - Cost: **MODERATE→EXPENSIVE** (re-home the `Padic.norm_natCast_eq_one_iff` step onto a
    general `Valued`/DVR statement; the `prod_one_sub_pow_eq_order` ultrametric argument
    survives unchanged).
  - Mathlib downstream this enables: tame-cyclotomic unit computations over any local
    field (Iwasawa theory, Stickelberger, cyclotomic-unit constructions) — exactly the
    `N(ζ_{nf} − 1)` tame χ-cyclotomic units the literature (Rubin, arXiv 0905.4382) uses.
  - Real mathematical improvement: it removes the `ℚ_p`-coefficient restriction and the
    artificial `pⁿ` factor, giving the *clean tame-part unit fact* that mathlib currently
    lacks in non-archimedean-absolute-value form (mathlib only has the **field-norm**
    `Algebra.norm K L` version, and only in the **wild** prime-power case — see Phase 5).

Crucially: the modern-idiom target is **not** the target declaration itself; it is the
target's *sub-lemma* `IsPrimitiveRoot.norm_pow_sub_one_eq_one`, generalised. The target is
a narrowing of that sub-lemma.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (theorems introduce no definitional equalities
or typeclass-search paths). Skipped.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `norm_pow_sub_one_eq_one_of_unit`

```
[A] Lean-Finder       — no MCP server connected (n/a: server absent)
[B] Loogle            — no MCP server connected (n/a: server absent)
[C] LeanSearch        — no MCP server connected (n/a: server absent)
[D] Grep mathlib src  ‖·^c - 1‖=1 / norm_pow_sub_one / norm_sub_one_eq_one
                       / prod_one_sub_pow / IsOfFinOrder.norm / rootsOfUnity-norm
                       → see findings below
[E] Name pattern      norm_pow_sub_one_eq_one / norm_sub_one_eq_one_of_pow
                       → only THIS project (Coefficients.lean, ValuesAtOne.lean,
                         NonTame.lean); no mathlib hit
```

Searched for both the user's current form (mixed `D·pⁿ`, `ZMod`-unit) **and** the
literature-standard form (tame root, `‖u−1‖=1`). Grep findings (the load-bearing ones):

- **`IsPrimitiveRoot.prod_one_sub_pow_eq_order`** — mathlib HAS the algebraic product
  identity `∏(1 − ζ^k) = order`. This is the *building block* the project proof rests
  on. It is in mathlib (used by `FltRegularBernoulli` too). **But it is the algebraic
  identity, not the p-adic-norm consequence.**
- **`IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`, `…norm_pow_sub_one_of_prime_ne_two`,
  `…norm_pow_sub_one_two`, `…norm_pow_sub_one_eq_prime_pow_of_ne_zero`**
  (`Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`) — mathlib HAS
  `norm_pow_sub_one_*` lemmas, **but they compute the FIELD norm `Algebra.norm K L (ζˢ − 1)`**
  (`= p^…`), require `Irreducible (cyclotomic n K)`, and are stated for the **WILD**
  `p^(k+1)`-power case. This is a *different quantity* (relative field norm, not the
  non-archimedean absolute value `‖·‖`) and the *opposite* (wild, not tame) regime. **Not a match.**
- **`IsOfFinOrder.norm_eq_one`** (`Mathlib/Analysis/Normed/Ring/Finite.lean`) — `‖ζ‖ = 1`
  for finite-order `ζ`. A building block (gives `‖εᶜ‖=1`, which the project re-proves as
  `norm_eq_one_of_pow_eq_one`), **not** the `‖εᶜ − 1‖ = 1` statement.
- **`Complex.norm_eq_one_of_pow_eq_one`**, `Complex.norm_eq_one_of_mem_rootsOfUnity` — the
  archimedean (`ℂ`) analogue of `‖ζ‖=1`, irrelevant to `‖ζ−1‖` and to the non-arch setting.
- **`NumberField.…norm_toInteger_sub_one_eq_one`** (`Cyclotomic/Basic.lean:316`) — again a
  *field-norm* statement over number fields, not the local absolute value.

Concluded: **not in mathlib** (all grep/name methods exhausted, both forms searched).
Mathlib has the *building block* `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and the
finite-order `‖ζ‖=1` fact, plus a *wild-case field-norm* family, but it does **not** have
the **tame-part non-archimedean absolute-value** statement `‖ζᶜ − 1‖ = 1` in any form —
neither the target's mixed-modulus wrapper nor its clean sub-lemma. (Lean-search MCP
servers were unavailable; the grep + name-pattern sweep over `Mathlib/NumberTheory/Cyclotomic/`
and `Mathlib/Analysis/Normed/` is thorough enough to be confident.)

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `norm_pow_sub_one_eq_one_of_unit`

Internal use count: **K = 1** (within the project, excluding the declaring line 104).
External-to-file callers: **0 distinct files** (the one use is in the same file).

| Caller file:line          | Usage pattern (one-line excerpt)                                                          |
|---------------------------|-------------------------------------------------------------------------------------------|
| ValuesAtOne.lean:1736     | `‖ε ^ c - 1‖ = 1 := fun c _ hcu => norm_pow_sub_one_eq_one_of_unit hD1 hD hε hcu` (the `hnorm` discharge feeding the headline `L_p(θ,1)` value theorem) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the target?):
- `NonTame.lean:50, 118` and `isUnit_root_mul_*` (NonTame.lean:40–130) derive the SAME
  tame norm-one fact **but via the sub-lemma `IsPrimitiveRoot.norm_pow_sub_one_eq_one`
  directly** (pure `D`-modulus, no `pⁿ` factor) — they do *not* call the target. This
  confirms the target's wrapper is needed *only* at the one `D·pⁿ` site; the reusable
  content lives in the sub-lemma, which 3 files use.

Signal (per the call-sites table in `mathlibable-verdicts.md`): **K = 1 internal use
only → "possibly the wrong abstraction; lean toward NO-composable / re-aim at the parent."**
The genuinely-reused result is the sub-lemma (3 files), not this wrapper (1 site).

### Composition check (Phase 6)

Can `norm_pow_sub_one_eq_one_of_unit` be derived in ≤3 chained mathlib calls?

Attempt 1 (from mathlib alone): **fails.** Mathlib lacks the tame absolute-value fact
entirely (Phase 5). There is no mathlib lemma giving `‖ζᶜ − 1‖ = 1`, so no mathlib-only
composition can produce the conclusion. NOT-COMPOSABLE-from-mathlib.

Attempt 2 (from the PROJECT's own sub-lemma — i.e. assuming the sub-lemma is the mathlib
target instead): the wrapper is a short reduction, but NOT a ≤3-call composition. The
proof body genuinely does, in order:
  1. `hcop := (ZMod.isUnit_iff_coprime …).1 hcu`; `hcopD := hcop.coprime_dvd_right …`;
     `hDc := …Nat.eq_one_of_dvd_coprimes…` (derive `¬D∣c` — 3 steps with `omega`),
  2. `hεD := hε.pow_of_dvd … ▸ Nat.mul_div_cancel …` (`ε^{pⁿ}` primitive `D`-th — 2 steps),
  3. `hεc := norm_eq_one_of_pow_eq_one …` (`‖εᶜ‖=1`),
  4. `hpow1 := …hεD.norm_pow_sub_one_eq_one…` after `pow_mul`/`mul_comm` rewriting,
  5. `exact norm_sub_one_eq_one_of_pow hpow1 hεc.le` (the auxiliary ultrametric lift).

That is **5+ steps with real reasoning between them** (number-theory bookkeeping +
two project auxiliaries `norm_eq_one_of_pow_eq_one` and `norm_sub_one_eq_one_of_pow`,
the latter itself a 15-line ultrametric lemma). Per the Phase-6 heuristics table this is
"multiple `have`s with non-trivial reasoning between → NO, this is a proof," not a
composition.

Conclusion: **NOT-COMPOSABLE** (neither from mathlib — which lacks the key fact — nor as
a ≤3-call glue over the project's sub-lemma; it is a genuine short proof). Phase 7
therefore does **not** pick NO-composable-from-mathlib.

---

## Verdict: `norm_pow_sub_one_eq_one_of_unit`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the tame-part unit fact (`‖1−ζ‖=1` for `ord(ζ)` coprime
  to `p`; `Φ_D(1)=1`) is standard textbook/folklore across 5 web channels + arXiv;
  but it is stated for "order coprime to `p`", with **no** `D·pⁿ`/`ZMod`-unit wrapper.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the target adds an
  artificial `pⁿ` factor and a `ZMod`-unit hypothesis on top of its own clean sub-lemma;
  the modern-idiom target (Phase 4c) is a maximally-general DVF restatement of the
  *sub-lemma*, not of the target.
- Mathlib search (Phase 5): **not in mathlib** in any form (the building block
  `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and the wild-case *field-norm* family exist;
  the tame non-archimedean *absolute-value* fact does not).
- Composition check (Phase 6): **NOT-COMPOSABLE** (mathlib lacks the key fact; the wrapper
  is a 5-step proof, not a ≤3-call glue). Call sites: **K = 1**, same-file only; the
  genuinely-reused content is the sub-lemma (3 files).

**Rationale (why BORDERLINE, not a YES or a clean NO):**

The *mathematics* here is unambiguously mathlib-worthy and currently missing: mathlib
has the algebraic product identity (`prod_one_sub_pow_eq_order`) and the wild-case
*field-norm* of `ζˢ − 1`, but it lacks the **tame-part non-archimedean absolute-value
unit fact** `‖ζᶜ − 1‖ = 1` (order coprime to `p`) — a textbook result with real
downstream use (tame cyclotomic units, Stickelberger, Iwasawa theory). So a YES-shaped
outcome is correct *for the underlying content*.

But the verdict cannot be `YES-add-as-is` (Phase 4b is STRICTLY NARROWER and Phase 4c
offers a real modernisation, both of which forbid `YES-add-as-is` per the gate), and it
should not be a blunt `YES-but-generalise-first` *on this declaration*, because **the
declaration the user pointed at is the wrong grain**: it is a project-internal `N = D·pⁿ`
bookkeeping wrapper (K = 1 use, same file, audience-narrow) sitting on top of the
genuinely-reusable `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (3-file use). The mathlib
contribution should be the **sub-lemma**, generalised to "order coprime to `p`" (and
ideally to a general complete non-archimedean field), with the `D·pⁿ`/`ZMod`-unit
wrapper staying project-local. Which of those two grains to upstream — and how far to
push the coefficient-field generalisation — is a judgment call (mathematical taste +
project scoping) that `mathlibable-verdicts.md` explicitly assigns to BORDERLINE
("audience-narrow result", "the genuinely reusable result is the parent, not this").

**Numbered questions (≤5):**

1. The mathlib-worthy object is the **sub-lemma** `IsPrimitiveRoot.norm_pow_sub_one_eq_one`
   (`projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:211`: for `ζ` a primitive
   `D`-th root, `p ∤ D`, `D ∤ c` ⇒ `‖ζᶜ − 1‖ = 1`), **not** this `D·pⁿ` wrapper. Do you
   agree the upstreaming target should be the sub-lemma, with this wrapper kept
   project-local? (yes/no)
2. Should the mathlib statement be generalised from "`NormedAlgebra ℚ_[p] K`" to **any
   complete non-archimedean field of residue characteristic `p`** (the Phase-4c
   modern-idiom form, MODERATE→EXPENSIVE: re-home `Padic.norm_natCast_eq_one_iff` onto a
   `Valued`/`IsDiscreteValuationRing` statement), or is the `ℚ_p`-algebra form the right
   scope for a first PR? (general-DVF / ℚ_p-algebra)
3. Should the mathlib form be phrased on the **element directly** — "`u` a root of unity,
   `orderOf u` coprime to `p`, `u ≠ 1` ⇒ `‖u − 1‖ = 1`" — rather than via
   `IsPrimitiveRoot ζ D` + `D ∤ c`? (element-order form is cleaner and matches the
   literature; the `IsPrimitiveRoot` form matches the existing project proof.) (element / IsPrimitiveRoot)
4. If you DO want this exact `norm_pow_sub_one_eq_one_of_unit` wrapper in mathlib too
   (alongside the sub-lemma, e.g. as a `ZMod`-unit convenience corollary), confirm — its
   K = 1 same-file use otherwise argues for keeping it inline at `ValuesAtOne.lean:1736`. (yes/no)

**Next action:** answer Q1–Q4; then run `/generalise IsPrimitiveRoot.norm_pow_sub_one_eq_one`
(the sub-lemma — tension it against the literature "order coprime to `p`" form and the
modern general-DVF idiom) and `/cleanup` it before opening a `feat(NumberTheory/Cyclotomic):
add tame-part p-adic norm of ζ^c − 1` PR. Keep `norm_pow_sub_one_eq_one_of_unit` itself
project-local unless Q4 is "yes".

---

## Next step

Answer Q1–Q4 above; then `/generalise` the **sub-lemma** `IsPrimitiveRoot.norm_pow_sub_one_eq_one`
(not this wrapper) against the literature's "order-coprime-to-`p`" form and the
general-DVF modern idiom, `/cleanup` it, and open the mathlib PR for the sub-lemma. This
`D·pⁿ` wrapper (`norm_pow_sub_one_eq_one_of_unit`, K = 1 same-file use) stays project-local
unless you explicitly want it as a `ZMod`-unit convenience corollary (Q4).
