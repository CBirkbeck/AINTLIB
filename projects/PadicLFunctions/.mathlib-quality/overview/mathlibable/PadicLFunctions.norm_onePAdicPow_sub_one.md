# /mathlibable report — `PadicLFunctions.norm_onePAdicPow_sub_one`

**Final verdict: `YES-but-generalise-first`** — the result is a genuinely
missing, canonical fact of p-adic analysis (the p-adic logarithm/exponential
is a norm *isometry* on `pℤ_p ↔ 1+pℤ_p`), mathlib has nothing in this area at
all, but the project's chosen packaging (the equality `‖y^t − 1‖ = ‖t‖·‖y−1‖`
phrased through a *project-local* power `PadicInt.onePAdicPow`, with an `ℤ_[p]`
exponent and an odd-`p` hypothesis baked in) should be restated against the
mathlib-canonical primitives — a genuine `padicLog`/`padicExp` plus the two
isometry lemmas `‖log y‖ = ‖y−1‖` and `‖exp w − 1‖ = ‖w‖` — before any PR.
The combined equality then drops out and belongs *with* those primitives, not
as a standalone bespoke statement about a custom `AddChar`.

---

### Baseline (Phase 0)
- lake build:               **not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.norm_onePAdicPow_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:103`
- kind:                      `theorem`
- has sorry:                 no (the file `ResidueZeta.lean` contains 0 `sorry`/`admit`; this proof and every dependency are complete)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — continuity of the non-exceptional branches, a simple pole with residue `1 − p⁻¹` at `s = 1`, and the supporting p-adic exp/log isometry bridge.

(Note: Phase 4.5 — diamond/defeq risk — is `n/a`; the declaration is a `theorem`, not a `def`/`class`/`instance`, so it introduces no definitional equalities or typeclass-search paths.)

---

### Statement (Phase 1)

`PadicLFunctions.norm_onePAdicPow_sub_one` is **a theorem** stating the
following.

Let `p` be an odd prime (`p ≠ 2`) and let `y ∈ ℤ_p` be a **principal unit**,
i.e. `y ≡ 1 (mod p)` (witnessed by `y − 1 ∈ pℤ_p`). For every p-adic integer
exponent `t ∈ ℤ_p`, the continuous power `y^t` (defined as the unique continuous
additive character of `ℤ_p` sending `1 ↦ y`) satisfies the **exact norm
identity**

  ‖ y^t − 1 ‖ = ‖t‖ · ‖y − 1‖.

In valuation terms: `v_p(y^t − 1) = v_p(t) + v_p(y − 1)`. This is the precise,
quantitative form of the statement that "the p-adic logarithm is an isometry on
principal units and is a homomorphism in the exponent" — `log(y^t) = t·log y`
plus `‖log y‖ = ‖y − 1‖` plus `‖exp w − 1‖ = ‖w‖`, assembled through the
exp/log bridge `y^t = exp(t·log y)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the residue characteristic.
- `y : ℤ_[p]` (implicit) — the base, a principal unit.
- `t : ℤ_[p]` — the p-adic exponent.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — oddness; ensures `pℤ_p` lies *strictly inside* the
  exponential convergence ball (`‖x‖^{p−1} ≤ p^{−(p−1)} < p⁻¹` needs `p − 1 ≥ 2`).
  Without it the isometry can fail (the `p = 2` analogue is only the one-sided
  bound `‖y^t − 1‖ ≤ ‖t‖`, captured separately by `norm_onePAdicPow_sub_one_le`).
- `hy : y − 1 ∈ Ideal.span {(p : ℤ_[p])}` — principal-unit membership `y ∈ 1+pℤ_p`.

Conclusion (math): `‖y^t − 1‖ = ‖t‖·‖y − 1‖` (equivalently `v(y^t−1) = v(t)+v(y−1)`).

Conclusion (Lean): `‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ = ‖t‖ * ‖y - 1‖`.

Proof shape (3 chained heavy facts, all project-custom):
```lean
rw [← padicExp_smul_padicLog_eq_onePAdicPow …,            -- bridge y^t = exp(t·log y)
    …, norm_padicExp_sub_one …,                            -- ‖exp w − 1‖ = ‖w‖
    …, norm_mul, …]                                        -- ‖t·log y‖ = ‖t‖·‖log y‖
congr 1
rw […, norm_padicLog …, …]                                 -- ‖log y‖ = ‖y − 1‖
```

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the named, quantitative form of a standard p-adic-analysis fact
(the log/exp isometry on principal units), and its proof is the payoff of a
~1000-line custom development (`PadicExp.lean`) of the p-adic exponential and
logarithm that **mathlib does not have at all**. It is not a one-step helper:
it sits at the top of a real isometry stack. (It is *not* a `## Main results`
headline of `ResidueZeta.lean` — that headline is the residue/pole of
`zetaPBranch` — but the underlying isometry it packages is a textbook theorem.)

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
framing only.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (a `set`, three `have`s, two `rw`
blocks, a `congr 1`). Kind is `theorem`.
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`.
The one-line-definition exemption machinery does not apply.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic logarithm isometry `1+pℤ_p` norm equality `‖log‖=‖x−1‖` Iwasawa | yes  | `log` is an isometry `1+pℤ_p → pℤ_p`; `v(log(1+x)) = v(x)` for `p` odd | Speyer MIT `~dav/exp.pdf`; Conrad/Thorne `math5020`; Dion (Laval) report; MIT 18.785 PS10 |
|  2 | WebSearch (general form)         | p-adic exp/log isometry principal units norm-preserving Washington cyclotomic fields | yes  | "exp/log are mutually inverse isometries between additive `m` and multiplicative `1+m`, for `e < p−1`" | Lombaers thesis; arXiv:1904.09850 (image of log on principal units); the *general* form is over any local field `K` with `e_K < p−1`, not just `ℚ_p` |
|  3 | WebSearch (named-after / aliases)| p-adic power `y^s` continuous exponentiation by p-adic integer, norm, `1+pℤ_p`, principal units | yes  | `U₁ = 1+pℤ_p` principal units; exp/log iso on the disk `|x|<1` for odd `p`; `log(xⁿ)=n log x` | Cambridge `jat58/all.pdf`; K. Conrad notes; "principal units" is the standard name; power = `exp(s·log)` |
|  4 | ChatGPT MCP                      | "standard form + generality + historical evolution of the p-adic log/exp isometry on principal units" | **n/a** | — | `chatgpt-math` MCP is *configured* (`~/.claude/mcp-servers/chatgpt-math/server.js`) but **not loaded as a callable tool in this session** and requires auth (`mcp-needs-auth-cache.json`). Recorded as attempted-unavailable; the gap is covered by 6 corroborating WebSearch/source channels below. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | **n/a** | (no references dir) | both `…/.mathlib-quality/references/` and the shared `refs/` symlink are **absent** in this checkout — recorded as n/a. The in-source RJW citations (Lem 5.14, TeX 1892–1894) serve as the project's own pointer. |
|  6 | nLab                             | p-adic exponential / logarithm convergence radius isometry | partial | radius `p^{−1/(p−1)}`; exp/log inverse iso `pℤ_p ↔ 1+pℤ_p` | nLab has no dedicated isometry page; PlanetMath "p-adic exponential and p-adic logarithm" + umontreal Appendix 16.6 confirm the convergence/iso picture |
|  7 | nCatLab (if categorical)         | (categorical angle) | **n/a** | — | not a categorical concept — it is a metric/valuation identity on a specific topological group; no higher-categorical content to look up |
|  8 | Stacks Project (if alg geom)     | (algebraic-geometry angle) | **n/a** | — | not an algebraic-geometry concept; the Stacks Project has no p-adic-analysis exp/log isometry material |
|  9 | MathOverflow / Math.StackExchange| p-adic log isometry proof `v(log(1+x)) = v(x)`; exp isometry ball | yes  | `log : V_ρ → V_ρ` surjective isometry; exp/log inverse iso on `pℤ_p ↔ 1+pℤ_p`; bijection when `e_K < p−1` | Stoll Bayreuth `pAdicAnalysis-WS2015` notes; standard MO/MSE answers reproduce `v(logx)=v(x)` on the small ball |
| 10 | recent arXiv (last 5 years)      | p-adic exp/log isometry **formalization** (Lean / mathlib / Coq), 2023–2025 | yes (formalization status) | mathematics is classical; **no Lean-4/mathlib formalization of p-adic exp/log exists** | arXiv:2302.14491 (Narayanan, "Formalization of p-adic L-functions") is **Lean 3**; arXiv:2306.17234 (norm extensions) and the 2025 AFM local-fields work do **not** add p-adic exp/log. Confirms the mathlib gap. |

**Protocol pass check.** WebSearch ran 3 distinct queries at three generality
levels (rows 1–3: specific equality, most-general local-field form, named-alias
"principal units / continuous power"). ChatGPT MCP row recorded `n/a` with a
concrete reason (not loaded / auth-gated) and the loss is compensated by six
independent corroborating channels. Local refs checked (absent → n/a). nLab
checked. Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with a
one-line reason. No channel is silently skipped.

### Literature summary (Phase 3)

Concept identified as: **the p-adic logarithm/exponential isometry on principal
units** — `log : 1+pℤ_p → pℤ_p` and `exp : pℤ_p → 1+pℤ_p` are mutually inverse
**isometries** (for `p` odd, more generally for a local field with absolute
ramification `e < p − 1`); equivalently `v_p(log y) = v_p(y − 1)` and
`v_p(exp w − 1) = v_p(w)`. The target's exact identity
`‖y^t − 1‖ = ‖t‖·‖y − 1‖` is the composite of this isometry with the exponent-
homomorphism `log(y^t) = t·log y` and `v(t·log y) = v(t) + v(log y)`.

Sources agree on the standard form: **yes** — Speyer (MIT), K. Conrad / J.
Thorne, Stoll (Bayreuth), Gouvêa/Koblitz-style course notes, Washington's
*Cyclotomic Fields* and the Iwasawa-theory literature all state it identically;
the only variation is the *ambient field* and the exact *hypothesis* (`p` odd
for `ℚ_p`; `e < p−1` for a general local field).

Most general standard form: over a complete discretely-valued non-archimedean
field `K` of residue characteristic `p` with absolute ramification index
`e < p − 1`, `exp`/`log` are mutually inverse isometries between the maximal
ideal `m_K` (additive) and `1 + m_K` (multiplicative); the power `y^t` for
`t ∈ ℤ_p` (or `t ∈ 𝒪_K`) is `exp(t·log y)`, and `v(y^t − 1) = v(t) + v(y − 1)`.

Generality dimensions where the literature varies:
  - **ambient ring**: from `ℤ_[p]` (the user's form) → `𝒪_K` of any local field
    with `e < p − 1` → general non-archimedean setting. The user's form is the
    base case `K = ℚ_p`.
  - **hypothesis encoding**: `p ≠ 2` (user) vs. the sharp `e < p − 1`. For
    `K = ℚ_p`, `e = 1`, so `e < p − 1 ⇔ p > 2 ⇔ p ≠ 2` — the user's `p ≠ 2`
    *is exactly* the specialisation of the sharp condition. (Good: not over- or
    under-constrained for `ℚ_p`.)
  - **exponent type**: `t ∈ ℤ_p` (user) is the natural maximal generality for
    `y ∈ 1+pℤ_p ⊆ ℤ_p^×` (the power is continuous in `t` over all of `ℤ_p`).

Disagreement with the literature: **none.** The user's identity is exactly the
standard one, specialised to `ℚ_p` and packaged through a project-local power
object. The mathematics is correct and canonical; the only question is the
*form/primitives* it is stated over (Phase 4).

If anything, the literature is *unanimous and rich* here — the opposite of the
"empty Phase 3 ⇒ BORDERLINE/NO" failure mode. This is a textbook result.

---

### Generality analysis — `PadicLFunctions.norm_onePAdicPow_sub_one`

Literature-standard form (from Phase 3): for a local field with `e < p − 1`,
`exp`/`log` are inverse isometries `m_K ↔ 1+m_K`, and `v(y^t − 1) = v(t) + v(y−1)`.

| # | Parameter / hypothesis                | Current Lean form               | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|---------------------------------|----------------------------------|---------------------|------------------------------------|
| 1 | base ring `ℤ_[p]`                     | the p-adic integers `ℤ_p`       | `𝒪_K`, any local field `e<p−1`   | yes (in principle)  | the *isometry* generalises to `e<p−1`; but the project's whole exp/log stack (`PadicExp.lean`) is built for the `ℚ_p`-instance with `IsUltrametricDist` — generalising the ambient field is a real (EXPENSIVE) re-development, not a free rewrite |
| 2 | `hp2 : p ≠ 2`                          | odd prime                       | `e_K < p − 1` (here `e=1`)        | NO                  | for `K=ℚ_p` this is already the sharp hypothesis (`p≠2 ⇔ 1<p−1`); cannot be dropped — the `p=2` isometry genuinely fails (only `‖y^t−1‖ ≤ ‖t‖` survives, cf. `norm_onePAdicPow_sub_one_le`) |
| 3 | exponent `t : ℤ_[p]`                  | p-adic integer                  | `t ∈ ℤ_p` (or `𝒪_K`)             | NO (already maximal)| `ℤ_p` is the natural maximal exponent domain for a continuous power of a `1+pℤ_p` element; nothing weaker makes sense |
| 4 | the power object `PadicInt.onePAdicPow`| project-local `AddChar` wrapper over mathlib `addChar_of_value_at_one` | `exp(t·log y)` over a genuine `padicLog`/`padicExp` | **yes — this is the real generality/idiom issue** | the *statement* is phrased about a project-private definition; the mathlib-canonical statement is about `padicLog`/`padicExp` (which mathlib lacks) — see Phase 4c |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along axis 1 — the
ambient ring — and, more importantly, along the *primitive* axis 4: it is stated
about a bespoke power object rather than the canonical `padicLog`/`padicExp`).

Number of weakening opportunities found: K = 1 *substantive* (the ambient-field
generalisation, axis 1) + 1 *reformulation* (axis 4, the primitives — handled
in 4c). Axes 2 and 3 are already maximal/sharp for `ℚ_p`.

Proposed restatement (literature-weakening axis 1, the EXPENSIVE option):
state the isometry over `𝒪_K` for a local field with `e < p − 1`. This is the
fully general textbook form but requires re-developing `PadicExp.lean` over a
general local field.

Cost of restatement: **EXPENSIVE** for axis 1 (new local-field exp/log
development). **CHEAP–MODERATE** for axis 4 (re-state over `padicLog`/`padicExp`
once those land in mathlib — the equality is then a 3-line corollary; the proof
*already exists*, it just currently routes through `onePAdicPow`).

EXPENSIVE does not downgrade the verdict (Bourbaki-2.0 rule). It informs
sequencing: ship the `ℚ_p` form first, generalise the field later.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses? | no | the hypotheses are already typeclass-driven (`Fact p.Prime`, `IsUltrametricDist`) | — |
|  2 | sequences/metric → filters/topological? | no | it is already a clean norm equality; nothing sequence-based to filter-ise | — |
|  3 | **construct an object where a primitive should be characterised?** | **YES** | the statement is about a *constructed* `AddChar` (`onePAdicPow`); the canonical mathlib idiom is to define `padicLog`/`padicExp` (genuine functions with an `AddChar`/`MonoidHom` API) and prove the isometry of *those*, then derive the power identity | the two component isometries `‖padicLog y‖ = ‖y−1‖`, `‖padicExp w − 1‖ = ‖w‖` would each be standalone reusable mathlib lemmas; the power identity is a corollary. This is exactly how the project *internally* already proves it (`norm_padicLog`, `norm_padicExp_sub_one`) — those internal lemmas are the real contributions |
|  4 | set-with-predicate → bundled substructure? | no | `1+pℤ_p` is already `Ideal.span`-based membership; fine | — |
|  5 | field/metric-specific → weaken typeclass? | **partially** (= axis 1 above) | weaken `ℚ_p`/`ℤ_p` to a local field `e < p−1` | full local-field exp/log API | 
|  6 | 1-categorical → higher-categorical? | no | no categorical content | — |
|  7 | concrete index → general structure? | no | `t ∈ ℤ_p` is already the right structure | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (rows 3 and 5).
  - Proposed mathlib-idiomatic restatement: **do not** ship
    `norm_onePAdicPow_sub_one` (about a private `AddChar`) as the headline.
    Ship instead the two genuine isometry lemmas about real p-adic transcendentals:
    ```lean
    -- in a new Mathlib/NumberTheory/Padics/ExpLog.lean (the primitives mathlib lacks)
    theorem PadicInt.norm_log_eq (hp2 : p ≠ 2) {y : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
        ‖padicLog y‖ = ‖y - 1‖
    theorem PadicInt.norm_exp_sub_one_eq (hp2 : p ≠ 2) {w : ℤ_[p]} (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
        ‖padicExp w - 1‖ = ‖w‖
    ```
    and then, *as a corollary*, the power identity stated against the canonical
    power `exp(t · log y)`:
    ```lean
    theorem PadicInt.norm_pow_sub_one (hp2 : p ≠ 2) {y : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
        (t : ℤ_[p]) : ‖padicExp (t * padicLog y) - 1‖ = ‖t‖ * ‖y - 1‖
    ```
  - Cost: **MODERATE** — gated on first contributing `padicExp`/`padicLog`
    themselves (the larger PR). Once present, this is a re-statement of an
    already-complete proof.
  - Mathlib downstream this enables: a genuine p-adic `exp`/`log` (currently
    entirely absent — confirmed by grep over `Mathlib/NumberTheory/Padics/`),
    plus the convergence/homomorphism/isometry API; these are prerequisites for
    Iwasawa theory, the p-adic regulator, Coleman maps, Coates–Wiles, and the
    very p-adic-L-function programme this project is formalising.
  - Real mathematical improvement (not "looks cooler"): the *primitive* `padicLog`
    is what the literature, and downstream mathlib users, will reach for — not a
    one-off `AddChar`. The isometry of `padicLog` is the reusable theorem; the
    `onePAdicPow` packaging is a project-internal convenience tied to RJW §7.

Because Phase 4c finds a real modern-idiom improvement AND Phase 4b found a
strict literature-weakening (axis 1), Phase 7 takes **YES-but-generalise-first**
(reasons: both MODERN-IDIOM and LITERATURE-WEAKENING).

---

### Diamond / defeq risk — `PadicLFunctions.norm_onePAdicPow_sub_one`

**n/a — declaration kind is `theorem`.** Phase 4.5 is skipped for
theorems/lemmas (no definitional equalities, no typeclass-search paths
introduced).

---

### Mathlib search-status: `PadicLFunctions.norm_onePAdicPow_sub_one`

[A] Lean-Finder       — `n/a` — Lean-Finder MCP not available in this session
[B] Loogle            `‖_ ^ _ - 1‖ = ‖_‖ * ‖_‖`; `‖padicLog _‖ = _`; `‖padicExp _ - 1‖ = _` — `n/a` — `lean_loogle` MCP not loaded (no matching deferred tool); substituted by exhaustive source grep below
[C] LeanSearch        "p-adic logarithm is an isometry on principal units"; "norm of p-adic power minus one" — `n/a` — `lean_leansearch` MCP not loaded; substituted by source grep
[D] Grep mathlib src  `padicExp` / `padicLog` / `isometry` / `norm_pow_sub_one` / `principal unit` / `addChar.*norm` over `.lake/packages/mathlib/Mathlib/` — **NO HITS for any p-adic exp/log/power isometry.** mathlib has *no* p-adic exponential and *no* p-adic logarithm at all (`Mathlib/NumberTheory/Padics/` contains AddChar, Complex, Hensel, MahlerBasis, PadicIntegers, PadicNumbers, PadicNorm, PadicVal, … but **no `Exp.lean`/`Log.lean`**). The only `norm_pow_sub_one_*` lemmas are about `IsPrimitiveRoot` (cyclotomic `‖ζ^k − 1‖`, `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`) — a different object. `addChar_of_value_at_one` exists (`Padics/AddChar.lean`) but carries **no norm/isometry lemma**.
[E] Name pattern (grep) `norm_onePAdicPow`, `norm_log`, `norm_exp`, `norm_padic*`, `isometry` over mathlib — no hit for the principal-unit power isometry

Searched for both:
  - the user's current form (`‖onePAdicPow y t − 1‖ = ‖t‖·‖y−1‖`) — absent.
  - the literature-standard form (`padicLog`/`padicExp` isometry; `v(y^t−1)=v(t)+v(y−1)`) — **also absent** (the primitives themselves don't exist in mathlib).

Concluded: **not in mathlib** (all available methods exhausted: A/B/C are MCP
tools genuinely not loaded this session and are recorded `n/a`; D/E — the
authoritative grep over the vendored mathlib source tree — are exhausted and
return nothing). Both the user's form and the more-general literature form are
missing because mathlib has no p-adic exp/log development whatsoever.

(Cross-check via the formalization literature, Phase 3 row 10: the only p-adic
exp/log formalization on record is Narayanan's **Lean 3** p-adic-L-functions
work; nothing in current Lean-4 mathlib. Consistent with the grep.)

---

### Call sites — `PadicLFunctions.norm_onePAdicPow_sub_one`

Internal use count: **0** (within the project, NOT counting the declaring file
and NOT counting comment/docstring mentions).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none — every match is a docstring/comment reference, not a call) | `ResidueZeta.lean:311,340` mention it *by name in comments* contrasting it with the `p=2`-valid weaker bound; no proof invokes it |

Inline-derivation grep (is the equivalent re-derived / used elsewhere?):
  - The downstream consumers (`continuous_zetaNum_branch_pairing`,
    `branch_denom_ne_zero`) **do not use the sharp equality**. They use the
    *one-sided* bound `norm_onePAdicPow_sub_one_le` (`‖y^t − 1‖ ≤ ‖t‖`, holds
    for **all** `p`, including `p = 2`) — see `ResidueZeta.lean:382`. The sharp
    equality `norm_onePAdicPow_sub_one` is, in the current codebase, an
    **isolated result with no consumer**: the §7 development was routed through
    the weaker, more general bound instead.

What the call-sites pattern tells you (per the Phase-6 signal table):
`K = 0` internal uses, **and** the closely-related weaker lemma is what's
actually consumed → on its own this leans toward NO/BORDERLINE for *the bespoke
form*. But this is precisely the case the Bourbaki-2.0 rule covers: the value is
not "is this wrapper used here" but "is the underlying isometry a thing mathlib
should have, in the right form". The right form (Phase 4c) is the `padicLog`/
`padicExp` isometry — which the project *does* use internally (`norm_padicLog`,
`norm_padicExp_sub_one` feed `pZpExp_coe`, `pZpLog_mem`, the bridge, and the
pole computation `tendsto_branch_denom_div`). So the `K = 0` here strengthens
the 4c conclusion: **don't ship this exact statement**; ship the reusable
primitives it is built from.

---

### Composition check (Phase 6)

Can `norm_onePAdicPow_sub_one` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: assemble from a mathlib p-adic-log isometry + a mathlib
exponent-homomorphism.
  - Mathlib decls used: *none exist* — there is no `padicLog`, no `padicExp`,
    no isometry lemma, no `log(y^t) = t log y` in mathlib.
  - Result: **fails** at step 0.

Attempt 2: derive directly from `Padics/AddChar.lean` (`addChar_of_value_at_one`)
norm properties.
  - Mathlib decls used: `addChar_of_value_at_one`, `AddChar.tendsto_eval_one_sub_pow`.
  - Result: **fails** — `AddChar.lean` provides the *construction* and continuity
    of the character and the bijection `κ ↦ κ1 − 1`, but **no norm formula** for
    `‖κ(t) − 1‖`. Getting `‖κ(t) − 1‖ = ‖t‖·‖y−1‖` from these requires the entire
    exp/log isometry argument (the project's ~1000-line `PadicExp.lean`: Legendre
    factorial bounds, summability, `padicExp_add`, the strict-tail isometry,
    `norm_padicExp_sub_one`, `norm_padicLog`, the bridge). That is a *proof*, not
    a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE.** The result is the apex of a deep custom
development with no mathlib building blocks to lean on (the prerequisite
primitives are themselves missing from mathlib). Phase 7 therefore considers the
YES verdicts, not NO-composable.

---

## Verdict: `PadicLFunctions.norm_onePAdicPow_sub_one`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the p-adic log/exp isometry on principal units is
  a canonical, unanimously-stated textbook fact (Speyer, K. Conrad, Stoll,
  Washington, Iwasawa-theory literature); the user's identity
  `‖y^t − 1‖ = ‖t‖·‖y−1‖` is its exact specialisation to `ℚ_p`. ≥6 corroborating
  channels (rows 1,2,3,6,9,10); ChatGPT MCP n/a with reason.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — narrower than the
  general local-field (`e < p−1`) form (axis 1, EXPENSIVE) and, decisively,
  stated over a *project-private power object* rather than the canonical
  `padicLog`/`padicExp` primitives (Phase 4c MODERN-IDIOM, MODERATE).
- Mathlib search (Phase 5): **not in mathlib** — and neither is the more general
  form, because mathlib has **no p-adic exp/log at all** (authoritative source
  grep; corroborated by the formalization literature showing only a Lean-3
  precedent).
- Composition check (Phase 6): **NOT-COMPOSABLE** — no mathlib building blocks;
  the prerequisite primitives are themselves absent.

**Rationale.**
This is a genuinely missing, genuinely canonical piece of p-adic analysis: that
the p-adic logarithm and exponential are mutually-inverse *isometries* between
`pℤ_p` and `1+pℤ_p` (for odd `p`), of which `‖y^t − 1‖ = ‖t‖·‖y−1‖` is the
quantitative power form. Mathlib has nothing here — no `padicExp`, no `padicLog`,
no isometry lemma — confirmed by exhaustive grep over `Mathlib/NumberTheory/
Padics/` and corroborated by the formalization literature (the only precedent is
Narayanan's *Lean 3* work; current Lean-4 mathlib lacks it entirely). So the
content unquestionably *belongs* in mathlib. The reason the verdict is
*generalise-first* rather than add-as-is is twofold and concrete. (1) MODERN-IDIOM
(Phase 4c, row 3): the theorem as written is about `PadicInt.onePAdicPow` — a
project-local thin wrapper over mathlib's `addChar_of_value_at_one`. The
mathlib-canonical contribution is not a bespoke `AddChar` statement but the
isometry of *genuine* `padicLog`/`padicExp` functions (`‖padicLog y‖ = ‖y−1‖`,
`‖padicExp w − 1‖ = ‖w‖`) — which the project has *already proved internally*
(`norm_padicLog`, `norm_padicExp_sub_one`) and which are the real, reusable
theorems; the power identity is then a corollary stated over `exp(t·log y)`.
(2) LITERATURE-WEAKENING (Phase 4b, axis 1): the sharp textbook form is over a
local field with `e < p−1`, of which `ℚ_p`/`p≠2` is the base case. Note the
`p ≠ 2` hypothesis is *correct and sharp* for `ℚ_p` (it is exactly `e < p−1`
with `e=1`) and must stay — the `p=2` isometry genuinely fails, leaving only the
one-sided `norm_onePAdicPow_sub_one_le`. Finally, the call-site evidence
(`K = 0`; downstream code uses the weaker all-`p` bound, not this sharp equality)
reinforces 4c: the bespoke statement has no consumer even locally, whereas the
primitives it is built from are used throughout the file — so the upstreaming
target is those primitives, not this wrapper.

**Reason for the generalisation:**
  - **MODERN-IDIOM (Bourbaki 2.0):** restate over genuine `padicLog`/`padicExp`
    (which mathlib should gain) and their isometry lemmas, rather than over the
    project-private `onePAdicPow` `AddChar`.
  - **LITERATURE-WEAKENING:** the maximally-general statement is over a local
    field with `e < p − 1`; ship `ℚ_p` first, then generalise the field.

Proposed restatement (the mathlib-idiomatic, primitive-first target):
```lean
-- Mathlib/NumberTheory/Padics/ExpLog.lean  (the primitives mathlib currently lacks)

/-- The p-adic logarithm is a norm isometry on principal units (`p` odd). -/
theorem PadicInt.norm_log_eq (hp : p ≠ 2) {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖padicLog y‖ = ‖y - 1‖ := by
  sorry  -- = the project's `norm_padicLog` ∘ `pZpLog_coe`, already proved

/-- `‖exp w − 1‖ = ‖w‖` on `pℤ_p` (`p` odd). -/
theorem PadicInt.norm_exp_sub_one_eq (hp : p ≠ 2) {w : ℤ_[p]}
    (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖padicExp w - 1‖ = ‖w‖ := by
  sorry  -- = the project's `norm_padicExp_sub_one` ∘ `pZpExp_coe`, already proved

/-- The continuous p-adic power `y ↦ y^t = exp(t·log y)` is a norm isometry in
the exponent on principal units (`p` odd): `‖y^t − 1‖ = ‖t‖·‖y − 1‖`. -/
theorem PadicInt.norm_pow_sub_one (hp : p ≠ 2) {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖padicExp (t * padicLog y) - 1‖ = ‖t‖ * ‖y - 1‖ := by
  sorry  -- corollary: norm_exp_sub_one_eq + norm_mul + norm_log_eq
```

Estimated cost of regeneralisation: **MODERATE** — gated on first contributing
`padicExp`/`padicLog` to mathlib (the larger prerequisite PR; the project's
`PadicExp.lean` is the ready-made source). Once the primitives land, the three
lemmas above are essentially re-exports of already-complete proofs. The
EXPENSIVE local-field (`e < p−1`) generalisation is a *separate, later* PR and
does **not** gate this one (and does not downgrade the verdict — Bourbaki 2.0).

Mathlib downstream this enables (REQUIRED, MODERN-IDIOM):
  - A genuine p-adic `exp`/`log` API — **completely absent** from current mathlib
    (the named gap: no `Mathlib/NumberTheory/Padics/Exp.lean` or `Log.lean`;
    `Padics/AddChar.lean` even lists "homeomorphism" as a TODO and has no norm
    lemma). This is the canonical prerequisite for: Iwasawa theory, the p-adic
    regulator, Coleman power series / Coleman maps, Coates–Wiles, p-adic
    heights, and the p-adic-L-function formalisation this very project pursues.
  - The two isometry lemmas compose with all of mathlib's `IsUltrametricDist`
    and `PadicInt` norm/valuation API (`norm_le_pow_iff_mem_span_pow`,
    `norm_eq_zpow_neg_valuation`, the ultrametric isosceles lemmas) — enabling
    valuation computations `v(y^t−1)=v(t)+v(y−1)` that are currently impossible
    to state in mathlib for lack of the power object.
  - Proofs currently *blocked* by the absence of `padicLog`: any downstream
    result needing "log is a homeomorphism `1+pℤ_p ≅ pℤ_p`" (the AddChar.lean
    TODO), e.g. the structure theory of `ℤ_p^×`.

Next action: run `/generalise PadicLFunctions.norm_onePAdicPow_sub_one`
(it will tension against both the literature-standard `e < p−1` local-field form
from Phase 3 and the primitive-first `padicLog`/`padicExp` modern-idiom form from
Phase 4c). In practice the *first* concrete PR is the larger one — upstream
`padicExp`/`padicLog` from `PadicExp.lean` with `norm_padicExp_sub_one` /
`norm_padicLog` as headline isometry lemmas — and this power identity rides along
as the corollary `PadicInt.norm_pow_sub_one`. Do **not** PR the
`onePAdicPow`-phrased statement standalone.

---

## Next step

Run `/generalise PadicLFunctions.norm_onePAdicPow_sub_one` to produce the
mathlib-idiomatic restatement over genuine `padicLog`/`padicExp` (and tension
against the general local-field `e < p−1` form). The upstreaming path is: first
contribute `padicExp`/`padicLog` (from the project's `PadicExp.lean`) with the
two isometry lemmas `‖padicLog y‖ = ‖y−1‖` and `‖padicExp w − 1‖ = ‖w‖` as the
headline, then add the power identity `‖y^t − 1‖ = ‖t‖·‖y−1‖` as a corollary
stated against `exp(t·log y)` — not against the project-private `onePAdicPow`.
