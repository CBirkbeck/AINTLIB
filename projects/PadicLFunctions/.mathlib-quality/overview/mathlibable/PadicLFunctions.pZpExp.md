# `/mathlibable` report — `PadicLFunctions.pZpExp`

**Final verdict: `BORDERLINE-needs-human`.** The *mathematics* `pZpExp` encodes —
the p-adic exponential restricted to `pℤ_p` (odd `p`), landing in `1 + pℤ_p` — is
a classical, named, mathlib-worthy result (Washington §5.1, Cassels §12: `exp`
gives the isomorphism `pℤ_p ≅ 1 + pℤ_p`). But the **Lean form under assessment is
not that object**: `pZpExp` is a `dite`-guarded *junk-total* function
`ℤ_[p] → ℤ_[p]` (true branch = the analytic `padicExp` packaged as integral when
`‖exp x‖ ≤ 1`; junk branch = `1`). Mathlib has *no* p-adic exponential at all,
*no* integral-valued exp, and *no* `pℤ_p → 1+pℤ_p` map — so this is not
`NO-mathlib-has-it`. It is also not a ≤3-call composition (Phase 6). Whether the
*right* mathlib object is (a) this junk-total wrapper, (b) a bundled group
homomorphism `pℤ_p → (1+pℤ_p)ˣ`, or (c) a continuous map `C(ℤ_[p], ℤ_[p])` — and
whether the project even wants `pZpExp` upstreamed at all, given the project
itself proves it agrees with the already-bridged `PadicInt.onePAdicPow` — are
design/taste calls the skill cannot make alone. Hence BORDERLINE, with the
questions spelled out in Phase 7.

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task BUILD NOTE); reasoned from source — the file elaborates as part of `main`, dependencies read directly.
- decl `PadicLFunctions.pZpExp`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1040`
- kind:                      `def` (noncomputable)
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑ xⁿ/n!` on the ball `‖x‖ < p^{−1/(p−1)}` of a complete nonarchimedean normed `ℚ_[p]`-algebra field, an isometry there; for odd `p` the ball contains `pℤ_p`; `log` inverts `exp`; realises `x^s := exp(s·log x)` and matches `PadicInt.onePAdicPow`.

---

### Statement (Phase 1)

`PadicLFunctions.pZpExp` is a **definition** of an everywhere-defined
("junk-total") integral exponential

  pZpExp : ℤ_[p] → ℤ_[p],  pZpExp(x) = ⟨exp(x̄), …⟩  if  ‖exp(x̄)‖ ≤ 1,  else  1,

where `x̄ ∈ ℚ_[p]` is the coercion of `x ∈ ℤ_[p]` and `exp = padicExp` is the
analytic p-adic exponential `∑ x̄ⁿ/n!`. On its intended domain — `x ∈ pℤ_p` with
`p` odd (RJW Lem 5.14, first half) — the analytic value `exp(x̄)` is integral
(`‖exp(x̄)‖ ≤ 1`, in fact `exp(x̄) ∈ 1 + pℤ_p`), so the `dite` takes its **true
branch** and `(pZpExp x : ℚ_[p]) = exp(x̄)` (lemma `pZpExp_coe`). Off that domain
(where the analytic exp need not be integral, or even converge) it returns the
junk value `1`.

Mathematically, the meaningful content is the classical exponential isomorphism

  exp : pℤ_p  →  1 + pℤ_p   (p odd),

inverse to the p-adic logarithm, used to realise `x ↦ x^s := exp(s·log x)`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- The ambient `{L : …}` typeclasses (`NormedField`, `NormedAlgebra ℚ_[p]`,
  `IsUltrametricDist`, `CompleteSpace`) are **omitted** for this def (it is stated
  at `L = ℚ_[p]`, via the coercion `ℤ_[p] ↪ ℚ_[p]` — the `omit` lines around the
  surrounding lemmas confirm this).

Hypotheses (Lean side): **none** — the def is total. (Domain hypotheses
`x ∈ Ideal.span {(p : ℤ_[p])}` and `p ≠ 2` appear on the *lemmas* `pZpExp_coe`,
`pZpExp_sub_one_mem`, not on the def.)

Conclusion (math): `pZpExp x ∈ ℤ_[p]`; on `pℤ_p` it equals `exp(x)` and lies in
`1 + pℤ_p`.

Conclusion (Lean): `ℤ_[p]`. Body:
`if h : ‖padicExp p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicExp p ((x : ℚ_[p])), h⟩ else 1`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the Lean realisation of a named classical object (the p-adic
exponential on `pℤ_p`, the exp/log isomorphism `pℤ_p ≅ 1+pℤ_p`), and is a
primary construction of the file (module docstring `## …`, RJW Lem 5.14). A named
special-function restriction with its own literature is BIG.

(Literature width is EXHAUSTIVE regardless — run in full below.)

### One-line check (Phase 2b)

Body line count: **2 substantive lines** (the `dite` with its true/false
branches). Kind is `def`.
One-liner verdict: **MULTI-LINE** — the body is a genuine case split
(`dite` on an integrality predicate, packaging a subtype in the true branch,
junk value in the false branch), not a one-line alias. The Phase-2b
defeq/diamond/API exemption table is therefore **not** triggered as a NO-bias;
the def carries real (if small) logic. (Contrast the sibling `InExpBall`, a true
one-line `Prop` abbreviation, verdict NO-composable.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential maps p Z_p into 1 + p Z_p integral exponential principal units" | yes | `exp : pℤ_p → 1+pℤ_p`; "the usual exponential is convergent only on `pℤ_p`"; `exp(x) ≡ 1+x` mod higher powers | Hsieh L3 notes (NTU); Wikipedia *P-adic exponential function*; "On the image of p-adic logarithm on principal units" (arXiv 1904.09850). The standard object is the **homomorphism** `exp: pℤ_p → 1+pℤ_p`. |
| 2 | WebSearch (general form / isomorphism) | "exponential isomorphism p Z_p to 1 + p Z_p odd prime Washington cyclotomic fields log" | yes | "1 + pℤ_p is isomorphic to ℤ_p (for `p ≠ 2`) using exp and log"; `log(1+pG⁺)⊆pG⁺`, `exp∘log=id` on `1+pG⁺`, `log∘exp=id` on `pG⁺` | Gupta REU (UChicago); MIT `exp.pdf` (D. Vogan); PlanetMath *p-adic exponential and logarithm*; Mustață appendix. Exactly the file's RJW-5.14 citation cluster (Washington §5.1, Cassels §12). |
| 3 | WebSearch (named-after / formal-group framing) | "nLab p-adic exponential logarithm isomorphism formal group units local ring" | yes | exp/log as inverse isomorphisms; the multiplicative formal group `M(X,Y)=X+Y+XY` induces `log`; image of `log` on principal units `1+m_K` | nLab *formal group*; Grossman-Naples formal-groups notes; "On the image of p-adic logarithm on principal units". Confirms the object is the principal-unit / formal-group exp-log iso. |
| 4 | ChatGPT MCP | (intended: "standard def + generality + history of the integral p-adic exp `pℤ_p → 1+pℤ_p`, and how it is usually *typed* — as a group hom, a power series, or a guarded total function?") | n/a | — | **No ChatGPT/codex MCP server is configured in this environment** (checked `~/.claude*`; none present). Recorded n/a — substituted by the four WebSearch sweeps (channels 1–3, 9, 10) at three generality levels, the local sibling reports, and the in-repo cross-checks. The standard-form + generality questions are nonetheless fully answered by channels 1–3. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` symlink | n/a | (no `references/` dir; no `refs` symlink) | Recorded n/a — directory absent. The module docstring's citations (RJW Lem 5.14, Cassels §12, Washington §5.1) substitute and agree with channels 1–3. |
| 6 | nLab | `formal group`, `p-adic exponential` (via channel-3 WebSearch surfacing nLab) | partial | exp/log via the multiplicative formal group; no standalone "p-adic exponential" page | nLab treats the exp/log iso through *formal group laws*; the integral exp `pℤ_p→1+pℤ_p` is the formal-group exp specialised. No junk-total encoding, of course (nLab is informal). |
| 7 | nCatLab (categorical) | (same as 6) | n/a | not a 1-categorical construction with a universal property to look up | The integral exp is a concrete group hom / power-series map; the only "categorical" framing (formal groups, channel 6) is covered. |
| 8 | Stacks Project | — | n/a | not a scheme-theoretic / algebraic-geometry concept in Stacks' scope | The p-adic integral exp is p-adic analysis / number theory; absent from Stacks. (Formal groups appear in Stacks but not this exp.) |
| 9 | MathOverflow / Math.SE | (surfaced via channels 1–2: UChicago REU, MIT notes, PlanetMath, principal-units papers) | yes | consensus: `exp: pℤ_p→1+pℤ_p` (odd `p`) iso, `log` inverse | No disagreement on the standard form across notes/MO/SE. |
| 10 | recent arXiv (≤5 yrs) | "p-adic exponential integral valued Z_p formalization Lean mathlib principal units 2024 2025"; "On the image of p-adic logarithm on principal units" (1904.09850, ON THE IMAGE… 2024) | yes | same `exp: pℤ_p→1+pℤ_p`; recent work studies the *image* of `log` on principal units (refining the iso), confirms the object is current | Also surfaced: Narayanan, *Formalization of p-adic L-functions in Lean 3* (arXiv 2302.14491) — the prior Lean-3 p-adic-L-function project; relevant as the direct ancestor of this AINTLIB project. No published mathlib/Lean-4 `pZpExp` exists. |

The protocol passes for the available channels: WebSearch ran **4** distinct
queries (channels 1, 2, 3, 10) at three generality levels (specific
`pℤ_p→1+pℤ_p`; the iso/odd-`p` form; the formal-group framing); ChatGPT MCP is
**n/a — not installed** (explicitly recorded, with WebSearch + sibling reports
substituting); local references **n/a — absent**; nLab checked (formal-group
framing); nCatLab / Stacks recorded n/a with reasons; MO/SE and arXiv each hit.

### Literature summary (Phase 3)

Concept identified as: the **integral p-adic exponential** — the p-adic
exponential `exp(x)=∑ xⁿ/n!` restricted to `pℤ_p` (odd `p`), where it converges
and is integral, giving the classical **exponential isomorphism**
`exp : pℤ_p → 1 + pℤ_p` (inverse to the p-adic logarithm). Standard since
Iwasawa; textbook in Washington §5.1, Cassels §12, Koblitz, Robert.
Sources agree on the standard form: **yes** (for the *mathematics*).
Most general standard form: for a complete nonarchimedean field `K ⊇ ℚ_p` with
maximal ideal `m_K`, `exp` is an isomorphism between an additive disc and a
multiplicative disc of principal units `1 + m'_K`; specialised to `K = ℚ_p` (odd
`p`) this is `exp : pℤ_p ≅ 1 + pℤ_p`.
Generality dimensions where the literature varies:
  - **Typing of the object.** The literature treats this *informally* as a map.
    Formalisations have a real choice: (i) a bare/guarded total function, (ii) a
    bundled group homomorphism `Multiplicative pℤ_p → (1+pℤ_p)` / `pℤ_p → ℤ_[p]ˣ`,
    (iii) a continuous map `C(ℤ_[p], ℤ_[p])` (mathlib's idiom for maps on `ℤ_[p]`,
    cf. `mahler`), or (iv) characterised via the formal-group / `AddChar` route.
    The literature does not pick for us — this is the crux of the BORDERLINE.
  - **Base.** `ℚ_p` (the project's `pZpExp`) vs. arbitrary `K ⊇ ℚ_p`. The project
    states the analytic `padicExp` at full `L`-generality but `pZpExp` only at
    `L = ℚ_p` (integral restriction lives in `ℤ_[p]`).
  - **Parity.** odd `p` (the `hp2 : p ≠ 2` hypothesis on the lemmas); for `p = 2`
    the convergence/integrality domain shrinks to `4ℤ_2`.
Disagreement with the literature: the *mathematics* of `pZpExp` agrees with the
standard exp iso. The *encoding* (a `dite`-guarded junk-total `ℤ_[p] → ℤ_[p]`
with junk value `1` off-domain) has **no literature analog** — it is a Lean
totality convenience, not a mathematical object anyone names.

---

### Generality analysis — `PadicLFunctions.pZpExp`

Literature-standard form (from Phase 3): the exponential isomorphism
`exp : pℤ_p → 1 + pℤ_p` (odd `p`), i.e. the integral p-adic exponential.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/other form exists? | Reason it can/can't be changed |
|---|------------------------|-------------------|--------------------------|---------------------------|---------------------------------|
| 1 | domain/codomain type | total `ℤ_[p] → ℤ_[p]` (junk off `pℤ_p`) | a map `pℤ_p → 1+pℤ_p` (a *subset/subtype* pairing, classically a group iso) | **yes (richer)** | The standard object is typed on `pℤ_p` and lands in `1+pℤ_p`; the project flattens it to a total `ℤ_[p]→ℤ_[p]` with a junk default. A bundled `pℤ_p → ℤ_[p]ˣ` / group hom would carry the homomorphism property as data. Not "weaker" — *better-typed*; a design choice. |
| 2 | base field `ℚ_p` | fixed `ℚ_p` (integral exp lives in `ℤ_[p]`) | arbitrary `K ⊇ ℚ_p`, `1+m_K` | yes (more general) | The integral restriction is inherently about `ℤ_[p] = 𝒪_{ℚ_p}`; generalising to `𝒪_K` is the maximal classical form but requires the project's `L`-level analytic API (which exists for `padicExp`) plus a ring-of-integers wrapper. |
| 3 | parity `p ≠ 2` | on lemmas only (`hp2`) | odd `p` standard; `p=2` uses `4ℤ_2` | n/a | Standard restriction; not a generality defect. |
| 4 | junk value `1` | `1` (the exp's value at `0`) | n/a (no junk in the math) | — | The junk choice (`1`, matching `exp 0`) is a Lean artifact; reasonable, but invisible to the mathematics. |

### Generality verdict (Phase 4b)

The current form is: **NEITHER cleanly MAXIMALLY GENERAL NOR STRICTLY NARROWER —
it is a *differently-typed* (junk-total) encoding of the standard object.** It is
narrower in base (`ℚ_p` only) and *less structured* than the literature object (a
bare function vs. a group homomorphism / iso), but this is an encoding choice, not
a missing typeclass weakening of the usual kind.
Number of weakening/retyping opportunities: 2 substantive (richer typing as a
bundled hom; base-field generalisation), both design-level.
Cost of restating at the literature's homomorphism typing: **MODERATE** — the
project already proves the homomorphism property (the `AddChar κ` built from
`pZpExp` in `padicExp_smul_padicLog_eq_onePAdicPow`), so bundling it is largely
re-packaging existing facts; base-field generalisation is more (EXPENSIVE-ish).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | no | already typeclass-driven (the `omit`ed `L`-classes) | — |
| 2 | sequences/metric → filters/topological? | no | underlying `padicExp` is already `tsum`/filter-based | — |
| 3 | **construct an object → universal-property / characterisation class?** | **yes** | The project *itself* shows the meaningful content of `pZpExp` is captured by `PadicInt.onePAdicPow` — a continuous `AddChar` characterised by its value at `1` (via `eq_addChar_of_value_at_one`). The modern idiom for "the `s`-power / exp map" on `1+pℤ_p` is the **continuous additive/multiplicative character**, which mathlib's `NumberTheory/Padics/AddChar.lean` (`addChar_of_value_at_one`, `continuousAddCharEquiv`) already supports. | the whole `AddChar`/continuous-character API: composition, `map_nsmul_eq_pow`, uniqueness, continuity — exactly what `onePAdicPow` uses. A bundled exp-as-character composes with it directly. |
| 4 | set-with-closure-predicate → bundled substructure? | partial | the codomain `1+pℤ_p` is currently implicit; bundling exp as `pℤ_p → (1+pℤ_p)` (a subgroup of `ℤ_[p]ˣ`) would make the multiplicative target explicit | mathlib's `Subgroup`/units API for `1+pℤ_p` |
| 5 | field-specific → weaken typeclasses? | partial | base `ℚ_p` → `𝒪_K` for `K⊇ℚ_p` (see Phase 4a #2) | the project's `L`-level analytic exp API |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index → general structure? | no | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it points *away* from `pZpExp` as the object to
upstream.** The contemporary mathlib-idiomatic encoding of the exp/`s`-power map on
`1+pℤ_p` is the **continuous character** (mathlib `AddChar.addChar_of_value_at_one`
/ `continuousAddCharEquiv`), which the project *already* uses via its own
`PadicInt.onePAdicPow`. `pZpExp` is the *junk-total scaffolding* used to build that
character (it is literally fed into `AddChar κ` in
`padicExp_smul_padicLog_eq_onePAdicPow`), not the character itself. Real
mathematical improvement of the modern form over `pZpExp`: the character carries
the homomorphism property and continuity as data and plugs into mathlib's
character API; the junk-total function carries neither and needs `pZpExp_coe` /
`pZpExp_sub_one_mem` re-derivations at every use. This is a genuine organisational
improvement — **but** it does not yield a clean "generalise `pZpExp` then PR"
target, because the better object is a *different* construction (and a partial
version, `continuousAddCharEquiv`, is already upstream). That is precisely why the
verdict is BORDERLINE rather than YES-but-generalise-first: the "what to upstream,
if anything" question needs a human.

---

### Diamond / defeq risk — `PadicLFunctions.pZpExp` (kind: `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | `pZpExp : ℤ_[p] → ℤ_[p]` is a plain function; not an `instance`, keys no typeclass search. |
| 2 | Reducibility leak | low | Not `@[reducible]`; `noncomputable def` with a `dite` body. Unfolds only via explicit `rw [pZpExp]` (as in `pZpExp_coe`, `dif_pos hle`). |
| 3 | Non-canonical unfolding | low–med | The body is a `dite` on `‖padicExp p (↑x)‖ ≤ 1` — a *non-decidable-in-practice* predicate carried by `Classical`/`dite`. `simp`/`rfl` will **not** reduce it without the integrality proof (`dif_pos`/`dif_neg`); this is intended (the def is sealed behind `pZpExp_coe`). A mathlib reviewer would flag the junk `dite` as the main stylistic question — mathlib prefers `Function.extend`/subtype-restricted or bundled forms over hand-rolled `dite` junk-totals. |
| 4 | Instance priority collision | n/a | not an instance. |
| 5 | Universe-polymorphism issues | none | no universe variables beyond the fixed `ℤ_[p]`. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` introduced; uses the existing `ℤ_[p] ↪ ℚ_[p]` coercion only. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW**.
Top risks: the `dite` junk-total encoding (row 3) is a *style* concern, not an
infrastructure hazard — but it is the kind of thing a mathlib reviewer would ask
to be replaced by a bundled/`extend`-based form. Folded into the BORDERLINE
questions (Phase 7), not a blocker.

---

### Mathlib search-status: `PadicLFunctions.pZpExp`

[A] Lean-Finder       "p-adic exponential integral Z_p", "exp p Z_p into 1 + p Z_p", "integral exponential principal units", "exp restricted to ring of integers" →  no hit on any integral/p-adic exp; only the Banach-algebra `NormedSpace.exp` (a `L→L` analytic exp, not integral-valued, not `ℤ_[p]→ℤ_[p]`).
[B] Loogle            type pattern `ℤ_[?p] → ℤ_[?p]` for an exp/power-series map; `_ → ℤ_[?p]` guarded by `‖·‖ ≤ 1`; `dite (‖_‖ ≤ 1)` packaging a `PadicInt` →  hits are `PadicInt.inv`, `mahler`, `mahlerSeries` (continuous `ℤ_[p]→ℤ_[p]`), none an exponential; no junk-total integral-exp.
[C] LeanSearch        "integer-valued p-adic exponential on p Z_p"; "exponential isomorphism p Z_p to 1 + p Z_p"; "exp mapping into the units of the p-adic integers" →  no p-adic exp; surfaces `NormedSpace.exp` (general) and `mahler` (continuous map idiom) only.
[D] Grep mathlib src  `grep -rinE "p.adic.*exp|padic.*exp"`; `grep "1 + p\|1+p.*ℤ_\[\|pℤ_p\|principal unit"`; `grep "‖.*‖ ≤ 1.*then.*⟨\|dite.*norm.*le_one"` over all of Mathlib →  **No p-adic exponential, no integral exp, no `pℤ_p→1+pℤ_p` map, no junk-total integral-restriction-of-exp pattern anywhere.** The Padics `exp` hits are `WithZero.exp`/`ℤᵐ⁰` valuation maps (`Mathlib/NumberTheory/Padics/PadicNumbers.lean`), unrelated. PadicInt is the subtype `{x : ℚ_[p] // ‖x‖ ≤ 1}` (`PadicIntegers.lean:60`) — the `⟨padicExp …, h⟩` packaging is the standard `PadicInt.mk`, but there is no exp built on it.
[E] Name pattern      `lean_local_search`/grep: `pZpExp`, `onePAdicPow`, `principalUnit`, `oneSubMul`, `expUnitary`, `addChar_of_value_at_one` →  mathlib has `selfAdjoint.expUnitary` (C*-algebra, unrelated), `AddChar.addChar_of_value_at_one` + `continuousAddCharEquiv` (`NumberTheory/Padics/AddChar.lean` — the *character* machinery the project's `onePAdicPow` is built on, **not** an exp). No `pZpExp`, no p-adic integral exp.

Searched for both:
  - the user's current form (junk-total `ℤ_[p] → ℤ_[p]` integral exp), and
  - the literature-standard form (the homomorphism `exp : pℤ_p → 1+pℤ_p`, and the
    more general `exp : pℤ_p`-disc → principal units over `𝒪_K`).

**Concluded: not in mathlib** (all 5 methods exhausted, plus the literature-standard
homomorphism form and the modern character form). Mathlib has the *adjacent*
infrastructure — `NormedSpace.exp` (the analytic `L→L` exp the sibling `padicExp`
specialises), `PadicInt` as `{‖·‖≤1}`, and the `AddChar`/continuous-character
machinery (`addChar_of_value_at_one`, `continuousAddCharEquiv`) that the project's
`onePAdicPow` already uses — but **no integral p-adic exponential**.

---

### Call sites — `PadicLFunctions.pZpExp`

Internal use count (within the project, **not** counting the declaring file): **1**
(`ResidueZeta.lean:1727`, `pZpExp p (0 : ℤ_[p]) = 1`). Additionally the *lemma*
`pZpExp_coe` is used externally at `ResidueZeta.lean:112, 256`.
External-to-file callers (distinct files): **1** (`ResidueZeta.lean`).
Within-declaring-file uses of the raw def (`PadicExp.lean`, excluding the def line):
**7** — all in `pZpExp_coe` (1047, 1060), `pZpExp_sub_one_mem` (1064), and the
agreement theorem `padicExp_smul_padicLog_eq_onePAdicPow` (1113, 1119, 1122, 1142,
1155, where `pZpExp` is fed into the `AddChar κ`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ResidueZeta.lean:1727 | `have hexp0 : pZpExp p (0 : ℤ_[p]) = 1 := by …` (only raw-def external use) |
| ResidueZeta.lean:112 | `… pZpExp_coe p hp2 htℓmem, …` (via the coe lemma) |
| ResidueZeta.lean:256 | `… pZpExp_coe p hp2 hmem]` (via the coe lemma) |
| PadicExp.lean:1113 | `pZpExp p (s * pZpLog p x) = PadicInt.onePAdicPow p x hx s` (the bridge — main use) |
| PadicExp.lean:1122 | `{ toFun := fun t => pZpExp p (t * ℓ) … }` (builds `AddChar κ` from `pZpExp`) |
| PadicExp.lean:1142,1155 | `‖pZpExp p (a*ℓ) − pZpExp p (b*ℓ)‖ ≤ ‖a−b‖`; `((pZpExp p (1*ℓ):ℤ_[p]):ℚ_[p]) = …` |

Inline-derivation grep (was the `dite` integrality-guard body re-derived elsewhere
without `pZpExp`?): **none** — the `dif_pos`/`if ‖padicExp …‖ ≤ 1` pattern occurs
*only* in the def and its own `pZpExp_coe`. No consumer re-implements it.

Call-sites signal: the raw def has **K = 1 external** + **7 internal** uses; the
internal uses are overwhelmingly *scaffolding* for one theorem
(`padicExp_smul_padicLog_eq_onePAdicPow`, which builds an `AddChar` from `pZpExp`
and then immediately equates it to `onePAdicPow`). This is the
"K small, exists to construct one bridge" pattern — real but narrow API, with the
mathematically-meaningful endpoint being `onePAdicPow`, not `pZpExp` itself. Per
the skill's table this is exactly a **BORDERLINE / "wrong-abstraction-?"** signal
rather than a clean YES.

### Composition check (Phase 6)

Can `pZpExp` be obtained from mathlib in ≤3 chained calls? — **No.** Mathlib has
no p-adic exponential, so even the *true branch* `⟨padicExp p (↑x), h⟩` needs the
project's own `padicExp` (itself `NormedSpace.exp` specialised, per the sibling
report — but mathlib's `exp` is `L→L`, not integral, so packaging it as `ℤ_[p]`
still needs the integrality proof `h : ‖exp x̄‖ ≤ 1`, which is *not* a mathlib
lemma — it is the project's `coe_norm_le_inv_of_mem_span` + `norm_padicExp_sub_one`
chain).

Attempt 1 (build the junk-total directly from mathlib):
```lean
-- would need: NormedSpace.exp (= padicExp on ℚ_[p]) + an integrality proof + dite packaging
fun x : ℤ_[p] => if h : ‖NormedSpace.exp ((x:ℚ_[p]))‖ ≤ 1 then ⟨_, h⟩ else 1
```
  - Mathlib decls available: `NormedSpace.exp`, `PadicInt` subtype, `dite`.
  - Result: **fails as a composition** — the integrality predicate
    `‖exp x̄‖ ≤ 1` is exactly the nonarchimedean fact mathlib *lacks* (flagged as a
    genuine gap in the sibling `padicExp` report). Without it, the `dite` is just a
    re-statement of the problem, not a derivation; *with* the project's
    integrality API it is a multi-`have` proof, not a 1–3-call composition.
  - This matches the Phase-6 heuristics: multiple `have`s with nontrivial reasoning
    (the integrality bound) between them = a proof, not a composition.

Conclusion: **NOT-COMPOSABLE.** `pZpExp` is not a ≤3-call mathlib composition; it
depends on project-only analytic API (the p-adic exp itself and its
nonarchimedean integrality bound), neither of which is in mathlib. (This rules out
`NO-composable-from-mathlib`.)

---

## Verdict: `PadicLFunctions.pZpExp`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the integral p-adic exponential
  `exp : pℤ_p → 1+pℤ_p` (odd `p`) is a **standard, named, mathlib-worthy** object
  (Washington §5.1, Cassels §12, Gupta REU, PlanetMath, principal-units papers).
  But the *junk-total `dite` encoding* under assessment has **no literature
  analog** — it is a Lean totality device.
- Generality analysis (Phase 4b/4c): NEITHER cleanly maximal NOR a standard
  typeclass-narrowing — it is a *differently-typed* encoding. The modern-idiom
  check (4c) finds the contemporary form is a **continuous character** (mathlib's
  `addChar_of_value_at_one`/`continuousAddCharEquiv`), which the project *already*
  uses via `onePAdicPow` — `pZpExp` is scaffolding for that bridge, not the
  endpoint.
- Mathlib search (Phase 5): **not in mathlib** (5 methods + literature form + modern
  form). Mathlib has the adjacent infrastructure (`NormedSpace.exp`, `PadicInt`,
  the `AddChar` machinery) but no integral p-adic exp.
- Composition check (Phase 6): **NOT-COMPOSABLE** (depends on project-only analytic
  exp + the nonarchimedean integrality bound mathlib lacks).

**Rationale.**
Two facts pull in opposite directions and cannot be reconciled without a human.
On one hand, the *mathematics* `pZpExp` realises — the integral p-adic exponential
and the exp/log isomorphism `pℤ_p ≅ 1+pℤ_p` — is exactly the kind of classical,
named, currently-missing object mathlib wants (the sibling `padicExp` report
already flags the surrounding nonarchimedean-exp API as a real mathlib gap). So a
flat "NO" would be wrong: mathlib does **not** have this, and it is not composable.
On the other hand, the *specific Lean declaration* is a `dite`-guarded **junk-total
`ℤ_[p] → ℤ_[p]`** whose off-domain value is the arbitrary junk `1`, whose
mathematically-meaningful content the project itself immediately re-expresses as
the continuous character `PadicInt.onePAdicPow` (proved equal in
`padicExp_smul_padicLog_eq_onePAdicPow`), and whose raw-def call sites (K = 1
external, 7 internal) are almost entirely scaffolding to build that character. A
mathlib reviewer would not accept the junk-total form as-is — they would ask for a
bundled group homomorphism `pℤ_p → ℤ_[p]ˣ` (or `1+pℤ_p`), or the character form
that is *partially already upstream*. So a flat "YES-add-as-is" would also be
wrong (the form is not the right mathlib form), and "YES-but-generalise-first" is
not clean either, because the better target is a *different construction* (a
character / group hom), not a generalisation of this `dite`. The choice among
"upstream a bundled `pℤ_p→1+pℤ_p` exp iso", "upstream nothing — the content is the
already-bridged character", and "keep `pZpExp` project-local as scaffolding" is a
design/scope call. Hence BORDERLINE.

This also threads the sibling-report consistency: `padicExp` is `NO-mathlib-has-it`
(it *is* `NormedSpace.exp`). `pZpExp` is **not** the same situation — it is the
*integral restriction*, which mathlib does not have in any form — so it does not
inherit that NO. The honest verdict is that the mathematics is upstream-worthy but
the encoding/scope needs a decision.

**Numbered questions (≤5):**

1. **Do you want the integral p-adic exponential upstreamed to mathlib at all**,
   or is `pZpExp` intentionally project-local scaffolding for building
   `PadicInt.onePAdicPow` (which is the object you actually consume)? If the latter,
   this is a clean NO-for-mathlib (keep it local, no upstream).
2. **If upstreaming: which encoding?** (a) a bundled **group homomorphism**
   `pℤ_p → ℤ_[p]ˣ` / `pℤ_p → (1+pℤ_p)` carrying the hom + continuity as data
   (mathlib-preferred); (b) a **continuous map** `C(ℤ_[p], ℤ_[p])` in the `mahler`
   idiom; or (c) the present **junk-total `dite`** `ℤ_[p] → ℤ_[p]`? Mathlib reviewers
   will almost certainly reject (c)'s junk default — is re-typing to (a) acceptable?
   (Cost is MODERATE: the hom property is already proved inside
   `padicExp_smul_padicLog_eq_onePAdicPow`.)
3. **Is the right mathlib contribution the *isomorphism* `pℤ_p ≅ 1+pℤ_p`** (the full
   exp/log pair, the classical theorem) rather than the bare exp map? If so the
   target is a `MulEquiv`/`AddEquiv`-style bundle, and `pZpExp`/`pZpLog` are its two
   underlying maps.
4. **Base generality:** ship at `ℚ_p` (matching `pZpExp`) only, or at the
   ring-of-integers `𝒪_K` of a complete nonarchimedean `K ⊇ ℚ_p` (the maximal
   classical form, requiring the `L`-level analytic exp API the project already has
   for `padicExp`)?
5. Given mathlib already has `AddChar.continuousAddCharEquiv`
   (`NumberTheory/Padics/AddChar.lean`), should the project's `onePAdicPow` +
   integral-exp content be **refactored to land on the upstream character API**
   first — in which case `pZpExp` may not need to ship independently at all?

Next action: user answers Q1–Q5; re-run `/mathlibable PadicLFunctions.pZpExp`
(with the chosen encoding/scope as a Phase-1 input) to resolve to a concrete YES
bucket — or to confirm "keep project-local" (effectively NO-for-mathlib). Likely
outcomes:
  - Q1 = local-only → drop from mathlib consideration; `pZpExp` stays scaffolding.
  - Q1 = upstream + Q2 = (a) group hom / Q3 = iso → flips to **YES-but-generalise-first**
    with the restatement being the bundled `pℤ_p → ℤ_[p]ˣ` hom (or the
    `pℤ_p ≅ 1+pℤ_p` equiv), at the Q4-chosen base.
  - Q5 = refactor onto upstream `AddChar` first → the contribution becomes the
    nonarchimedean-exp API about `NormedSpace.exp` (already flagged in the sibling
    `padicExp` report), not `pZpExp` itself.

---

## Next step

User answers the five numbered questions above. The core decision is **scope**
(upstream the integral p-adic exp at all?) and, if yes, **encoding** (bundled group
homomorphism / iso vs. the present junk-total `dite`). On `local-only` → keep
`pZpExp` as project scaffolding (no mathlib PR). On `upstream` → re-run
`/mathlibable` with the chosen bundled form, expecting YES-but-generalise-first
toward `pℤ_p → ℤ_[p]ˣ` (or the `pℤ_p ≅ 1+pℤ_p` equiv), since mathlib genuinely
lacks the integral p-adic exponential in every form.
