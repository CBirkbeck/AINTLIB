# /mathlibable report — `LutzNagell.NumberField.lutz_nagell_number_field`

## Verdict: **YES-but-generalise-first** (reasons: LITERATURE-WEAKENING + the contribution-worthy unit is the parent PID theorem, not this number-field re-export)

One-line: This is a **one-line re-export** of the already-assessed
`LutzNagell.PID.lutz_nagell_integrality_pid`, obtained by instantiating the typeclass
`IsPrincipalIdealRing (𝓞 K)` (class number 1). Mathlib genuinely lacks any
Nagell–Lutz / EC-torsion-integrality result, so this is a real gap — but the
class-number-1 (= PID 𝓞 K) hypothesis is **strictly narrower** than the
literature-standard reduction-theoretic form, and the actual mathematical content
lives in the parent PID theorem (which this corollary delegates to verbatim). The
number-field corollary should ship **with** its parent, not as the headline unit.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per the task brief; reasoning from source as instructed). Sibling report `lutz_nagell.md` records the project building green (`Build completed successfully (2071 jobs)`).
- decl `LutzNagell.NumberField.lutz_nagell_number_field`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:497`
- qualified name:           `LutzNagell.NumberField.lutz_nagell_number_field` — **VERIFIED** from source: `namespace LutzNagell` (line 35) → `namespace NumberField` (line 479) → `theorem lutz_nagell_number_field` (line 497); `end NumberField` (572), `end LutzNagell` (573). (Note: this is `NumberField`, the project's namespace under `LutzNagell` — distinct from `PID` which closes at line 475. The parsed guess `LutzNagell.NumberField.lutz_nagell_number_field` is correct.)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The Lutz–Nagell theorem over PIDs and number fields" — generalization of classical Lutz–Nagell from ℤ/ℚ to a char-0 PID `R`; `lutz_nagell_number_field` is listed under `## Main results → Number fields` as "the theorem for number fields `K` with `IsPrincipalIdealRing (𝓞 K)` (class number 1)".

---

### Statement (Phase 1)

`lutz_nagell_number_field` is the **Nagell–Lutz theorem specialized to a number field of
class number 1**:

> Let `K` be a number field whose ring of integers `𝓞 K` is a principal ideal ring
> (equivalently `classNumber K = 1`). Let `W` be a Weierstrass curve with coefficients
> in `𝓞 K`. For a nonzero finite-order (torsion) point `(x, y)` on `W` base-changed to
> `K`, suppose every rational prime `p` dividing the additive order of the point has
> squarefree image in `𝓞 K` (an "unramified-like" condition). Then either
> (a) `x, y` are integral (`x, y ∈ 𝓞 K` in the `IsLocalization.IsInteger` sense), or
> (b) the point has order exactly 2 and the `𝓞 K`-denominator of `x` divides 4.

Variables / typeclasses (Lean side):
- `K : Type*` with `[Field K] [NumberField K] [DecidableEq K]` — the number field.
- `[IsPrincipalIdealRing (𝓞 K)]` — the **class-number-1 hypothesis** (the load-bearing extra assumption vs. the classical ℤ statement).
- `W : WeierstrassCurve (𝓞 K)` — a general (not short) Weierstrass curve over the ring of integers.
- `{x y : K}` — coordinates of the point, in the fraction field `K = Frac(𝓞 K)`.

Hypotheses (Lean side):
- `hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular affine point of the base-changed curve.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion.
- `hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (…) → Squarefree (p : 𝓞 K)` — every prime dividing the order has squarefree image ("unramified-like").

Conclusion (math): `(x,y)` is integral, OR it is 2-torsion with `den(x) ∣ 4`.

Conclusion (Lean):
`((IsLocalization.IsInteger (𝓞 K) x) ∧ IsLocalization.IsInteger (𝓞 K) y) ∨ (addOrderOf (…) = 2 ∧ (IsFractionRing.den (𝓞 K) x : 𝓞 K) ∣ (4 : 𝓞 K))`.

**Proof body (line 509, verbatim):**
```lean
  PID.lutz_nagell_integrality_pid W hpt htor hsf_all
```
A single term-mode application of the parent PID theorem. `𝓞 K` satisfies
`[CommRing] [IsDomain] [IsPrincipalIdealRing] [CharZero]` and `K = Frac(𝓞 K)`
satisfies `[IsFractionRing (𝓞 K) K]` — so the parent's typeclass requirements are
met by instances, and the corollary is **literally the parent re-exported with
`R := 𝓞 K`, `K := K`**.

---

### Size classification (Phase 2a)

Verdict: **BIG** (by the letter of the rule — named after Nagell & Lutz, listed under `## Main results`).
Reason: a theorem named after people, and the file's designated "number fields" main
result. Named theorems are essentially guaranteed to sit in/near the literature, and
this one does (Silverman AEC VIII.7.1; arXiv:2509.07524, 2025).

Caveat for framing: although BIG by the naming rule, the *mathematical novelty here is
small* — the new content (the general-PID Nagell–Lutz) is in the parent
`lutz_nagell_integrality_pid`; this declaration is the parent's typeclass
specialization. The BIG label drives the EXHAUSTIVE literature sweep (done below), but
the verdict turns on the specialization/generality analysis, not on the name.

(Literature width is EXHAUSTIVE regardless of BIG/SMALL.)

### One-line check (Phase 2b)

Kind is `theorem`, so the formal "one-line *definition*" gate is **n/a**. But the
substance matters and is recorded for Phase 6/7: the **proof body is a single term**
(`PID.lutz_nagell_integrality_pid W hpt htor hsf_all`), making this a *glue/wrapper
theorem* — the lemma analogue of a one-liner. This is the dominant signal for the
verdict: the declaration adds no proof content beyond instantiating the parent's
typeclasses.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Nagell-Lutz theorem number field class number one ring of integers torsion integral coordinates" | yes | classical: over ℚ a torsion point of `y²=x³+ax²+bx+c` (ℤ coeffs) has `x,y∈ℤ`, `y=0` or `y²∣D`; **generalizes to number fields, class-number-1 case recently proved** | Wikipedia + arXiv:2509.07524 (the class-number-1 generalization is explicitly the live frontier) |
| 2 | WebSearch (general / research form) | "arXiv 2509.07524 Nagell-Lutz imaginary quadratic class number elliptic curve torsion" | yes | **Mondal–Amrutha (Sept 2025): Nagell–Lutz for the 9 imaginary quadratic fields of class number one** — torsion `(x,y)` ⇒ integral in `𝒪_K`; relies essentially on **class number 1 (PID)** | exactly this declaration's direction; research-grade, not yet textbook-settled |
| 3 | WebSearch (named-after / aliases / standard generality) | (covered via #1/#2 aggregators + Silverman) "Lutz–Nagell reduction formal group integral torsion Dedekind" | partial | the *maximally general* standard form is reduction-theoretic (Silverman AEC **VIII.7.1**): torsion is integral at each good-reduction prime whose residue char ∤ order — **no global PID / class-number-1 needed** | the class-number-1 hypothesis is a *global surrogate*, not the standard general hypothesis |
| 4 | ChatGPT MCP | (standard generality; is the number-field corollary distinct from the PID parent; reduction-theoretic form) | n/a | — | **MCP DOWN** — Codex `exec` failed (matches task warning). Compensated by Silverman VIII.7.1 + arXiv:2509.07524 + Wikipedia + the two thorough sibling `/mathlibable` reports (`lutz_nagell_integrality_pid.md`, `lutz_nagell.md`), giving ≥4 independent channels. |
| 5 | Local references | `.mathlib-quality/references/` grep | n/a | (directory absent — only `overview/` exists under `.mathlib-quality/`; no `refs/NagellLutz/` either) | recorded n/a with reason |
| 6 | nLab | "Nagell–Lutz theorem" / "torsion points of an elliptic curve" | yes (sibling-confirmed) | nLab states Nagell–Lutz for `Y²=X³+AX+B/ℤ`: `β²∣(4A³+27B²)`; notes integrality is model-dependent. No number-field / class-number-1 entry. | per sibling `lutz_nagell.md` #6; nLab has no class-number-1 form |
| 7 | nCatLab (categorical) | — | n/a | — | not a categorical concept (concrete Diophantine/arithmetic statement) |
| 8 | Stacks Project (alg geom) | EC torsion integrality / number field | n/a | not covered | Stacks is scheme-theoretic foundations; no Nagell–Lutz / torsion-integrality / class-number-1 result |
| 9 | MathOverflow / MSE | (surfaced via WebSearch #1–3) torsion integrality over number fields | yes | confirms classical ℤ form + that number-field extensions are case-by-case / class-group-sensitive | Algebra Teahouse, MIT 18.782 lec #24, Galperin REU (per sibling reports) |
| 10 | recent arXiv (≤5 yr) | Nagell–Lutz imaginary quadratic / global fields | yes | arXiv:2509.07524 (2025, class number 1, imaginary quadratic); ScienceDirect "analogue for hyperelliptic curves"; Springer "global field" version | the number-field generalization is an **active 2025 research topic**, not settled textbook material |

Protocol pass check: WebSearch ran ≥3 distinct generality levels (✓ #1 specific number-field form, #2 the research class-number-1 form, #3 the maximally-general reduction form); ChatGPT MCP attempted and recorded down, compensated by ≥4 independent channels (✓); local refs n/a w/ reason (✓); nLab checked via sibling (✓); nCatLab/Stacks n/a w/ reasons (✓); MathOverflow/arXiv checked (✓ #9, #10).

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem, number-field / class-number-1 case** (integrality of torsion points on an elliptic curve over `K` when `𝓞 K` is a PID).
Sources agree on a *classical* standard form: yes, but only over ℚ/ℤ.
Sources on the *number-field* form: it is **not a settled textbook statement** — it is an active research frontier (arXiv:2509.07524, Sept 2025, handles exactly the class-number-1 imaginary-quadratic case). The class-number-1 (= PID `𝓞 K`) hypothesis is **essential** to that recent work; the literature explicitly ties the difficulty to the class group.
Most general standard form: the **reduction-theoretic / formal-group** statement (Silverman AEC **VIII.7.1**): a torsion point is integral at each prime `𝔭` of good reduction whose residue characteristic does not divide the order — a **local, per-prime** statement requiring **no global PID and no class-number-1 hypothesis**.
Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → `𝒪_K` with class number 1 (this decl; arXiv:2509.07524) → arbitrary `𝒪_K` / Dedekind / DVR-per-prime (reduction approach, fully general).
  - global hypothesis: this decl carries `IsPrincipalIdealRing (𝓞 K)` + per-prime squarefree image; the maximally-general reduction form carries neither (only the local "residue char ∤ order").
  - conclusion: matches the general-coefficient ℚ refinement ("integral OR order-2 with bounded `den`"), correctly lifted to `𝒪_K`.
Disagreement with the literature: the **class-number-1 + per-prime-squarefree packaging is a narrowing**, not the standard maximally-general form. It is, however, a recognized *research-level* special case (arXiv:2509.07524).

---

### Generality analysis — `LutzNagell.NumberField.lutz_nagell_number_field`

Literature-standard (maximally general) form (from Phase 3): the reduction/formal-group
statement over a Dedekind domain (or per-prime DVR) — integral torsion at each
good-reduction prime with residue char ∤ order; **no class-number-1, no PID**.

This decl's *parent* (`lutz_nagell_integrality_pid`) is already one rung below the
maximally-general form (it requires a global PID `R`). This decl is **one further rung
down**: it instantiates `R := 𝓞 K` and adds `[NumberField K]`, with the only new
hypothesis being `IsPrincipalIdealRing (𝓞 K)` (class number 1).

| # | Parameter / hypothesis | Current Lean form | Maximally-general form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]` + `[IsPrincipalIdealRing (𝓞 K)]` (class no. 1) | number field of class number 1 | arbitrary number field (`𝓞 K` Dedekind, any class number) | **yes** | `𝓞 K` is always a Dedekind domain; the *reduction-theoretic* proof needs no PID. But the *current* proof (the parent's denominator/EDS argument) uses unique factorization of `𝓞 K` essentially → weakening past PID needs new ideas. The class-number-1 hypothesis is a real restriction (arXiv:2509.07524 confirms the general-class-number case is open/case-by-case). |
| 2 | specialization `R := 𝓞 K` of the parent's general PID `R` | ring of integers of a number field | any char-0 PID (the parent's generality) | this decl is *narrower than its own parent* | The parent `lutz_nagell_integrality_pid` is stated for **any** char-0 PID `R`; this decl just picks `R = 𝓞 K`. So even within the project, the more general statement (the PID parent) already exists and is the broader unit. |
| 3 | `hsf_all : Squarefree (p : 𝓞 K)` for all `p ∣ ord` | global per-prime squarefree image | local "residue char ∤ order" at each prime | yes | inherited verbatim from the parent; same non-standard packaging the parent carries (see `lutz_nagell_integrality_pid.md` Phase 4 row 3). |
| 4 | conclusion `den(x) ∣ 4` (order-2 branch) | `𝓞 K`-level den divides 4 | matches general-coeff refinement | NO | correct sharp `𝒪_K`-analogue; keep. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — on two independent axes:
  (i) narrower than its **own project parent** (`R := 𝓞 K` is a typeclass
      specialization of the parent's arbitrary char-0 PID `R`); and
  (ii) narrower than the **literature-maximal** form (class-number-1 + per-prime
      squarefree image vs. the reduction-theoretic per-prime statement with no global
      hypothesis).
Number of weakening opportunities found: 3 (rows 1–3: drop class-number-1 → arbitrary number field; the `R = 𝓞 K` specialization is subsumed by the PID parent; the bespoke squarefree hypothesis → local residue-char condition).
Proposed restatement (target — see Phase 7): **ship the parent PID theorem**
`lutz_nagell_integrality_pid` (arbitrary char-0 PID `R`), from which this number-field
corollary is a one-line specialization; and target the **reduction-theoretic Dedekind
form** as the eventual maximally-general mathlib statement.
Cost of restatement: **CHEAP for the PID parent** (it already exists, sorry-free, and
this decl is literally its instantiation); **EXPENSIVE** for the reduction-theoretic
Dedekind form (needs EC-reduction + formal-group infrastructure mathlib lacks — see the
parent's report). EXPENSIVE does not downgrade the verdict.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let K be a foo" → typeclasses? | already done | uses `[NumberField K]`, `[IsPrincipalIdealRing (𝓞 K)]` — fully typeclass-based | — |
| 2 | sequences/metric → filters/topological? | partial (inherited) | the maximally-general proof is `𝔭`-adic / reduction-map — a `Valued`/reduction formulation per prime (see parent report) | mathlib valuation / local-field / formal-group API (once it exists) |
| 3 | construct → universal property? | no | a divisibility/integrality theorem; nothing to characterise universally | — |
| 4 | set+closure → bundled substructure? | no | conclusion is about coordinates of a single point | — |
| 5 | field-specific → weaker typeclass? | **yes** | class-number-1 `𝓞 K` → arbitrary `𝓞 K` (Dedekind) → DVR-per-prime; and `𝓞 K` → arbitrary char-0 PID is *already* the parent | full Dedekind / number-field / local-field torsion API |
| 6 | 1-categorical → higher-categorical? | no | arithmetic statement; no categorification | — |
| 7 | concrete index (ℤ) → general structure? | **yes** | the whole point: ℤ → PID (parent, done) → `𝓞 K`-class-no-1 (this decl) is a *re-narrowing back down* from the PID parent; the genuine idiom step is PID → Dedekind/local | unifies number-field & local-field developments |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — the reduction-map / formal-group (per-prime,
Dedekind/DVR) formulation, identical to the parent's Phase-4c target. Relative to *this*
declaration the dominant moves are simpler still:
  - This corollary **re-narrows** the parent's arbitrary char-0 PID `R` back to the
    single case `R = 𝓞 K`. The parent is already the more general object inside the
    project, so the immediate "generalise-first" target is just **the parent**.
  - Beyond that, the genuine modernisation (PID → Dedekind / reduction-theoretic) is the
    parent's modernisation, inherited here. Real improvement: removes the global
    class-number-1 / PID crutch that Silverman VIII.7.1 does not need.
  - Mathlib downstream: torsion-injection `E(K)_tor ↪ Ẽ(k_𝔭)`; uniform PID / number-field
    / local-field corollaries; classical ℚ Nagell–Lutz as a one-liner.

(Phase 4.5 diamond/defeq risk: **n/a** — declaration kind is `theorem`, not `def`/`class`/`instance`. No new definitional equalities or instances introduced.)

---

### Mathlib search-status: `LutzNagell.NumberField.lutz_nagell_number_field`

[A] Lean-Finder       n/a — MCP/index tool not exposed in this environment
[B] Loogle            n/a — MCP/index tool not exposed in this environment
[C] LeanSearch        n/a — MCP/index tool not exposed in this environment
[D] Grep mathlib src  `nagell`, `lutz`, `lutz_nagell`, `Nagell` over **all** `Mathlib/` — **0 hits** (no `nagell`/`lutz` decl or even string anywhere in mathlib). `IsOfFinAddOrder`/`addOrderOf` over `Mathlib/AlgebraicGeometry/EllipticCurve/` — **0 hits** (no torsion-order result on EC points). `torsion`/`integ` over `Mathlib/NumberTheory/` — hits are all **unit-torsion** (`NumberField/Units`, `FundamentalCone`, `Ideal/Basic`), unrelated to EC points. `IsLocalization.IsInteger` over `EllipticCurve/` — **0 hits**.
[E] Name pattern      `NumberField` ∩ `EllipticCurve/` — the **only** crossref is `EllipticCurve/LFunction.lean` (L-functions, unrelated to torsion integrality). No integrality-of-torsion decl exists.

Searched for both:
  - the user's current form (class-number-1 `𝓞 K`, general Weierstrass, torsion integrality) — **absent**.
  - the literature-maximal reduction form (torsion integral at good-reduction primes) — also **absent**; mathlib has the `AddCommGroup` on `W.Point` and the division/torsion *polynomials*, but no reduction map for elliptic curves and no torsion-integrality theorem in any form.

Concluded: **not in mathlib** (mathlib source exhausted for both forms; the dedicated
index tools are not exposed here, but the source grep over the relevant trees is
authoritative for *existence*, and the two sibling `/mathlibable` reports reach the same
conclusion independently). Mathlib has only the group structure + division-polynomial
machinery — the building blocks the project forks/extends, not the result.

---

### Call sites — `LutzNagell.NumberField.lutz_nagell_number_field`

Internal use count (within the project, excluding the declaring file `PIDMain.lean`): **0**
External-to-file callers: **0** distinct files. (Verified: `grep -rn "lutz_nagell_number_field\b" projects/ --include="*.lean" | grep -v PIDMain.lean` returns nothing.)

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | `lutz_nagell_number_field` is a top-level *presentation* corollary; nothing downstream consumes it. |

Inline-derivation grep (was the equivalent re-derived elsewhere without this decl?):
  - The mathematical workhorse is the **parent** `PID.lutz_nagell_integrality_pid`
    (`K=2` internal uses per `lutz_nagell_integrality_pid.md`: a recursive call at
    `PIDMain.lean:380` and *this very corollary* at `PIDMain.lean:509`). This corollary
    itself is re-derivation-free but also consumer-free.

Interpretation: `K=0` consumers for a **glue/wrapper theorem** (one-term body
delegating to the parent) is the textbook NO-leaning signal *for the wrapper as a
standalone unit* — it confirms the contribution-worthy object is the parent PID
theorem, with this corollary shipped alongside as the named number-field face. It is
**not** dead code (it is a deliberate `## Main results` presentation statement), but it
carries no independent weight.

---

### Composition check (Phase 6)

Can `lutz_nagell_number_field` be derived in ≤3 chained calls?

Attempt 1: from **mathlib** primitives.
  - Mathlib decls available: none — Phase 5 found no torsion-integrality and no
    reduction map for EC. **Fails.**

Attempt 2: from the **project's own** parent in ≤1 call.
  - `PID.lutz_nagell_integrality_pid W hpt htor hsf_all` — this is **exactly** the body
    (line 509). A single term application, with `R := 𝓞 K` supplied by typeclass
    inference (`𝓞 K` is a char-0 PID; `K = Frac(𝓞 K)`). **Succeeds in 1 call.**

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib has nothing to chain), but it **IS
a 1-call composition of the project's own parent theorem**. This is the defining
property of the declaration: it is the parent re-exported under the number-field
typeclasses, not an independent result. For mathlib-contribution purposes the right
unit is therefore the **parent** (`lutz_nagell_integrality_pid`), with this corollary
as a trivial specialization shipped in the same PR.

---

## Verdict: `LutzNagell.NumberField.lutz_nagell_number_field`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz over a number field of class number 1 is an *active 2025 research frontier* (arXiv:2509.07524), with the class-number-1 (= PID `𝓞 K`) hypothesis essential to it. The *maximally-general* standard form is reduction-theoretic (Silverman AEC VIII.7.1) and needs **no** class-number-1 / PID hypothesis. ≥4 channels concur (ChatGPT MCP down, compensated).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** on two axes — narrower than its own project parent (`R := 𝓞 K` specializes the parent's arbitrary char-0 PID `R`) *and* narrower than the literature-maximal reduction form (class-number-1 vs. per-prime residue-char). 3 weakening opportunities.
- Mathlib search (Phase 5): **not in mathlib** under either form — zero `nagell`/`lutz` decls, no EC torsion-integrality, no reduction map; only the EDS / division-polynomial building blocks the project forks.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib**, but a **1-call composition of the project's own parent** (`= the body`).

**Rationale:**

Mathlib genuinely lacks any Nagell–Lutz statement — a grep across all of `Mathlib/`
finds neither the string "nagell"/"lutz" nor any integrality-of-torsion result for
elliptic curves (only the `AddCommGroup` on points and the division/torsion
*polynomials*). So this is a real gap, not a duplicate: it is **not**
`NO-mathlib-has-it`. And because the proof chain bottoms out in an original multi-file
PID development (not mathlib primitives), it is **not** `NO-composable-from-mathlib`
in the skill's sense (the skill's NO-composable bucket is about composing *mathlib's*
primitives — here the only ≤1-call composition is from the *project's own* parent).

It is nevertheless **not** `YES-add-as-is`, for two independent reasons, either of
which is decisive under the skill's gate. **First**, Phase 4b is STRICTLY NARROWER:
this declaration is a typeclass specialization (`R := 𝓞 K`) of the project's *own* more
general parent `lutz_nagell_integrality_pid`, which is stated for an arbitrary char-0
PID and whose body this corollary reproduces in one term. The mathlib unit should be
the parent, with the number-field face as a one-line corollary shipped in the same PR —
not the corollary in isolation. **Second**, the class-number-1 hypothesis
`IsPrincipalIdealRing (𝓞 K)` is itself a narrowing of the literature-maximal,
reduction-theoretic Nagell–Lutz (Silverman VIII.7.1), which is local at each prime and
needs no global PID; the number-field-with-arbitrary-class-number case is, per
arXiv:2509.07524, still research-level. A STRICTLY-NARROWER Phase-4b verdict forces
`YES-but-generalise-first`, not `YES-add-as-is`.

This corollary's `K=0` consumers and one-term body confirm the framing: it is a
*presentation* wrapper, mathematically inseparable from its parent. The recommendation
is therefore to upstream the **parent PID theorem** (already sorry-free, the real
content), bundle this number-field corollary in the *same* PR as its named
class-number-1 face, and — separately, as the genuinely maximal mathlib target — pursue
the reduction-theoretic Dedekind form once mathlib acquires EC-reduction / formal-group
infrastructure. Note this verdict, its parent's (`lutz_nagell_integrality_pid.md`), and
the short-form headline's (`lutz_nagell.md`) all converge on the same conclusion: the
contribution is the **general theorem**, and these specializations ride along.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b — the user's form (class-number-1 `𝓞 K`, per-prime squarefree image) is strictly narrower than both (a) its own project parent (arbitrary char-0 PID) and (b) the literature-maximal reduction-theoretic Dedekind/DVR form.
  - **MODERN-IDIOM (inherited):** Phase 4c — the reduction-map / formal-group per-prime formulation removes the global class-number-1 / PID crutch; identical to the parent's modernisation target.

**Proposed restatement** (the unit to upstream — already proved sorry-free in the project):
```lean
-- THE contribution: the general char-0-PID Nagell–Lutz (project's own parent, used internally).
theorem lutz_nagell_integrality_pid
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K}
    (hpt : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) →
      Squarefree (p : R)) :
    ((IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧ (IsFractionRing.den R x : R) ∣ (4 : R)) := …
-- THEN this number-field corollary (the existing one-liner) ships alongside, unchanged:
--   lutz_nagell_number_field K W hpt htor hsf_all := lutz_nagell_integrality_pid W hpt htor hsf_all
```
Eventual maximally-general mathlib target (EXPENSIVE — needs infrastructure mathlib
lacks): the reduction-theoretic Dedekind/DVR form (see `lutz_nagell_integrality_pid.md`
Phase 7), from which the class-number-1 number-field corollary is a specialization.

Estimated cost of regeneralisation: **CHEAP** to surface the PID parent as the unit
(it already exists; this corollary is its one-line instantiation). **EXPENSIVE** only
for the reduction-theoretic Dedekind form — which does *not* gate this verdict.

Mathlib downstream this enables:
  - The parent applies to **any** char-0 PID — `ℤ` (classical Nagell–Lutz), `𝓞 K` class-number-1 (this corollary), and any other PID — from one statement.
  - Foundational for a future `E(K)_tors` finiteness/computation API (torsion as a finite checkable set), and for the eventual reduction-theoretic / number-field-of-arbitrary-class-number generalizations (arXiv:2509.07524 direction).

**Next action:** run `/generalise LutzNagell.NumberField.lutz_nagell_number_field` —
which will immediately surface that the broader project unit is the parent
`lutz_nagell_integrality_pid` (and, beyond it, the reduction-theoretic Dedekind form).
Upstream the **parent** PID theorem to `Mathlib/NumberTheory/EllipticCurve/` (new file,
e.g. `NagellLutz.lean`), bundling this number-field corollary and the short-form
`lutz_nagell` in the **same** PR as named faces. Keep all three in the project as-is in
the meantime — they are correct and useful; the generalisation is purely an
upstreaming-grain concern, not a project defect. Pre-PR: `/cleanup` the `General*` /
`PID*` chain (the real content), pick a reviewer from recent
`Mathlib/AlgebraicGeometry/EllipticCurve/` commits (division-polynomial / EDS authors).

---

## Next step

Run `/generalise LutzNagell.NumberField.lutz_nagell_number_field`. The mathlib
contribution is the **parent** `lutz_nagell_integrality_pid` (general char-0 PID;
already sorry-free), with this class-number-1 number-field corollary shipped alongside
as its named face — not as a standalone unit. Target the reduction-theoretic Dedekind
form as the eventual maximally-general statement, gated on mathlib first acquiring
elliptic-curve reduction + formal-group torsion infrastructure.
