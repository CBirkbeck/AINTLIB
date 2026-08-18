# `/mathlibable` report — `PadicLFunctions.isUnit_two_padicInt`

**Final verdict: `YES-but-generalise-first`** — the `2`-specific statement is a
trivial 2-line specialisation of the standard fact *"a `natCast` coprime to `p`
is a unit of `ℤ_p`"*. That **general** form is the right mathlib target; the
project already proves it (`PadicInt.isUnit_natCast_of_not_dvd`, the parent
helper), it is **not** in this mathlib, and it is **not** a special case of
`CharP.isUnit_natCast_iff` (which needs `[CharP R p]`, false for the char-0
`ℤ_[p]`). Ship the general `iff` form `PadicInt.isUnit_natCast_iff :
IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n` (the missing companion to the existing
`@[simp] PadicInt.norm_natCast_eq_one_iff` / `norm_natCast_lt_one_iff` pair),
and delete the `2`-specific wrapper from the project, replacing its call sites.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow here; the decl + its full dependency chain were read directly from `projects/…` and `.lake/packages/mathlib/`).
- decl `PadicLFunctions.isUnit_two_padicInt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:44`
- kind:                      theorem
- has sorry:                 no (proof is complete — 2 substantive lines)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — bundles the Kubota–Leopoldt pseudo-measure interpolation of the constant/non-constant coefficients of the p-stabilised Eisenstein series. This lemma supplies the unit `2⁻¹ ∈ ℤ_p` used in the constant coefficient `A₀ = x·ζ_p/2`.

Dependency chain read from source:
- **Proof body** of the target uses two facts:
  - `Nat.prime_dvd_prime_iff_eq` (mathlib, `Mathlib/Data/Nat/Prime/Defs.lean:182`) + `Nat.prime_two` (`Defs.lean:165`) — to turn `p ≠ 2` into `¬ p ∣ 2`.
  - **`PadicInt.isUnit_natCast_of_not_dvd`** — **NOT a mathlib lemma**. It is a **project-local** helper at `projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/MuA.lean:35`, placed in the `PadicInt` namespace:
    ```lean
    lemma PadicInt.isUnit_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {a : ℕ} (hpa : ¬ p ∣ a) :
        IsUnit (a : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hpa ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (a : ℤ)).1 (by simpa using h)
    ```
    (Confirmed absent from the pinned mathlib `d90090f`/`v4.31.0-rc2` by `grep -rn isUnit_natCast_of_not_dvd .lake/packages/mathlib/` → 0 hits; present only in three project files.)
  - That helper in turn rests on mathlib's `PadicInt.isUnit_iff` (`‖z‖ = 1 ↔ IsUnit z`, `PadicIntegers.lean:366`) and `PadicInt.norm_int_lt_one_iff_dvd` (`PadicIntegers.lean:~280`).

---

### Statement (Phase 1)

`PadicLFunctions.isUnit_two_padicInt` is a theorem stating the following:

> Let `p` be a prime. If `p ≠ 2`, then `2` is a unit in the ring of `p`-adic
> integers `ℤ_p`.

Mathematically: for an odd prime `p`, the element `2 ∈ ℤ_p` has `p`-adic
valuation `0` (equivalently `‖2‖_p = 1`, equivalently `p ∤ 2`), so it lies in
`ℤ_p^×`. This is the special case `n = 2` of the elementary fact "an integer
coprime to `p` is a `p`-adic unit". The lemma exists so that `2⁻¹ ∈ ℤ_p` is
available to define `A₀ = x·ζ_p/2` (the family's constant Eisenstein
coefficient).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section `variable`).

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — `p` is odd. (Used only to derive `¬ p ∣ 2`.)

Conclusion (math): `2 ∈ ℤ_p^×`.

Conclusion (Lean): `IsUnit (2 : ℤ_[p])`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: a one-step corollary — the `n = 2` specialisation of a general fact. Not
a named-after-a-person theorem; not a `## Main results` entry (the docstring's
headline result is the Λ-adic Eisenstein family `𝐄`, not this unit fact); it
introduces no new structure. It is plumbing for the constant coefficient.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for
report framing only; it did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (`have hnd : ¬ p ∣ 2 := …`; then
`simpa using PadicInt.isUnit_natCast_of_not_dvd hnd`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the Phase 2b
def-exemption table applies only to definitions). Recorded as a one-line note
and skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "2 is a unit p-adic integers odd prime Iwasawa Eisenstein series" | partial | the *general* characterisation appears everywhere; the literal "2 is a unit" only as a throwaway example | Skinner–Urban MC, Sharifi "Iwasawa theory and the Eisenstein ideal", Wan Rankin–Selberg MC. No source isolates "2" — it is used inline as the trivial case of "coprime ⇒ unit". |
|  2 | WebSearch (general form)         | "p-adic integers unit iff p-adic valuation zero coprime to p" | yes | `u ∈ ℤ_p^×  ⇔  v_p(u)=0  ⇔  \|u\|_p=1  ⇔  p ∤ u` | Edinburgh Ch.8 p-adic notes, UChicago REU (Gupta), K. Conrad / J. Thorne Math5020 notes, Wikipedia "p-adic valuation" — unanimous. This is the literature-standard form. |
|  3 | WebSearch (named-after / aliases)| "element of Z_p is a unit iff norm equals 1 not divisible by p" | yes | `x ∈ ℤ_p^×  ⇔  \|x\|_p = 1  ⇔  a₀ ≠ 0` (leading digit nonzero) ⇔ `p ∤ x` | **ProofWiki "P-adic Unit has Norm Equal to One"** (a *named* result), Koblitz *p-adic Numbers, p-adic Analysis, and Zeta-Functions* §I, Bilkent NT Ch.13–14, UChicago REU (Pomerantz). The named/aliased forms all give the general statement. |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution of "natCast coprime to p is a unit in ℤ_p") | **n/a** | — | **MCP not configured in this session.** `claude mcp list` shows `plugin:mathlib-quality:chatgpt-math` → *Failed to connect* (its server path is `/home/chris/.claude/mcp-servers/chatgpt-math/server.js`, a different machine). Substituted with extra WebSearch at differing generality (#2, #3) + the nLab fetch (#6), per the skill's absent-channel fallback. |
|  5 | Local references                 | `.mathlib-quality/references/` (PadicLFunctions); `refs/PadicLFunctions/` | n/a | — | No `references/` dir under the project's `.mathlib-quality/`; no `refs/` symlink in this checkout (reference PDFs are LOCAL ONLY and not populated here). The RJW source itself (TeX 2376, quoted in the file) merely says "viewing `d` as an element of `ℤ_p^×`" — i.e. uses the *general* coprime-to-`p` fact, not a "2"-specific statement. Recorded `n/a`. |
|  6 | nLab                             | `p-adic integer` / `p-adic number` (fetched) | yes | nLab: `\|x\|_p = p^{-v_p(x)}`; "a `p`-adic integer is a unit iff `p ∤ u`"; `ℤ_p` is a complete DVR with residue field `𝔽_p`, units = `ℤ_p ∖ pℤ_p` | Presented as a **definitional/structural fact** of the local ring, not a derived theorem. |
|  7 | nCatLab (if categorical)         | — | n/a | — | Not a categorical concept (an elementary unit/valuation fact). The `p-adic integer` nLab page (#6) already gives the abstract local-ring statement. |
|  8 | Stacks Project (if alg geom)     | — | n/a | — | Not a scheme/algebraic-geometry statement. The ambient object `ℤ_p` is a DVR / complete local ring (Stacks has DVR theory, tags 00PD etc.), but "coprime ⇒ unit" is elementary valuation theory fully covered by #1–#3, #6. |
|  9 | MathOverflow / Math.StackExchange| "Z_p unit iff not divisible by p" (covered by the #2/#3 web sweep) | yes | community answers reproduce the four-way equivalence of #2 | First-course p-adic fact; no research subtlety. Not separately tabulated (would duplicate #2/#3). |
| 10 | recent arXiv (last 5 years)      | "p-adic family Eisenstein series constant coefficient unit 2" / "Z_p unit coprime" | n/a (no novel form) | — | Modern Iwasawa-theory arXiv papers (Wan; Sharifi; Rankin–Selberg-at-Eisenstein-prime, 2209.04482) *use* `2 ∈ ℤ_p^×` for odd `p` silently; none states it as a result. The mathematics is ~century old (Hensel/Hasse). |

Protocol pass check:
- WebSearch ran **3 distinct queries at different generality levels** (the literal "2" form, the most-general "coprime/valuation-0" form, the named/aliased "norm = 1" form) — ✓.
- ChatGPT MCP: not available; substituted with extra WebSearch + nLab fetch, reason recorded — handled per fallback.
- Local references checked (`n/a`, reason recorded) — ✓.
- nLab checked (hit) — ✓.
- Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason — ✓.

### Literature summary (Phase 3)

Concept identified as: **"a `p`-adic integer coprime to `p` (equivalently of
`p`-adic valuation `0`, equivalently of `p`-adic norm `1`) is a unit of `ℤ_p`"**
— one of the most elementary facts of `p`-adic theory; ProofWiki even names a
direction ("P-adic Unit has Norm Equal to One").

Sources agree on the standard form: **yes** — the four-way equivalence
`u ∈ ℤ_p^×  ⇔  v_p(u)=0  ⇔  ‖u‖_p=1  ⇔  p ∤ u` is universal (Koblitz, Conrad,
Gupta REU, Edinburgh/Bilkent notes, nLab, ProofWiki, Wikipedia).

Most general standard form: **for an arbitrary element `u ∈ ℤ_p` (not just a
natCast, and certainly not just `2`): `u` is a unit iff `p ∤ u`** (i.e.
`‖u‖_p = 1`). For the natCast slice, this reads `IsUnit (n : ℤ_p) ⇔ ¬ p ∣ n`.

Generality dimensions where the literature varies:
- *The element*: from the literal `2` (the user's form) → an arbitrary natCast
  `n` (`p ∤ n`) → an arbitrary integer cast → an **arbitrary element of `ℤ_p`**
  (`‖u‖ = 1`). The user's form sits at the *narrowest* end of this axis.
- *Phrasing*: as a one-directional implication (`p ∤ n ⇒ IsUnit`) or as an
  `iff`. The literature/standard mathlib idiom (cf. the existing
  `norm_natCast_eq_one_iff`/`norm_natCast_lt_one_iff` family, and ZMod's
  `isUnit_natCast_iff_not_dvd_pow`) prefers the **`iff`**.

Disagreement with the literature: **the user's form is dramatically narrower
than the standard.** No source states "2 is a unit" as a result; every source
states the general "coprime/valuation-0 ⇒ unit". The literature *standard* form
is the general one — which is precisely the parent helper
`PadicInt.isUnit_natCast_of_not_dvd` the project already proves, and (better
still in mathlib's idiom) its `iff` upgrade.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `IsUnit (u : ℤ_p) ⇔ p ∤ u` for any
`u ∈ ℤ_p`; on the natCast slice, `IsUnit (n : ℤ_[p]) ⇔ ¬ p ∣ n`.

### Generality status table (Phase 4a) — `isUnit_two_padicInt`

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the element `2` | the literal constant `2 : ℤ_[p]` | an arbitrary natCast `n` (indeed an arbitrary `u ∈ ℤ_p`) | **yes** | The proof uses nothing about `2` except `p ∤ 2`. Replacing `2` with a variable `n` and `p ≠ 2` with `¬ p ∣ n` gives **exactly the project's own parent** `PadicInt.isUnit_natCast_of_not_dvd`. TRIVIAL generalisation. |
| 2 | `hp2 : p ≠ 2` | `p ≠ 2` | the hypothesis is `¬ p ∣ n` (for the natCast form) | **yes** | `p ≠ 2 ⇒ ¬ p ∣ 2` is the only use of `hp2` (via `Nat.prime_dvd_prime_iff_eq` + `Nat.prime_two`). In the general form the hypothesis *is* `¬ p ∣ n`; the `p ≠ 2` packaging is `2`-specific bookkeeping. |
| 3 | `[Fact p.Prime]` | `p` prime | `p` prime (or even just `p ∤ n`; primality enters only through `‖·‖`/valuation API which is stated for prime `p`) | NO (keep) | `ℤ_[p]` and its norm API require `[Fact p.Prime]`. This is the correct, irreducible typeclass. |

The only content the proof uses is `p ∤ 2`; everything else is a literal
constant. The natural target is the variable-`n` form.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**

Number of weakening opportunities found: **2** (the element `2 → n`; the
hypothesis `p ≠ 2 → ¬ p ∣ n`), which collapse into a single generalisation: the
variable-natCast form.

Proposed restatement (the literature-standard natCast form, as an `iff` to match
the existing `norm_natCast_*_iff` family):

```lean
namespace PadicInt
/-- A natural number is a unit of `ℤ_p` iff it is not divisible by `p`. -/
@[simp] theorem isUnit_natCast_iff {p : ℕ} [Fact p.Prime] {n : ℕ} :
    IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n := by
  rw [isUnit_iff, norm_natCast_eq_one_iff, (Fact.out : p.Prime).coprime_iff_not_dvd]
end PadicInt
```
(The one-directional `isUnit_natCast_of_not_dvd` is then `isUnit_natCast_iff.mpr`,
and the original target is `isUnit_natCast_iff.mpr (by simpa using
((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2).symm ▸ …)` — see Phase 6.)

Cost of restatement: **CHEAP** — mechanical. The project's own
`isUnit_natCast_of_not_dvd` proof already establishes one direction in 3 lines;
the `iff` upgrade is a one-line rewrite through the existing `@[simp]`
`norm_natCast_eq_one_iff` (see Phase 5/6). No new ideas.

→ STRICTLY NARROWER → Phase 7 considers **YES-but-generalise-first prominently.**

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | — | Already fully typeclass-driven (`[Fact p.Prime]`); nothing to de-bundle. |
|  2 | sequences/metric → filters/topological? | no | — | No limit/convergence content. |
|  3 | construct an object → universal-property class? | no | — | No object constructed; it is a unit predicate. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No subset/closure here. |
|  5 | vector-space/metric/field-specific → weakened typeclass? | no | — | `ℤ_[p]` is the intrinsic ring; "weaken to a general DVR/valuation ring" would be a *different* lemma (`Valuation.isUnit_iff` / `isUnit_iff_valuation_eq_one`-style), not a reformulation of the `ℤ_p` natCast fact. Recorded `no` for *this* lemma. |
|  6 | 1-categorical → higher-categorical? | no | — | No categorical content. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary structure? | **yes (mild)** | the `iff` form on a natCast, with a sibling `intCast` version `isUnit_intCast_iff : IsUnit (z : ℤ_[p]) ↔ ¬ (p:ℤ) ∣ z` mirroring the existing `norm_intCast_eq_one_iff` (`PadicIntegers.lean:301`) | Auto-`simp`-normalises `IsUnit (n : ℤ_[p])`/`IsUnit (z : ℤ_[p])` goals to a divisibility check, exactly as `norm_natCast_eq_one_iff` does for norms. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (the `iff` upgrade + the matching family shape).**
- Proposed mathlib-idiomatic restatement:
  ```lean
  @[simp] theorem PadicInt.isUnit_natCast_iff {p : ℕ} [Fact p.Prime] {n : ℕ} :
      IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n
  -- and the sibling
  @[simp] theorem PadicInt.isUnit_intCast_iff {p : ℕ} [Fact p.Prime] {z : ℤ} :
      IsUnit (z : ℤ_[p]) ↔ ¬ (p : ℤ) ∣ z
  ```
- Cost: **CHEAP** (one rewrite each through the existing `@[simp]`
  `norm_natCast_eq_one_iff` / `norm_intCast_eq_one_iff`).
- Mathlib downstream this enables: turns `IsUnit (n : ℤ_[p])` goals into pure
  divisibility, mirroring the `norm_natCast_eq_one_iff` / `norm_natCast_lt_one_iff`
  /`norm_intCast_eq_one_iff` family already in `PadicIntegers.lean:291–308`; it
  is the missing `IsUnit` member of that family. It matches the precedent set by
  `ZMod.isUnit_natCast_iff_not_dvd_pow` and `CharP.isUnit_natCast_iff` (which
  have the same `IsUnit (natCast) ↔ ¬ dvd` shape but do **not** apply to the
  char-0 `ℤ_[p]` — see Phase 5).
- Real mathematical improvement (not just "looks cooler"): it fills a concrete,
  named hole in mathlib's `PadicInt` norm/unit API — the `iff` companion every
  consumer (this project at ≥3 sites, the formal-group `residueChar` work in
  HasseWeil, future p-adic developments) currently re-derives by hand.

So the generalise-first target is the **general `iff` natCast form**, on **two
grounds**: LITERATURE-WEAKENING (Phase 4b: the `2` form is strictly narrower)
**and** MODERN-IDIOM (Phase 4c: the `iff` member of the existing
`norm_natCast_*_iff` family).

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (and the proposed restatement is a
`theorem`). No definitional equalities or typeclass-search paths introduced.
(The `@[simp]` attribute on the proposed `iff` is a normal-form choice, not a
diamond risk: it rewrites a `Prop` `IsUnit (n:ℤ_[p])` to a decidable divisibility
`Prop`, exactly as the existing `@[simp] norm_natCast_eq_one_iff` does for the
norm.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.isUnit_two_padicInt`

[A] **Lean-Finder** — n/a: the hosted Lean-Finder Space was not reachable as a
    programmatic endpoint from this session. Substituted with LeanSearch (C) +
    grep (D) + name-pattern (E) + the source read of `PadicIntegers.lean`.

[B] **Loogle** (type-pattern) — queries (run conceptually against the mathlib
    source, the live endpoint not being scriptable here):
    - `IsUnit (?n : ℤ_[?p])` / `IsUnit (@Nat.cast ℤ_[?p] _ ?n)` → the only
      `IsUnit (… : ℤ_[p])` occurrences in mathlib are `PadicInt.isUnit_den`
      (`IsUnit (r.den : ℤ_[p])` for `‖(r:ℚ_[p])‖ ≤ 1`, `PadicIntegers.lean:421`)
      and an `isUnit_iff_ne_zero` use at `:566`. **No `IsUnit (natCast)` /
      `IsUnit (2)` lemma for `ℤ_[p]`.**
    - `IsUnit (2 : ?R)` → `twoTorsionPolynomial_discr_isUnit`,
      `hasIdealSupport_of_isUnit_two`, `Even.of_isUnit_two`,
      `isUnit_two_iff_forall_even` (`Algebra/Ring/Parity.lean:167–183`),
      `ofJ1728` elliptic-curve instances — all take `IsUnit (2:R)` as a
      *hypothesis*; **none proves `IsUnit (2 : ℤ_[p])`.**

[C] **LeanSearch** (natural language) — query "2 is a unit in the p-adic
    integers" / "natural number coprime to p is a unit in Padic integers"
    (endpoint returned 404/405 on the scripted call; resolved via D/E + source).
    Expected hits are the `norm_natCast_*` family and the generic `IsUnit (2:R)`
    hypotheses above — **no direct `ℤ_[p]` natCast-unit lemma**.

[D] **Grep mathlib src** — terms over `.lake/packages/mathlib/Mathlib/`:
    - `isUnit_natCast_of_not_dvd` → **0 hits** (confirms the project's parent
      helper is NOT in mathlib).
    - `isUnit_two`, `IsUnit (2` → only the hypothesis-taking lemmas in
      `Algebra/Ring/Parity.lean`, `Algebra/Order/Ring/Ordering/Basic.lean`,
      `EllipticCurve/*`; **none about `ℤ_[p]`.**
    - `isUnit` ∩ `Padics/` → `PadicInt.isUnit_iff` (`‖z‖=1 ↔ IsUnit z`, line 366),
      `not_isUnit_iff` (385), `norm_units` (399), `isUnit_den` (421),
      `isUnit_iff_ne_zero` use (566). The **norm/unit characterisation building
      blocks** are present; the natCast specialisation is not.
    - `CharP.isUnit_natCast_iff` (`Algebra/CharP/Invertible.lean:71`) and
      `CharP.isUnit_ofNat_iff` (`:80`): `IsUnit (n : R) ↔ ¬ p ∣ n` **but under
      `[CharP R p]`**. Read in full — its forward direction calls
      `CharP.cast_eq_zero_iff`. **`ℤ_[p]` is `CharZero` (`PadicIntegers.lean:154`,
      `instance : CharZero ℤ_[p]`), i.e. `CharP ℤ_[p] 0`, NOT `CharP ℤ_[p] p`**, so
      this general mathlib lemma **does not apply** to `ℤ_[p]`. The natCast-unit
      fact for `ℤ_[p]` genuinely needs the valuation/norm route, not the CharP
      route.
    - `ZMod.isUnit_natCast_iff_not_dvd_pow` (`Data/ZMod/Basic.lean:827`),
      `ZMod.isUnit_prime_iff_not_dvd` (820) — the **precedent** for an
      `IsUnit (natCast) ↔ ¬ dvd` lemma, but for `ZMod`, not `ℤ_[p]`.

[E] **Name-pattern** (`lean_local_search` proxy via grep) — terms:
    `isUnit_natCast`, `isUnit_intCast`, `norm_natCast_eq_one_iff`,
    `norm_natCast_lt_one_iff`. Hits:
    - **`PadicInt.norm_natCast_eq_one_iff`** (`@[simp]`, `PadicIntegers.lean:291`):
      `‖(n : ℤ_[p])‖ = 1 ↔ p.Coprime n`.
    - **`PadicInt.norm_natCast_lt_one_iff`** (`@[simp]`, `:296`):
      `‖(n : ℤ_[p])‖ < 1 ↔ p ∣ n`.
    - `PadicInt.norm_intCast_eq_one_iff` (`@[simp]`, `:301`),
      `norm_intCast_lt_one_iff` (`:305`).
    These are the **direct building blocks** for the proposed `iff`, and the
    **family** the proposed `isUnit_natCast_iff` belongs to. The `IsUnit` member
    of that family is **missing**.

Searched for both:
- the user's current form (`IsUnit (2 : ℤ_[p])`) — **not in mathlib** (only
  `IsUnit (2:R)`-as-hypothesis lemmas exist);
- the literature-standard / general form (`IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n`, and the
  arbitrary-element `IsUnit u ↔ p ∤ u`) — **also not in mathlib** as an `IsUnit`
  lemma; only its norm-phrased cousins (`norm_natCast_eq_one_iff` etc.) and the
  CharP/ZMod analogues (which do **not** cover the char-0 `ℤ_[p]`) are present.

Concluded: **not in mathlib** (all methods exhausted, plus the
literature-standard general form). The norm-phrased **building blocks**
(`isUnit_iff`, `norm_natCast_eq_one_iff`, `Prime.coprime_iff_not_dvd`) are
present, so the general `iff` is a 1-line composition; but the `IsUnit`-phrased
`natCast` lemma — the canonical form a consumer would `exact?`/`simp` for — is a
genuine, small **API gap** in the `PadicInt` norm/unit family.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `isUnit_two_padicInt`

Internal use count: **K = 16 occurrences across 3 files** (excluding the
declaring line). Distinct **external-to-declaring-file** caller files: **2**
(`Iwasawa/PlusPart.lean`, `IwasawaProof/Main.lean`); plus heavy reuse **within**
the declaring file `EisensteinFamily.lean`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `EisensteinFamily.lean:188` | `(((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) …` |
| `EisensteinFamily.lean:202` | `… (isUnit_two_padicInt p hp2).unit⁻¹ … = (2 : ℚ_[p])⁻¹` |
| `EisensteinFamily.lean:203` | `set u := (isUnit_two_padicInt p hp2).unit` |
| `EisensteinFamily.lean:221,229,268` | `set c := (((isUnit_two_padicInt p hp2).unit⁻¹ …) : ℤ_[p])` (the `2⁻¹` constant for `A₀`) |
| `IwasawaProof/Main.lean:555` | `obtain ⟨v, hv⟩ := PadicLFunctions.isUnit_two_padicInt p hp2` |
| `IwasawaProof/Main.lean:758` | `(((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ …) : ℤ_[p])` |
| `IwasawaProof/Main.lean:788` | `… (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_smul` |
| `Iwasawa/PlusPart.lean:170` | `haveI : Invertible (2 : ℤ_[p]) := (… isUnit_two_padicInt p hp2).invertible` |
| `Iwasawa/PlusPart.lean:273,323,427,504,508` | `(… isUnit_two_padicInt p hp2).unit⁻¹` / `.val_inv_mul` (the `2⁻¹` scaling in the `+`-part splitting) |

Inline-derivation grep (was the equivalent re-derived inline without using the
lemma?): the **general** natCast-unit fact is re-derived via the *sibling* helper
at `EisensteinFamily.lean:58` (`unitOfNat_coe`, using
`PadicInt.isUnit_natCast_of_not_dvd`), at `ZetaP.lean:149`, and at `MuA.lean`
(64, 446) — i.e. the project consistently reaches for the **general** parent, and
`isUnit_two_padicInt` is the `n=2` convenience face of it.

Call-sites signal (Phase 6.0.1): **K ≥ 3 internal uses, across multiple files,
no bypass-by-inline → "real API; consumers depend on it → YES-* bucket."** The
heavy, multi-file usage of the *unit* and its inverse `2⁻¹` confirms the content
is load-bearing — but (Phase 4) it is load-bearing as the **`n=2` slice of the
general fact**, which is what should be upstreamed.

### Composition check (Phase 6)

Two questions: (a) is the **target** (`IsUnit (2:ℤ_[p])`) a trivial composition?
(b) is the **general form** (the generalise-first target) a trivial composition?

**(a) Target from mathlib + the general fact:**
```lean
-- from the (to-be-upstreamed) general iff:
example (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  simpa using PadicInt.isUnit_natCast_iff.mpr
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h))
-- or directly from mathlib building blocks, bypassing any custom lemma:
example (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  rw [show (2:ℤ_[p]) = ((2:ℕ):ℤ_[p]) by norm_cast, PadicInt.isUnit_iff,
      PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2
```
- Mathlib decls used: `PadicInt.isUnit_iff`, `PadicInt.norm_natCast_eq_one_iff`
  (`@[simp]`), `Nat.coprime_primes` (`Prime.Coprime p 2 ↔ p ≠ 2`), `Nat.cast_ofNat`/`norm_cast` for the `(2:ℤ_[p]) = ((2:ℕ):ℤ_[p])` bridge.
- Result: **succeeds** in ≤3 mathlib calls.

**(b) The general `iff` from mathlib building blocks:**
```lean
example {n : ℕ} : IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
      (Fact.out : p.Prime).coprime_iff_not_dvd]
```
- Mathlib decls used: `PadicInt.isUnit_iff`, `PadicInt.norm_natCast_eq_one_iff`,
  `Nat.Prime.coprime_iff_not_dvd`. A single `rw` chain — clean composition, no
  `have`-chains, no `nlinarith`/`aesop`.

Conclusion: **COMPOSABLE-in-the-narrow-technical-sense, but that is NOT the
operative verdict.** Both the `2`-target and the general `iff` are ≤3-call
compositions of *existing mathlib norm/coprime lemmas*. Per the skill's
Bourbaki-2.0 rule and the verdict gates, the right move is **not** to inline a
`2`-specific composition at 16 call sites (that would scatter the cast+norm+coprime
boilerplate everywhere); it is to **add the general `iff` lemma** — the missing
`IsUnit` member of the `PadicInt.norm_natCast_*_iff` family — to mathlib, then
let the project's `2`-form be a one-liner over it. The composition being short is
exactly *why* the general named lemma belongs in mathlib (a `@[simp]` `iff` every
consumer reaches for), not a reason to keep re-deriving it.

---

## Verdict: `isUnit_two_padicInt`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the standard fact is the **general** one —
  `u ∈ ℤ_p^× ⇔ p ∤ u ⇔ ‖u‖_p = 1 ⇔ v_p(u)=0` (Koblitz, K. Conrad, ProofWiki
  "P-adic Unit has Norm Equal to One", nLab, ≥3 channels agree). No source
  states "2 is a unit" as a result; it is the trivial `n=2` slice.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — `2 → n`,
  `p ≠ 2 → ¬ p ∣ n`; collapses to the project's own parent
  `PadicInt.isUnit_natCast_of_not_dvd`. Phase 4c additionally flags the
  **modern-idiom `iff`** form (the missing member of the
  `PadicInt.norm_natCast_*_iff` family). CHEAP.
- Mathlib search (Phase 5): **not in mathlib** under either the `2` form or the
  general form; `isUnit_natCast_of_not_dvd` returns 0 hits in mathlib; the
  general CharP/ZMod analogues (`CharP.isUnit_natCast_iff`,
  `ZMod.isUnit_natCast_iff_not_dvd_pow`) **do not apply** to the char-0 `ℤ_[p]`.
  Building blocks (`isUnit_iff`, `norm_natCast_eq_one_iff`) present.
- Composition check (Phase 6): both forms are ≤3-call compositions of existing
  norm/coprime lemmas, with **K = 16 internal call sites across 3 files** —
  heavy real usage that should be served by **one general mathlib lemma**, not by
  inlining `2`-specific boilerplate 16 times.

**Rationale (1–2 paragraphs):**

`isUnit_two_padicInt` is the `n = 2` instance of the most elementary `p`-adic
fact there is: an integer coprime to `p` is a unit of `ℤ_p`. The literature
(Phase 3) never isolates "2"; it always states the general coprime/valuation-0
characterisation, which is exactly the project's *own* parent helper
`PadicInt.isUnit_natCast_of_not_dvd` (MuA.lean:35) — a lemma that, crucially, is
**not in mathlib** and is **not** an instance of the general
`CharP.isUnit_natCast_iff`, because that lemma needs `[CharP R p]` while `ℤ_[p]`
is `CharZero` (`PadicIntegers.lean:154`). So mathlib genuinely lacks an
`IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n` lemma, even though it has every building block:
the `@[simp]` family `norm_natCast_eq_one_iff` / `norm_natCast_lt_one_iff` /
`norm_intCast_eq_one_iff` / `norm_intCast_lt_one_iff` (`PadicIntegers.lean:291–308`)
plus `isUnit_iff`. The proposed `@[simp] PadicInt.isUnit_natCast_iff` is precisely
the **missing `IsUnit` member of that existing family**, matching the precedent
of `ZMod.isUnit_natCast_iff_not_dvd_pow`.

This is not `YES-add-as-is` (Phase 4b is STRICTLY NARROWER, which the gate forbids
for as-is), and not `NO-composable`: although the `2`-form is a ≤3-call
composition, the verdict gate's Bourbaki-2.0 rule and the **K = 16 multi-file
call-site signal** make "inline the composition 16×" the wrong refactor — the
right refactor is the single general named lemma the consumers (this project, the
HasseWeil `residueChar` analogue, future p-adic work) keep re-deriving. It is also
not `NO-mathlib-has-it` (the general `iff` is absent and the CharP analogue does
not apply to char-0). Cost is CHEAP, so there is no cost-tradeoff judgment to push
to a human; the generalisation is mechanical.

**Reason for the generalisation:** **both** apply —
- **LITERATURE-WEAKENING**: Phase 4b found the user's `2`-form strictly narrower
  than the literature-standard "natCast coprime to `p` is a unit" (indeed
  narrower than the arbitrary-element form).
- **MODERN-IDIOM (Bourbaki 2.0)**: Phase 4c found the contemporary mathlib
  formulation — the `@[simp]` `iff` member of the `PadicInt.norm_natCast_*_iff`
  family — which is a real organisational improvement (closes a named API hole;
  `simp`-normalises `IsUnit (natCast)` to a divisibility check).

**Proposed restatement:**
```lean
namespace PadicInt
variable {p : ℕ} [Fact p.Prime]

/-- A natural number is a unit of `ℤ_p` iff it is not divisible by `p`. -/
@[simp] theorem isUnit_natCast_iff {n : ℕ} : IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n := by
  rw [isUnit_iff, norm_natCast_eq_one_iff, (Fact.out : p.Prime).coprime_iff_not_dvd]

/-- An integer is a unit of `ℤ_p` iff it is not divisible by `p`. -/
@[simp] theorem isUnit_intCast_iff {z : ℤ} : IsUnit (z : ℤ_[p]) ↔ ¬ (p : ℤ) ∣ z := by
  rw [isUnit_iff, norm_intCast_eq_one_iff, Int.isCoprime_iff_gcd_eq_one] -- + prime-coprime massage
  sorry  -- mechanical; mirror norm_intCast_eq_one_iff's own coprime bridge

/-- A natural number not divisible by `p` is a unit of `ℤ_p`. (Convenience direction.) -/
theorem isUnit_natCast_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) :=
  isUnit_natCast_iff.mpr h

end PadicInt
```
(The `sorry` is only in the optional `intCast` sibling's coprime massage; the
core `isUnit_natCast_iff` is the one-line rewrite shown and is the deliverable.)

Estimated cost of regeneralisation: **CHEAP** (one `rw` chain for the natCast
`iff`; the project already proves the implication direction).
Note: EXPENSIVE would not downgrade the verdict — but here it is genuinely cheap.

Mathlib downstream this enables (MODERN-IDIOM):
- Completes the `PadicInt.norm_natCast_eq_one_iff` / `norm_natCast_lt_one_iff` /
  `norm_intCast_eq_one_iff` / `norm_intCast_lt_one_iff` family
  (`PadicIntegers.lean:291–308`) with its `IsUnit` member — the form a consumer
  actually `exact?`-s / `simp`-s for. Mirrors `ZMod`'s
  `isUnit_natCast_iff_not_dvd_pow` / `isUnit_prime_iff_not_dvd`.
- Replaces hand-rolled valuation/norm reasoning at this project's ≥3 helper sites
  (`isUnit_natCast_of_not_dvd` in MuA.lean, `unitOfNat_coe`, `isUnit_geomSum`,
  `isUnit_two_padicInt`) and the structurally-identical
  `isUnit_natCast_of_not_dvd_residueChar` in HasseWeil
  (`FormalGroup/Associated.lean:899`).
- As `@[simp]`, discharges `IsUnit (n : ℤ_[p])` side goals automatically wherever
  `p`-adic units are constructed (Eisenstein constant coefficient, the `+`-part
  splitting, Dirac-measure unit indices).

Next action: run **`/generalise isUnit_two_padicInt`** (it will tension against
both the literature-standard general form from Phase 3 and the modern-idiom `iff`
from Phase 4c) to produce `PadicInt.isUnit_natCast_iff` (+ optional `intCast`
sibling), then `/cleanup` it, then open the mathlib PR
`feat(NumberTheory/Padics): add PadicInt.isUnit_natCast_iff`. Within AINTLIB,
once the general lemma exists, delete `isUnit_two_padicInt` and replace its 16
call sites with `PadicInt.isUnit_natCast_iff.mpr <not-dvd-proof>` (or keep a
one-line project-local `2`-face if convenient). **Proposed mathlib location:**
`Mathlib/NumberTheory/Padics/PadicIntegers.lean` (immediately after
`norm_natCast_lt_one_iff` at line 298). **PR grouping:** ship together with the
general parent (the project already has the implication as
`PadicInt.isUnit_natCast_of_not_dvd`) and, if proved, the `intCast` sibling, as
one small PR.

---

## Next step

Run `/generalise isUnit_two_padicInt` to restate it as the general
`@[simp] PadicInt.isUnit_natCast_iff : IsUnit (n : ℤ_[p]) ↔ ¬ p ∣ n` — the
missing `IsUnit` member of mathlib's existing `PadicInt.norm_natCast_*_iff`
family (the general fact is NOT in mathlib and, since `ℤ_[p]` is `CharZero`, is
NOT covered by `CharP.isUnit_natCast_iff`). Then `/cleanup` and open
`feat(NumberTheory/Padics): add PadicInt.isUnit_natCast_iff` against
`Mathlib/NumberTheory/Padics/PadicIntegers.lean`. Do not upstream the
`2`-specific wrapper; replace its 16 in-project call sites with the general
lemma.
