# Mathlibable assessment — `invar_normEDS`

**Verdict: `BORDERLINE-needs-human`**

- **Qualified name:** `invar_normEDS` (root namespace — verified below; no enclosing `namespace`)
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1478`
- **Date:** 2026-06-21 (re-run; supersedes the 2026-06-18 assessment, which is preserved in spirit below)
- **One-line:** genuine, mathlib-absent, maximally-general EDS content (the `normEDS` payoff of Ward's
  EDS invariant), but it is a one-line root-namespace *specialisation wrapper* of the general
  `EllSequence.invar_of_net` — squarely on the direct path to mathlib's still-open `normEDS satisfies
  IsEllDivSequence` TODO, yet duplicated in-repo and colliding with the in-flight mathlib PR #25989.
  Whether it survives as named public mathlib API (vs. riding inside the `IsEllSequence (normEDS …)`
  interface as a `private` step) is a human packaging/dedup decision. Same disposition as its
  structural twin `rel₄_normEDS`.

---

## 0. Baseline (Phase 0)

- **lake build:** not run — local build is stale per task brief. Reasoned directly from source; the
  statement is unambiguous and the proof is a single `sorry`-free term.
- **decl resolved at:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1478`.
- **kind:** `lemma` (no `sorry`).
- **module docstring summary:** "Elliptic divisibility sequences" — defines EDS and constructs
  normalised EDSs from initial terms (file © 2024 David Kurniadi Angdinata; the in-progress upstream
  of the EDS-over-commutative-rings development, Angdinata–Xu arXiv:2604.05280).

### Qualified-name verification (root namespace)

The file opens `namespace EllSequence` at L90 but **closes** it at L597 (`end EllSequence`), then
`open EllSequence` at L599. All intervening namespaces are balanced and closed before L1478:
`IsEllSequence` (L643–702), the inner `EllSequence` blocks (L1079–1112, L1356–1431), `HaveSameParity₄`
(L216–297). Line 1478 sits inside **`section NormEDS`** (opened L881, `end NormEDS` L1520) — and a
plain `section` contributes **nothing** to the qualified name. There is no active `namespace` at
L1478. Hence the true qualified name is the bare **`invar_normEDS`** — the parsed/prompt name is
**correct**. (`open EllSequence` is in scope, so the *bodies* `invarNum`, `invarDenom`, `net_normEDS`,
`invar_of_net` resolve to `EllSequence.*`; the lemma itself is top-level.)

---

## 1. Statement (Phase 1)

```lean
omit ellW ellU in
lemma invar_normEDS (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ net_normEDS _ _ _
```

Ambient context: `variable {R : Type u} [CommRing R]` (L85) + `variable (b c d : R)` (L883);
`open scoped nonZeroDivisors`. The `omit ellW ellU` drops the elliptic-sequence hypotheses, so the
statement is **hypothesis-free** over an **arbitrary commutative ring**.

Supporting defs (all project-new, in `EllSequence`):
- `invarNum W s n := (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²`  (L140)
- `invarDenom W s n := W(n+s)·W(n)·W(n−s)`  (L145)
- `net W p q r s := W(p+q+s)W(p−q)W(r+s)W(r) − W(p+r+s)W(p−r)W(q+s)W(q) + W(q+r+s)W(q−r)W(p+s)W(p)`
  (L115) — Stange's elliptic-net relation (signs/term-order tweaked, per the docstring, to make the
  `rel₄`-equivalence unconditional and char-3-safe).
- `invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n)` (L149) — the **general** engine:
  the same cross-product conclusion for *any* `W : ℤ → R` whose `net` vanishes identically, with no
  elliptic / no non-zero-divisor hypotheses.
- `net_normEDS (p q r s)` (L1465) — the net of `normEDS b c d` vanishes identically (proved via the
  universal `MvPolynomial Param ℤ` carrier `universalNormEDS` and `IsEllSequence.normEDS.net`).

### Mathematical content

For the canonical normalised EDS `normEDS b c d`, the ratio `invarNum s n / invarDenom s n` is
**independent of the moving index `n`** (for each fixed shift `s`), stated cross-multiplied to stay
division-free over a general commutative ring. This is the classical "invariant of an elliptic
divisibility sequence" (it ultimately encodes the Weierstrass curve invariants `b₂, b₄`), specialised
from the elliptic-net relation to the concrete `normEDS`. The lemma is a **one-line corollary**: it
plugs `net_normEDS` (the fact that `normEDS`'s net vanishes) into the general engine `invar_of_net`.

Conclusion (Lean): `invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n = invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m`.

---

## 2. Preliminary checks (Phase 2)

### 2a. Size classification

**Verdict: SMALL.** A one-line term-mode corollary specialising the general `invar_of_net` to
`normEDS`; not itself a `def`/structure and not a stand-alone `## Main statements` headline (the
headline is `isEllDivSequence_normEDS`, which this feeds via `invar₂_normEDS`/`redInvar_normEDS`). It
*is* on a named-theorem path (Ward/Stange/Xu EDS theory) — literature width run exhaustively
regardless.

### 2b. One-line check

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner-def gate (defeq/diamond/API-name
exemptions) does not apply. Noted for Phase 7 granularity: the body is the single term
`invar_of_net _ net_normEDS _ _ _` (a one-line specialisation wrapper).

---

## 3. Literature search — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific) | EDS invariant `W(n+s)W(n−s)` cross-ratio independent of n (Ward) | yes | the EDS invariant ratio / determinant (cross-ratio) form | Wikipedia *EDS*; the index-independent invariant is built into the determinant formulation; Ward *Memoir* originates it |
| 2  | WebSearch (general) | elliptic net relation; `normEDS` over a commutative ring | yes | Stange net relation; Angdinata–Xu commutative-ring EDS | arXiv:0710.1316 (Stange), arXiv:2604.05280 (Angdinata–Xu) — exactly this `CommRing` setup; mathlib4-docs hosts the `normEDS`/`IsEllDivSequence` defs |
| 3  | WebSearch (named-after / PR) | mathlib4 PR #25989 elliptic nets `IsEllipticNet` Angdinata | yes | `IsEllipticNet`/`atom`/`atomRel`/`rel` (= upstream `addMulSub`/`rel₄`/`net`) | **fetched live 2026-06-21**: PR #25989 is **OPEN**, title `feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets`; infra only, **no `normEDS` payoff, no `invarNum`/`invarDenom`/`invar_of_net`**; a small standalone piece of the larger PR #13155 (continues #25030) |
| 4  | ChatGPT MCP | (standard form + generality + historical evolution) | n/a | — | MCP down per task brief; compensated by WebSearch ×3 at distinct generality levels + two live WebFetches (PR #25989, mathlib4-docs) + the corroborating sibling reports |
| 5  | Local references | grep `.mathlib-quality/references/` | n/a | — | directory absent (only `overview/` exists under `.mathlib-quality/`) — recorded n/a |
| 6  | nLab | "elliptic divisibility sequence" / "elliptic net" | n/a | — | nLab has no dedicated EDS/elliptic-net-invariant page; the concept lives in the arithmetic-geometry literature (Ward/Stange/Xu), already covered by #1–#2 |
| 7  | nCatLab | (categorical) | n/a | — | not a categorical concept |
| 8  | Stacks Project | "elliptic divisibility sequence" | n/a | — | Stacks covers scheme-theoretic foundations; EDS recurrences/invariants are not a Stacks topic |
| 9  | MathOverflow / MSE | EDS invariant ratio independent of index | yes (background) | the invariant is standard folklore in the EDS/Somos literature | confirms it is textbook, not a separately-named quotable theorem |
| 10 | arXiv (recent) | elliptic sequences over commutative rings; symmetries of elliptic nets | yes | Angdinata–Xu arXiv:2604.05280; *On Symmetries of Elliptic Nets* arXiv:1408.6623 | the formalisation target (Angdinata–Xu) develops EDS over arbitrary `CommRing` and proves `normEDS` satisfies the relations algebraically |

### Literature summary (Phase 3)

- **Concept identified as:** the *invariant of an elliptic divisibility sequence* — for an elliptic
  sequence the ratio with denominator `W(n+s)·W(n)·W(n−s)` is independent of `n` — specialised to the
  canonical `normEDS`. The underlying relation is **Stange's elliptic-net relation** (`net`); the
  classical source is **Ward, *Memoir on Elliptic Divisibility Sequences*** (the file's cited
  reference).
- **Sources agree on the standard form:** yes — the recurrence/relation algebra is textbook (Ward,
  Stange, Angdinata–Xu, Wikipedia). The **index-independent invariant** is standard folklore inside
  that theory.
- **Most general standard form:** the invariant is derived from the net/elliptic relation for an
  *arbitrary* elliptic net/sequence over a commutative ring (Angdinata–Xu, arXiv:2604.05280). That
  net→invariant derivation is the project's **general** `invar_of_net`; `invar_normEDS` is its
  concrete `normEDS` image.
- **Generality dimensions where the literature varies:** the *carrier* (ℤ → field, classically;
  ℤ → arbitrary `CommRing`, modern/Angdinata–Xu — the strictly more general one); the *object* (a
  general elliptic net/sequence vs. the specific `normEDS`). The Lean form already sits at the most
  general carrier (`CommRing`), specialised to `normEDS`.
- **Disagreement with the literature:** none. But note: there is **no separately-named theorem**
  matching this exact cross-product identity. It is a *step in the standard development* ("the EDS
  carries an index-independent invariant"), not an independently citable named result — and
  `invar_normEDS` is specifically the `normEDS`-specialisation of that step, even less of a stand-alone
  named theorem than the general `invar_of_net`.

---

## 4. Generality analysis

### 4a/4b. Generality status + verdict

Literature-standard form (Phase 3): the invariant derived from the net relation for any elliptic
net/sequence over a commutative ring — i.e. the **general** `invar_of_net`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker exists? | Reason |
|---|------------------------|-------------------|---------------------|----------------|--------|
| 1 | `[CommRing R]` | arbitrary commutative ring | commutative ring (Angdinata–Xu) | NO | `normEDS` is a polynomial in `b,c,d`; the identity is a polynomial identity — no weaker typeclass (already the floor; not even `IsDomain`/`Field` needed) |
| 2 | `(b c d : R)` | arbitrary coefficients | arbitrary | NO | already fully general; no constraint imposed |
| 3 | hypotheses | **none** (`omit ellW ellU`) | net-vanishing is discharged internally for `normEDS` | NO | the only "hypothesis" (`net normEDS = 0`) is supplied by `net_normEDS`, not assumed; cannot be weakened |
| 4 | indices `s m n` | `ℤ` | `ℤ` | NO | EDS are indexed by `ℤ` by definition |

**Verdict: MAXIMALLY GENERAL.** Number of weakening opportunities: **0**. There is **nothing to
weaken** — the statement is already at the maximal `CommRing`, coefficient-free, hypothesis-free
generality (matching Angdinata–Xu exactly). Generalisation in the assumption-weakening sense is
therefore **not** the blocker here.

The one object "more general" than `invar_normEDS` is not a weakening of *it* but a different
declaration: the general engine `EllSequence.invar_of_net` (the `W`-with-vanishing-net form) — which
already exists in the file and is separately assessed (`invar_of_net.md`, YES-but-generalise-first).
`invar_normEDS` is the **concrete `normEDS` specialisation** of that engine. (And one step further
toward the user-facing API is `EllSequence.IsEllSequence.invar` at L699 — the same conclusion for any
elliptic sequence `W`, the natural public form.)

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | "let X be a foo" → typeclass/instance? | no | already typeclass-driven (`[CommRing R]`); no bundled preamble to convert |
| 2 | sequences/metric → filters/topology? | no | a polynomial identity over `ℤ`-indexed sequences; no topology/limit to filter-ise |
| 3 | construct → universal property? | partial (not here) | the upstream modernisation is `IsEllipticNet` (mathlib PR #25989: abstract relator `rel`); but that re-aims the *def* `net`, not this lemma. The lemma's modern form is "the `rel`-form of `normEDS`'s invariant", which is the same packaging question, not a reformulation of `invar_normEDS` itself |
| 4 | set-with-closure → bundled substructure? | no | not a substructure statement |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing` floor |
| 6 | 1-categorical → higher-categorical? | no | not categorical |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | EDS are intrinsically `ℤ`-indexed |

**Modern idiom available: no** (for `invar_normEDS` as such). The relevant modernisation —
`net ↦ IsEllipticNet.rel` from PR #25989 — is a realignment of the **definitions** the lemma
quantifies over, not a better formulation of this lemma. It is captured in the packaging question
(Phase 7), not as a generalise-first restatement of `invar_normEDS`. (Same reason `rel₄_normEDS` was
**not** bucketed YES-but-generalise: already maximal; modernisation lives in the def layer /
packaging.)

---

## 4.5 Diamond / defeq risk

n/a — declaration kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

## 5. Mathlib search (five methods) — forked files checked first

Per project context, NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether this
lemma (or its apparatus) is already upstream. **It is not.**

```
[A] Lean-Finder       "normEDS invariant cross product", "invar_normEDS"   no hits (index unaware of `invar*`/`net`)
[B] Loogle            ?invarNum (normEDS ..) .. * ?invarDenom .. = ..        no hits — `invarNum`/`invarDenom` undefined in mathlib
[C] LeanSearch        "normEDS carries an index-independent invariant"       no hits
[D] Grep mathlib src  invar_normEDS / invarNum / invarDenom / `def net ` /
                      rel₄ / addMulSub / EllSequence / IsEllipticNet over
                      .lake/packages/mathlib/Mathlib/**                       ZERO hits for all
[E] Name pattern      invar_normEDS, net_normEDS, isEllDivSequence_normEDS    absent
```

Verified facts (greps run this session against the pinned checkout; PR + docs fetched live 2026-06-21):

1. **Pinned mathlib EDS file** (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
   547 lines): defines `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence` as flat `Prop`s, then
   `preNormEDS`/`normEDS`/`complEDS`/`*Rec`/`map_*`. It has **no `EllSequence` namespace** and **none**
   of `addMulSub`, `rel₄`, `net`, `Rel₃`, `invarNum`, `invarDenom`, `invar_of_net`, `invar_normEDS`.
   It still carries the **open TODOs** (grep + live mathlib4-docs, 2026-06-21):
   > * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
   > * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
   `invar_normEDS` is a **load-bearing step on the first TODO** (see consumer chain in §6).
2. **mathlib `DivisionPolynomial/{Basic,Degree}.lean`:** consume `normEDS`/`preNormEDS`; re-export
   `normEDS_*`; **no** four-index relation, **no** `net`/`invar` invariant.
3. **In-flight mathlib PR #25989** (`feat: add elliptic nets`, Angdinata) — **OPEN** (confirmed live
   2026-06-21) — adds the abstract relator `IsEllipticNet` + `atom`/`atomRel`/`rel` (upstream names for
   `addMulSub`/`rel₄`/`net`) and refactors `IsEllSequence` over the net relator. It is **infrastructure
   only**: it does **not** carry any `normEDS`-satisfies-the-relation lemma, and **no**
   `invarNum`/`invarDenom`/`invar_normEDS`. So this lemma is absent from the open PR too. (It is "a
   small standalone component" of the larger PR #13155, continuing #25030.)
4. **Within AINTLIB (dedup, not mathlibability):** `invar_normEDS` is **duplicated** verbatim — here
   (L1478) and `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:960`. (The 2026-06-18 report also
   counted a copy in `LutzNagell/EllipticDivisibilitySequenceOriginal.lean`; **that file has since been
   deleted** — only its inventory `.md` remains — so the live count is now **two**, not three.) This is
   intra-repo forking (a `/cleanup`/dedup concern), **not** evidence of a mathlib home.

**Concluded:** not in mathlib (all methods exhausted, plus the apparatus it depends on and the
in-flight PR #25989). The only upstream relationship is the **open TODO** this chain is designed to
discharge.

---

## 6. Composition check (+ call-sites)

### 6.0. Call sites — `invar_normEDS`

Internal use count (this project, excluding the declaring lemma line): **1** direct call.
External-to-file callers within NagellLutz: 0 distinct files (the consumer is in the same file).
Cross-project: the lemma is **duplicated** (not imported) in HasseWeil.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:1487` | `convert invar_normEDS 1 m (2 : ℤ) <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]` — inside `private lemma invar₂_normEDS_of_mem_nonZeroDivisors` (L1484) |

Downstream chain (load-bearing, despite K=1 direct): `invar_normEDS` →
`invar₂_normEDS_of_mem_nonZeroDivisors` (L1484) → `invar₂_normEDS` (L1491) → `redInvar_normEDS` (L1509)
→ **`DivisionPolynomialOmega.lean`** (`ω_spec`, via `redInvar_normEDS`), the ω/division-polynomial
identity central to the Nagell–Lutz development. So `invar_normEDS` is a real, used step (not dead
code), even though it has only one direct caller.

Inline-derivation grep: the duplicated copy in HasseWeil is not an inline re-derivation but a verbatim
fork of the same lemma — a dedup signal (handled by `/cleanup`), not a "consumers bypass it" signal.

### 6a. Composition attempt

Can `invar_normEDS` be derived from **mathlib** in ≤3 chained calls? **No.**

- Attempt 1: there is nothing upstream to compose against — mathlib has **no `net`**, **no
  `invarNum`/`invarDenom`**, **no `invar_of_net`**, and **no elliptic-net relation API** (released; and
  #25989 carries only the abstract relator, not the invariant or the `normEDS` payoff). The statement
  is **not even expressible** with current mathlib public API.
- Within the *project*, it is literally a 1-call corollary (`invar_of_net _ net_normEDS _ _ _`) — but
  `invar_of_net` and `net_normEDS` are project-new, not mathlib primitives. Per the heuristics, a
  composition out of **project-local** lemmas does not count as NO-composable-from-mathlib.

**Conclusion: NOT-COMPOSABLE** (from mathlib).

---

## 7. Verdict

## Verdict: `invar_normEDS`

**Category: `BORDERLINE-needs-human`**

**Evidence:**
- Literature search (Phase 3): standard Ward/Stange/Angdinata–Xu EDS theory; genuine content; **no
  separately-named theorem** for this exact cross-product identity — it is a step in the development,
  here specialised to `normEDS`. Sources: Ward *Memoir*; Stange arXiv:0710.1316; Angdinata–Xu
  arXiv:2604.05280.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — arbitrary `CommRing`, coefficient-free,
  hypothesis-free; **0** weakening opportunities; no modern-idiom restatement of the lemma itself.
  Generalisation is **not** the blocker.
- Mathlib search (Phase 5): not in released mathlib, not in `DivisionPolynomial`, and **not in the open
  PR #25989**; the target `isEllDivSequence_normEDS` TODO is **explicitly open** (verified live
  2026-06-21). Duplicated in-repo (×2).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the `net`/`invar` apparatus is
  upstream-absent; the statement is not even spellable).

**Rationale.**

The *mathematics* is genuinely mathlib-worthy: it is standard, absent from mathlib, maximally general,
and sits on the direct path that discharges mathlib's documented `normEDS satisfies IsEllDivSequence`
TODO (via `invar₂_normEDS` → `redInvar_normEDS` → the division-polynomial `ω_spec` identity). That
pushes toward YES, and rules out both NO buckets decisively (mathlib lacks it **and** lacks any
composition of it — even the statement is unspellable upstream today).

But `invar_normEDS` **as an isolated declaration** is the wrong granularity to port, and which way it
resolves is a human call the evidence does not settle:

1. **It is an internal `normEDS`-specialisation wrapper, not the natural API.** The general theorem is
   `EllSequence.invar_of_net` (assessed YES-but-generalise-first); the user-facing form of "an EDS
   carries an invariant" is `EllSequence.IsEllSequence.invar` (L699). `invar_normEDS` is the one-line
   `normEDS` image (`invar_of_net _ net_normEDS _ _ _`), used only as a `private` step toward
   `redInvar_normEDS`. In a mathlib PR it would most plausibly be a *supporting/`private`* lemma behind
   the `IsEllSequence (normEDS …)` / `IsEllDivSequence (normEDS …)` interface (the literal TODO
   targets, which this same file proves), not a public declaration added "as is".

2. **It is not a generalise-first case** (nothing to weaken — already maximal; no modern-idiom
   restatement of *the lemma*), and **not a clean add-as-is** (wrong unit / wrong granularity relative
   to the `IsEllSequence`/`IsEllDivSequence` API). The only "more general" object, `invar_of_net`,
   already exists and is separately assessed. So the standard YES sub-buckets do not fit; the blocker
   is packaging, which is a taste/interface decision the worker cannot ground in the evidence.

3. **Two cross-cutting decisions must precede upstreaming**, both human: (a) **dedup** the two verbatim
   in-repo copies (NagellLutz L1478, HasseWeil L960) into one source of truth; (b) **coordinate with
   mathlib PR #25989** — after it lands `IsEllipticNet`/`rel`, realign `net ↦ IsEllipticNet.rel` and
   decide whether the `normEDS`-invariant payoff (`invar_normEDS` and the `invar`/`redInvar` chain) is
   exposed or kept internal in the follow-up PR that closes the TODO.

This is the **same disposition as its structural twin `rel₄_normEDS`** (also root-namespace, also a
one-line maximally-general `normEDS`-specialisation on the TODO path) — `BORDERLINE-needs-human` for a
packaging/interface/dedup judgement, not NO (mathlib lacks it **and** any composition of it) and not a
clean YES (wrong granularity; generalisation is not the lever).

**Numbered questions (≤5):**

1. Should the `normEDS`-invariant identity enter mathlib as the **public** API
   `IsEllSequence (normEDS b c d)` / `IsEllDivSequence (normEDS b c d)` (the literal open TODO), with
   `invar_normEDS` kept **`private`** as an internal step — i.e. *not* a named public mathlib
   declaration?
2. After mathlib PR #25989 lands `IsEllipticNet`/`rel`, should the upstreamed form be stated in the
   `IsEllipticNet.rel` vocabulary (realigning `net`), with `invar_normEDS` re-expressed accordingly —
   or is the bespoke `invarNum`/`invarDenom` packaging retained?
3. Confirm the consolidation precondition: unify the two in-repo copies (NagellLutz + HasseWeil) into
   one `Common/` source of truth **before** any upstreaming — yes/no?
4. If `invar_normEDS` is *not* part of mathlib's public surface (per Q1), do you still want it tracked
   for the upstream PR as a supporting lemma, or dropped from mathlib consideration entirely (kept
   project-local)?

**Next action:** user answers Q1–Q4; re-run `/mathlibable invar_normEDS` to resolve. Most likely
outcome: it rides the `isEllDivSequence_normEDS` upstreaming as a `private`/supporting lemma (so it is
*not* independently added), after the in-repo dedup and the #25989 realignment — i.e. effectively
folded into the `invar_of_net` / `IsEllSequence.invar` / `net_normEDS` PR bundle that closes the TODO.

---

## 8. Evidence index

- **Source:** `EllipticDivisibilitySequence.lean:1478` (`invar_normEDS`); inputs `:149`
  (`invar_of_net`), `:1465` (`net_normEDS`), `:140`/`:145` (`invarNum`/`invarDenom`), `:115`
  (`def net`); natural-API sibling `:699` (`IsEllSequence.invar`); consumer `:1487`
  (`invar₂_normEDS_of_mem_nonZeroDivisors`) → `:1491` (`invar₂_normEDS`) → `:1509`
  (`redInvar_normEDS`) → `DivisionPolynomialOmega.lean` (`ω_spec`).
- **Pinned mathlib:** `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (547 lines) — apparatus absent (flat `IsEllSequence`; no `EllSequence`/`net`/`invar*`/`IsEllipticNet`);
  TODOs open (verified live 2026-06-21).
- **mathlib PR #25989** (OPEN, verified live 2026-06-21) `feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets`
  (Angdinata) — `IsEllipticNet`/`atom`/`atomRel`/`rel`; **no `normEDS` payoff, no invariant**; a
  standalone component of PR #13155 (continues #25030).
- **In-repo duplicate (dedup, not mathlibability):** `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:960`.
  (`LutzNagell/EllipticDivisibilitySequenceOriginal.lean` — the third 2026-06-18 copy — **no longer
  exists**; only its inventory `.md` remains.)
- **Literature:** Ward, *Memoir on Elliptic Divisibility Sequences* (cited reference); Stange,
  *Elliptic nets and elliptic curves* (arXiv:0710.1316); Angdinata–Xu, *On Elliptic Sequences over
  Commutative Rings* (arXiv:2604.05280); *Elliptic divisibility sequence* (Wikipedia,
  determinant/cross-ratio form); *On Symmetries of Elliptic Nets* (arXiv:1408.6623).
- **Family cross-refs (this folder):** `invar_of_net.md` (YES-but-generalise-first — the general
  engine), `IsEllSequence.invar.md` (YES-but-generalise-first — the natural API form), `net_normEDS.md`
  (YES-but-generalise-first — its sibling hypothesis-provider), `rel₄_normEDS.md`
  (**BORDERLINE-needs-human** — the closest structural twin), `net.md` (NO-mathlib-has-it — def =
  #25989's `rel`), `map_invarDenom.md` (NO-composable — the `invar*` track is absent from mathlib).

## Method-gap honesty note

- **Local Lean build stale** (per brief): statement/type read directly from source; it is unambiguous
  (`lemma invar_normEDS (s m n : ℤ) : … := invar_of_net _ net_normEDS _ _ _`) and `sorry`-free.
- **ChatGPT MCP** down (per brief): compensated with WebSearch (×3 at different generality levels) plus
  **two live WebFetches this session** — PR #25989 (still OPEN, infra-only scope) and the mathlib4-docs
  EDS page (apparatus absent, TODOs still open) — and the corroborating 2026-06-18 sibling reports. The
  verdict rests on directly-verified, current facts (apparatus absent from pinned source + open TODO +
  #25989 scope + in-repo duplication + the one-line specialisation-wrapper shape), not on the missing
  channel.
- **Delta vs. the 2026-06-18 run:** verdict unchanged (`BORDERLINE-needs-human`). Only correction: the
  in-repo copy count dropped 3 → 2 (`EllipticDivisibilitySequenceOriginal.lean` deleted); live re-checks
  confirm mathlib TODOs still open and PR #25989 still OPEN/out-of-scope.
