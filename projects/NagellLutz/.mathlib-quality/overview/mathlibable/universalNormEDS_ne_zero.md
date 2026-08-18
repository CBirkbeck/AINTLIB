# /mathlibable report — `universalNormEDS_ne_zero`

> Re-verified 2026-06-21 against pinned mathlib `09b373db6e24` (toolchain v4.32.0-rc1). All
> load-bearing facts below were re-checked by direct grep of `.lake/packages/mathlib`; the bucket
> was corrected from NO-composable-from-mathlib to **BORDERLINE-needs-human** for evidence/gate
> consistency (Phase 6 concludes NOT-COMPOSABLE-from-mathlib-alone, so the NO-composable gate fails;
> see Verdict).

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; reasoning from source)
- decl `universalNormEDS_ne_zero`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1250` (def head; proof 1250–1254;
  task prompt said 1251 — off by one).
- **Qualified name: `universalNormEDS_ne_zero`** (NO enclosing `namespace`). Re-verified: the
  declaration sits inside `section NormEDS` (line 881, `end NormEDS` 1520) and `section` (line 1203) —
  **named `section`s do NOT prefix the name**. Every `namespace` opened before line 1250
  (`EllSequence` 90, `HaveSameParity₄` 216, `IsEllSequence` 643, `EllSequence` 1079) is closed before
  1250 (the last, `EllSequence` 1079, closes at 1112). So the parsed `universalNormEDS_ne_zero` in the
  task prompt is correct (no namespace component).
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS). This file is a **fork** that
  massively expands the upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The
  fork adds: the four-/six-index elliptic-relation machinery (`addMulSub`/`rel₄`/`net`), the
  `IsEllDivSequence` theory (`IsEllSequence.ext`, `.eq_normEDS`), the **universal EDS** over a
  3-variable polynomial ring (`Param`, `universalNormEDS`), and the complement sequences. None of
  this `universalNormEDS`/`Param` machinery exists in mathlib.

Cross-project note: a **near-identical** copy lives in the HasseWeil project at
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:725` (there it is even marked
`private lemma universalNormEDS_ne_zero`), and a third copy in
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1190`. The fork is
triplicated; none of the three is in mathlib.

---

### Statement (Phase 1)

`universalNormEDS_ne_zero` states: for the **universal normalised EDS** `universalNormEDS`, every term
at a nonzero index is nonzero.

```lean
lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=
  fun h ↦ hn <| by
    apply_fun aeval (Param.rec (2 : ℤ) 3 2) at h
    simp only [universalNormEDS, map_normEDS, aeval_X, normEDS_two_three_two, map_zero] at h
    exact_mod_cast h
```

Supporting (all fork-local) definitions:
- `inductive Param : Type | B | C | D` (line 1179) — a bespoke 3-element index type, **project-only**.
- `universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)` (line 1187) — the
  normalised EDS with the three free parameters `b, c, d` taken to be the **generic** indeterminates
  `X B, X C, X D` in the polynomial ring `MvPolynomial Param ℤ`. It is the "universal" object: every
  concrete normalised EDS `normEDS b c d` is `aeval (Param.rec b c d) ∘ universalNormEDS`
  (`normEDS_eq_aeval`, line 1189), so identities about `universalNormEDS` specialise to all of them.
- `normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id` (line 1235) — **project-only**; the specialisation
  `(b,c,d) = (2,3,2)` recovers the identity sequence. Proof uses `IsEllSequence.ext` + `isEllSequence_id`.

Types / hypotheses:
- `{n : ℤ}`, `hn : n ≠ 0`.
- Coefficient ring is fixed to `MvPolynomial Param ℤ` (a polynomial ring over `ℤ` — an integral domain).

Conclusion (math): the generic `n`-th term `normEDS (X B) (X C) (X D) n` is a nonzero polynomial.

Conclusion (Lean): `universalNormEDS n ≠ 0`.

Proof idea (verbatim above): apply the evaluation ring hom `aeval (Param.rec 2 3 2)` (i.e.
`B,C,D ↦ 2,3,2`) to the hypothesis `universalNormEDS n = 0`; by `map_normEDS` + `normEDS_two_three_two`
the image is `((n : ℤ) : MvPolynomial …)` (the identity sequence at `n`), and `map_zero` makes the RHS
`0`, so `(n : ℤ) = 0` by `exact_mod_cast`, contradicting `hn`. (Mechanism: a nonzero polynomial stays
nonzero because it has at least one specialisation — here `2,3,2` — at which it is nonzero.)

---

### Size classification (Phase 2a)

Verdict: SMALL.
Reason: a helper lemma — not a `def`/`class`, not named after a person, not a `## Main statement`. It
exists to feed `universalNormEDS_mem_nonZeroDivisors` (immediately below, line 1258), which in turn
discharges the `mem : … ∈ R⁰` side-conditions of the complement/invariant lemmas via the
universal-specialisation technique.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner def check is n/a. (For the record the proof
is ~4 lines and is pure specialisation plumbing — a weak negative signal for independent inclusion.)

---

### Literature search table (Phase 3)

| Source | Query | Result |
|---|---|---|
| WebSearch | "universal elliptic divisibility sequence polynomial ring generic terms nonzero" | EDS literature (Ward 1948; arXiv 1101.3839, math/0404124, 2604.05280; Wikipedia). The **generic/universal EDS over a polynomial ring** appears as a *proof device* (prove an identity once over the generic coefficients, then specialise via a ring hom) — exactly the role `universalNormEDS` plays here. It is **not** a named, citable standalone theorem; "nonzero terms of the generic EDS" is folklore packaging of "a nonzero polynomial has a nonvanishing specialisation". |
| Concept | "nonvanishing of a polynomial detected by one specialisation" | Standard: `MvPolynomial`/`Polynomial` over a domain — a polynomial is `0` iff all evaluations vanish; equivalently, exhibiting one nonzero evaluation proves `≠ 0`. This is the entire mathematical content here. |

Conclusion: no literature theorem corresponds to `universalNormEDS_ne_zero`. Its content is the
generic-specialisation argument applied to the **fork-local** object `universalNormEDS`.

(Tool note: `lean_loogle`/`lean_leansearch` could not be loaded in this environment; `WebSearch` was
used for the literature sweep and the **local mathlib checkout** — `.lake/packages/mathlib` — was
grepped directly and exhaustively for the mathlib-search phase, which is decisive here.)

---

### Generality analysis (Phase 4)

The decl as written is **NOT maximally general** — it is hard-wired to:
- the specific coefficient ring `MvPolynomial Param ℤ`, and
- the specific construction `universalNormEDS` (= `normEDS` at the generic indeterminates).

The literature-/mathlib-standard form of "the underlying fact" is the **general** statement:

> for a normalised EDS over an integral domain, `normEDS b c d n ≠ 0` when `n ≠ 0`, under suitable
> nondegeneracy of `b, c, d` (the technique here: it suffices that *some* specialisation gives a
> nonvanishing sequence — e.g. the identity sequence `2,3,2`).

That **general `normEDS_ne_zero`** is a genuinely mathlib-worthy fact and a *currently open TODO in
mathlib*: the upstream file explicitly lists "prove `normEDS` satisfies `IsEllDivSequence`" and the
converse as TODO (lines 44–45), and has none of the nonzero/nonZeroDivisors API. So the right
generalisation target exists and is real — but it is a **different statement** from the decl under
review (which is glue specialised to `universalNormEDS`).

---

### Mathlib search — five methods (Phase 5)

Searched the pinned mathlib at `.lake/packages/mathlib` (file dated 17 Jun, 547 lines):

1. **Exact name / def** — `grep -rn "universalNormEDS" Mathlib/` → **0 hits**. `universalNormEDS` does
   not exist in mathlib. (Cannot: it is defined via the **project-local** `inductive Param`.)
2. **The supporting `Param` / `two_three_two`** — `grep -rn "inductive Param\|normEDS_two_three_two\|two_three_two" Mathlib/`
   → **0 hits**. Neither the 3-element index type nor the `(2,3,2) = id` specialisation is upstream.
3. **The EDS file contents** — mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` ends
   at `map_complEDS` (line 544/547). It contains `IsEllSequence`/`IsEllDivSequence` *definitions*,
   `preNormEDS`/`normEDS`/`complEDS₂`/`complEDS` and their basic API and `map_*` lemmas — but **no**
   `IsEllDivSequence` *proofs*, **no** `nonZeroDivisors`/`ne_zero` results, **no** universal/generic
   EDS, **no** `MvPolynomial` machinery. The relevant facts are explicit **TODOs** (lines 44–45).
4. **Building blocks that DO exist** — `map_normEDS`
   (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:530`), `MvPolynomial.aeval` / `aeval_X`,
   `MvPolynomial.X_ne_zero`, `Int.cast` injectivity / `exact_mod_cast`. These are the mathlib pieces
   the proof leans on.
5. **The load-bearing step is NOT in mathlib** — `normEDS_two_three_two` (the crux rewrite) is
   fork-local and itself rests on `IsEllSequence.ext` (line 1218) and `isEllSequence_id`, of which
   **only `isEllSequence_id` is in mathlib**; `IsEllSequence.ext` is fork-local (mathlib has no
   uniqueness lemma for elliptic sequences).

Conclusion: the decl is **absent from mathlib**, and its statement references vocabulary
(`universalNormEDS`, `Param`) that is absent too. It is not NO-mathlib-has-it.

---

### Composition check (Phase 6)

Can ≤3 **mathlib** calls give `universalNormEDS n ≠ 0` directly? **No.**

The actual proof is `apply_fun aeval (Param.rec 2 3 2)` then `simp only [universalNormEDS, map_normEDS,
aeval_X, normEDS_two_three_two, map_zero]` then `exact_mod_cast`. Of these the **decisive** rewrite is
`normEDS_two_three_two`, which is a **non-trivial fork lemma not in mathlib** (it itself needs the
fork-only `IsEllSequence.ext`). Stripping the fork lemmas, mathlib alone gives you `map_normEDS`,
`aeval_X`, `X_ne_zero`, casts — but **not** the fact that the generic sequence specialises to `id` at
`(2,3,2)`. So this is **not** a clean ≤3-mathlib-primitive composition.

However, it **IS** a short composition **relative to the project's own surrounding API** (the fork
already proves `normEDS_two_three_two` one line above): given `normEDS_two_three_two` + `map_normEDS`
(mathlib) + `X_ne_zero`/cast, the result is the 4-line glue shown. That is the sense in which it is
"composable" — composable from *fork + mathlib*, not mathlib alone.

Call sites in our project: `universalNormEDS_ne_zero` is consumed by `universalNormEDS_mem_nonZeroDivisors`
(line 1260), which is used at lines 1342 (complement) etc. — i.e. it is internal scaffolding for the
universal-specialisation technique, not an exported result.

---

## Verdict: `universalNormEDS_ne_zero`

**Category:** BORDERLINE-needs-human

(Prior draft said NO-composable-from-mathlib. Corrected: the NO-composable gate requires Phase 6 to
conclude COMPOSABLE from mathlib in ≤3 calls, but Phase 6 concludes **NOT-COMPOSABLE from mathlib
alone** — the crux `normEDS_two_three_two` is a fork lemma transitively needing the fork-only
`IsEllSequence.ext`. The decl's *statement* is also not expressible in mathlib (it names the fork-only
`universalNormEDS`/`Param`). What remains is a judgment call about the fork's universal-EDS strategy,
which is exactly BORDERLINE.)

**Evidence:**
- Literature (Phase 3): no standalone theorem; the content is "a nonzero polynomial has a nonvanishing
  specialisation," applied to the **fork-local** generic EDS. The universal/generic-EDS idea is a Ward
  proof *device*, not a citable result.
- Generality (Phase 4): the decl is a **specialisation** (fixed ring `MvPolynomial Param ℤ`, fixed
  construction `universalNormEDS`). Its mathlib-worthy *kernel* is the **general** `normEDS_ne_zero`
  (n≠0, over a domain, with nondegenerate `b,c,d`) — a real, currently-**open TODO** in mathlib (file
  lines 44–45) — but that is a **different statement**.
- Mathlib search (Phase 5): `universalNormEDS`, `Param`, `normEDS_two_three_two`, and the whole
  `IsEllDivSequence`/nonZeroDivisors layer are **absent** from mathlib (re-verified 2026-06-21,
  0 grep hits); only the base `normEDS`/`map_normEDS`/`aeval` building blocks exist. Not NO-mathlib-has-it.
- Composition (Phase 6): **NOT-COMPOSABLE** from mathlib in ≤3 calls — the crux `normEDS_two_three_two`
  is a fork lemma, transitively needing the fork-only `IsEllSequence.ext`. (It *is* a 4-line composition
  from **fork + mathlib**, but "fork + mathlib" is not the NO-composable bar, which is mathlib-only.)

**Rationale:**

`universalNormEDS_ne_zero` is **fork-internal scaffolding**, not an independent mathlib candidate. Its
very *statement* names project-only objects — `universalNormEDS` (the normalised EDS at the generic
indeterminates) and the bespoke `inductive Param` — so it cannot be proposed to mathlib as written:
mathlib would never carry a lemma whose subject is a one-off local "universal" wrapper and a 3-element
index type. The mathematical content is the standard generic-specialisation argument ("a nonzero
polynomial is detected by one nonvanishing evaluation"), here realised by specialising the generic EDS
to the identity sequence via `normEDS 2 3 2 = id`. That crux, `normEDS_two_three_two`, is itself
**fork-local and absent from mathlib** (it depends on the fork-only uniqueness lemma
`IsEllSequence.ext`), so the decl is not a clean composition of mathlib primitives either — it is
recoverable only relative to the fork's own API.

The genuinely mathlib-able object in this vicinity is the **general** non-vanishing theorem
`normEDS b c d n ≠ 0` for `n ≠ 0` over an integral domain (under suitable nondegeneracy of `b,c,d`),
which is exactly one of mathlib's listed EDS TODOs (upstream file lines 44–45). That is a
**generalise-first / future-PR** target, not this decl. The decl as-is is the universal-case glue used
to *prove* such facts inside the project (it feeds `universalNormEDS_mem_nonZeroDivisors`, which
supplies the `∈ R⁰` side-conditions throughout the complement/invariant development).

**Numbered questions (BORDERLINE — ≤5):**
1. The mathlib-worthy object here is the **general** `normEDS b c d n ≠ 0` (n ≠ 0, integral domain,
   nondegenerate `b,c,d`) — a listed upstream TODO — proved via this universal-EDS specialisation
   trick. Pursue *that* as the mathlib contribution (and keep `universalNormEDS_ne_zero` as the
   fork-internal lemma used to prove it)? (yes/no)
2. If the general `normEDS_ne_zero` is upstreamed, should the whole universal-EDS apparatus
   (`Param`, `universalNormEDS`, `normEDS_two_three_two`, `…_ne_zero`, `…_mem_nonZeroDivisors`) be
   proposed to mathlib *as the chosen proof mechanism*, or kept project-local? (mathlib / local)
3. Independently of mathlib: consolidate the **triplicated** universal-EDS block (NagellLutz
   `EllipticDivisibilitySequence.lean`, NagellLutz `EllipticDivisibilitySequenceOriginal.lean`,
   HasseWeil `Auxiliary/EllipticDivisibilitySequence.lean`) into one shared copy now? (yes/no)

**WHY (refactor-actionable) — supporting the BORDERLINE call:**
Not a standalone mathlib PR as written. The decl references fork-only vocabulary (`universalNormEDS`,
`Param`) and its proof depends on a fork-only crux lemma; it only makes sense bundled with the fork's
universal-EDS development. The honest mathlib action is to upstream the **general** `normEDS_ne_zero`
(the TODO), at which point this universal-case lemma either becomes a trivial corollary or is the
chosen internal proof device — which is the human call (Q1/Q2).

Mathlib building blocks (what the proof reuses):
- `map_normEDS` — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:530`
- `MvPolynomial.aeval_X`, `MvPolynomial.X_ne_zero`, `Int.cast` injectivity (`exact_mod_cast`)

Fork-local (would travel with the development, NOT in mathlib):
- `universalNormEDS` (line 1187), `inductive Param` (line 1179)
- `normEDS_two_three_two` (line 1235) — the crux; itself needs `IsEllSequence.ext` (line 1218)

Composition sketch (the existing 4-line proof — fork + mathlib, NOT mathlib-only):
```lean
fun h ↦ hn <| by
  apply_fun aeval (Param.rec (2 : ℤ) 3 2) at h
  simp only [universalNormEDS, map_normEDS, aeval_X, normEDS_two_three_two, map_zero] at h
  exact_mod_cast h
```

Refactor plan:
- **Primary (cross-project dedup, do regardless):** the universal-EDS block (`Param`,
  `universalNormEDS`, `normEDS_two_three_two`, `universalNormEDS_ne_zero`,
  `universalNormEDS_mem_nonZeroDivisors`) is **triplicated** across NagellLutz
  `EllipticDivisibilitySequence.lean`, NagellLutz `EllipticDivisibilitySequenceOriginal.lean`, and
  HasseWeil `Auxiliary/EllipticDivisibilitySequence.lean`. Consolidate to one copy (coordinator-level
  dedup) before any mathlib consideration.
- **Mathlib disposition:** none for this decl as written. If/when the **general** `normEDS_ne_zero`
  (n≠0, domain, nondegenerate `b,c,d`) is upstreamed (it is a listed mathlib TODO), revisit — the
  universal-case lemma then folds into it.

Next action: answer Q1–Q3 above. Default recommendation absent further input: do NOT open a standalone
mathlib PR for `universalNormEDS_ne_zero`; de-duplicate the triplicated universal-EDS scaffolding across
NagellLutz/HasseWeil; keep this as a local helper bundled with the universal-EDS development; and
(separately, as a real mathlib contribution) pursue the general `normEDS_ne_zero` TODO.

---

## Next step

Human call (BORDERLINE): decide Q1–Q3 — pursue the *general* `normEDS b c d n ≠ 0` (n≠0) upstream TODO
(yes/no), propose-or-keep-local the universal-EDS apparatus, and de-duplicate the triplicated block.
Absent input, treat `universalNormEDS_ne_zero` as fork-internal scaffolding (statement + crux both live
only in the fork) and pursue the general `normEDS_ne_zero` as the separate, generalise-first mathlib
contribution.
