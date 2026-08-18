# Mathlibable assessment — `normEDS_mul_complEDS`

**Verdict bucket:** `YES-add-as-is`
**Qualified name:** `normEDS_mul_complEDS` (root namespace)
**Date:** 2026-06-21
**Project:** NagellLutz (`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1338`)

---

## 0. The declaration (verified from source)

```lean
omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂ in
open Param in
lemma normEDS_mul_complEDS (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [normEDS_zero, mul_comm n 0]
  · have := congr(aeval (Param.rec b c d) $(normEDS_mul_complEDS_of_mem
      (b := X (R := ℤ) B) (c := X C) (d := X D)
      (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)
      (universalNormEDS_mem_nonZeroDivisors hm) n))
    simpa only [map_mul, map_normEDS, map_complEDS, aeval_X] using this
```

- True qualified name: **`normEDS_mul_complEDS`**. The declaration sits inside `section`s only
  (`section NormEDS` / `section Complement` etc.) — no enclosing `namespace` is open at line 1338
  (verified: the only `namespace` in scope, `EllSequence`, closed at line 1112). So the fully
  qualified name has no prefix. (The prompt's parsed guess `normEDS_mul_complEDS` is correct.)
- `b c d : R` are section variables with `[CommRing R]`; `complEDS b c d m = compl (normEDS b c d)
  (compl₂EDS b c d) m`.
- **Mathematical content:** the normalised EDS `W = normEDS b c d` satisfies
  `W(m) · Wᶜ(m, n) = W(n·m)`, where `Wᶜ = complEDS` is the division-free "complement" sequence
  representing `W(n·m)/W(m)`. This is the constructive witness that `W(m) ∣ W(n·m)` for **all**
  `m, n ∈ ℤ` — i.e. the full *divisibility* in "elliptic divisibility sequence".

Downstream in the same file it is the sole engine of:
- `IsDivSequence.normEDS` (line 1437) — `normEDS` is a divisibility sequence;
- `IsEllDivSequence.normEDS` (line 1444) — `normEDS` is an EDS;
- `IsEllSequence.isDivSequence_of_dvd` / `eq_normEDS_of_dvd` (line 1450) — converse: every suitable
  elliptic sequence equals a `normEDS`.

---

## 1. Literature search

`normEDS` is mathlib/AINTLIB's formalisation of **Morgan Ward's normalised elliptic divisibility
sequence** (M. Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70 (1948)). The
defining feature of an EDS — the reason for the word *divisibility* — is exactly:

> if `m ∣ n` then `W(m) ∣ W(n)`  (equivalently `W(k) ∣ W(n·k)` for all `n`).

WebSearch (Wikipedia "Elliptic divisibility sequence"; Ward's Memoir Thms 12.1/19.1; Stange,
*Elliptic nets and elliptic curves*, arXiv:0710.1316; Silverman/Shipsey) confirms this is a **named,
textbook, foundational** property — not a bespoke lemma. Ward proves it via the addition formula /
the sigma-function form `W_n = σ(nξ)/σ(ξ)^{n²}`; the Lean proof instead gives a purely algebraic,
division-free witness `complEDS` and proves the product identity by strong induction +
specialisation from the universal EDS over `MvPolynomial Param ℤ`.

→ The statement is squarely a standard result about a standard object. Strong prima-facie case for
mathlib.

## 2. Mathlib search (five methods, against the pinned source)

The repo builds against a real mathlib checkout at `.lake/packages/mathlib` (rev `09b373db6e24`,
toolchain `v4.32.0-rc1`). This project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
— so the right question is whether upstream already has this. Findings (all by direct `grep`/Read on
the pinned source — authoritative for a fork-vs-upstream question and not subject to index staleness;
loogle/leansearch were not reachable in this environment, but source grep over the *exact* built
mathlib is dispositive):

- **`complEDS` ALREADY EXISTS in mathlib** —
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:427`, signature `complEDS b c d k n`
  (mathlib's `k` = the project's `m`). Same author (D. K. Angdinata), same docstrings, same
  `complEDS'` recursion, same `complEDS_even` / `complEDS_odd`.
- **Mathlib's `complEDS` docstring literally promises the identity** (lines 388–389):
  *"the complement sequence … that witnesses `W(k) ∣ W(n·k)`. In other words,
  `W(k) * Wᶜ(k, n) = W(n·k)` for any `k, n ∈ ℤ`."* — verbatim the statement of
  `normEDS_mul_complEDS`.
- **BUT mathlib does NOT prove it.** Exhaustive search of the *entire* pinned mathlib:
  - `grep "normEDS_mul_complEDS"` → 0 hits.
  - `grep` for any `normEDS … * complEDS … = normEDS …` identity → 0 hits.
  - `grep "IsDivSequence (normEDS" / "isEllDivSequence_normEDS" / "IsDivSequence.normEDS"` → 0 hits.
    Mathlib proves `isEllDivSequence_id` only; it does **not** prove `normEDS` is a divisibility
    sequence.
  - The only related result mathlib has is the **n = 2 special case**
    `normEDS_dvd_normEDS_two_mul` (`…:326`, via `complEDS₂`); the general-`n` divisibility is absent.
- **DECISIVE — mathlib's own file marks this as an open TODO** (`…:44–45`):
  ```
  * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
  * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
  ```
  `normEDS_mul_complEDS` is precisely the lemma that discharges the **first** TODO (and the project's
  `eq_normEDS_of_dvd` discharges the second). The hooks (`complEDS`, its docstring contract) sit in
  mathlib waiting for exactly this theorem.
- Method coverage: (1) exact-name grep ✓; (2) statement-shape grep ✓; (3) read upstream `ComplEDS` +
  `Map` sections in full (lines 384–547) ✓; (4) downstream-consumer grep
  (`DivisionPolynomial/Basic.lean`, `Degree.lean`) — `complEDS` is used **only** inside the EDS file
  ✓; (5) divisibility-API grep (`normEDS_dvd` / `dvd_normEDS`) ✓.

→ **Not in mathlib.** The definition and its docstring contract are there; the theorem is an
explicit, named gap.

## 3. Generality analysis

The statement is already at the maximal natural generality for this object:
- Ring: arbitrary `CommRing R` (the section's `[CommRing R]`); no integral-domain / field hypothesis
  — the universal-EDS specialisation (`universalNormEDS : ℤ → MvPolynomial Param ℤ`, whose nonzero
  terms are non-zero-divisors) is exactly what removes any domain assumption. Matches mathlib's
  generality for `complEDS`/`normEDS`.
- Indices: full `m n : ℤ` (both signs), not just `ℕ`.
- Stated for the canonical `normEDS b c d`, the right level: every elliptic sequence whose first
  terms are non-zero-divisors equals `W(1) • normEDS …` (the file's `eq_normEDS_of_dvd`), so the
  `normEDS` form is universal and the general `IsDivSequence` corollary follows.

No weakening or strengthening is warranted; the form matches the literature standard (`W(k) ∣ W(nk)`)
and mathlib's existing `complEDS` API verbatim.

## 4. Composition check (≤ 3 mathlib calls?)

No. From what mathlib currently has (`complEDS_even`, `complEDS_odd`, `normEDS_mul_complEDS₂`,
`normEDS_dvd_normEDS_two_mul`) there is **no** ≤3-lemma route to the general-`n` identity. A proof
needs:
1. the full strong induction on `n` over the `complEDS'`/`compl'` recursion
   (`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`, a ~25-line inductive proof using
   the elliptic relation), and
2. the universal-EDS specialisation (`universalNormEDS_mem_nonZeroDivisors` + `aeval` transfer) to
   discharge the non-zero-divisor side condition over an arbitrary `CommRing`.

That is a multi-hundred-line development (the project spends lines ~844–1346 building `complEDS₂`,
`complEDS'`, `compl`, `compl₂EDS(Aux)`, the universal EDS, and the inductive core), not a short
composition of existing primitives. **Not composable.**

## 5. Verdict

**`YES-add-as-is`.**

`normEDS_mul_complEDS` is the standard Ward divisibility property for normalised EDSs, stated at full
generality (`CommRing`, `m n : ℤ`) against the **`complEDS` definition that mathlib already ships**,
whose docstring promises exactly this identity, and which mathlib flags via an explicit
`TODO: prove that normEDS satisfies IsEllDivSequence`. It is absent from mathlib, not composable from
existing lemmas, and the upstream API is already shaped to receive it.

**Recommended action:** PR this (with its private helpers `normEDS_mul_complEDS_of_mem`, the
`compl₂EDS`/`compl₂EDSAux`/`complEDS₂` machinery, `universalNormEDS*`, and the `IsDivSequence.normEDS`
/ `IsEllDivSequence.normEDS` corollaries) to
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, closing both file TODOs. Minor adaptation:
mathlib defines `complEDS` directly via `complEDS'`, whereas the project routes through the abstract
`compl`/`compl'` (over abstract `W₁ compl₂`); the `show … = compl (normEDS …) (compl₂EDS …)` step at
line 1326 bridges them, so the statement transfers verbatim but the surrounding helper definitions
must be reconciled with mathlib's (or `compl`/`compl'` introduced upstream as the general form). The
name is already mathlib-conformant.

### Evidence index
- Source decl: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1338`.
- Helpers: `…:1323` `normEDS_mul_complEDS_of_mem`; `…:1296`
  `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`; `…:1110` `def complEDS`; `…:1099`
  `def compl`; `…:1186` `universalNormEDS`.
- Downstream: `…:1437` `IsDivSequence.normEDS`; `…:1444` `IsEllDivSequence.normEDS`.
- Mathlib (pinned `09b373db6e24`),
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:
  `complEDS` def `:427`, docstring contract `:388-389`, **TODOs `:44-45`**,
  `normEDS_dvd_normEDS_two_mul` `:326`; no `normEDS_mul_complEDS`, no `IsDivSequence (normEDS)`
  anywhere in the tree.
- Literature: Ward, *Memoir on Elliptic Divisibility Sequences* (1948), Thms 12.1/19.1; Wikipedia
  "Elliptic divisibility sequence"; Stange, arXiv:0710.1316.
