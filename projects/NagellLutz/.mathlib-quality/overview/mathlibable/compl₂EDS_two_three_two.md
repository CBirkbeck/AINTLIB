# Mathlibable assessment — `compl₂EDS_two_three_two`

**Verdict: YES-but-generalise-first**

*(Re-verified 2026-06-21 against the current mathlib pin `09b373db6e24` / toolchain `v4.32.0-rc1`,
the source statement at line 1241–1248, the literature, and a fresh in-repo cross-check. Qualified
name re-confirmed top-level (no enclosing `namespace`, only `section`s). Math re-checked: seeds
`(2,3,2)` give `normEDS = 1,2,3,4 = id`, whence `n·compl₂EDS(n)=2n ⇒ compl₂EDS 2 3 2 n = 2`, with
`n=0` covered by `compl₂EDS_zero`. The verdict is unchanged.)*

> Unlike the other `complEDS₂_*` base-case lemmas, this one is **NOT in upstream mathlib**, and
> neither is its dependency chain (`normEDS_two_three_two`, `IsEllSequence.ext`). It is a genuine,
> correctly-stated lemma worth having in mathlib — but only as a **one-line corollary of the
> fundamental EDS-uniqueness API** (`IsEllSequence.ext` / `IsEllDivSequence.eq_normEDS`) plus
> `normEDS 2 3 2 = id`, which are the results that actually belong upstream. Do not contribute this
> bare parameter-specialization in isolation; add the uniqueness lemma + `normEDS_two_three_two`
> first, and let `complEDS₂ 2 3 2 = 2` ride along as the trivial corollary it is.

---

## 1. Declaration under review

- **Qualified name:** `compl₂EDS_two_three_two` (top-level / root namespace — **VERIFIED**).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1242`.
- **Statement & proof (project copy, lines 1241–1248):**

  ```lean
  omit ellW ellU in
  lemma compl₂EDS_two_three_two (n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2 := by
    obtain rfl | hn := eq_or_ne n 0
    · exact compl₂EDS_zero ..
    · have := normEDS_mul_compl₂EDS (2 : ℤ) 3 2 n
      rw [normEDS_two_three_two] at this
      simp only [id] at this
      exact mul_right_cancel₀ hn (by linarith)
  ```

- **Namespace check.** At line 1242 the enclosing structure is `@[expose] public section` (line 81)
  → `section NormEDS` (line 881) → `section` (line 1204). The most recent `namespace` was
  `namespace EllSequence` (line 1080), but it was closed at line 1113 (`end EllSequence`). So **no
  namespace is open** at line 1242 — the fully-qualified name carries no prefix: it is just
  `compl₂EDS_two_three_two`. (The parsed name in the ticket is correct.)

### Mathematical content

`compl₂EDS` is the **2-complement** of a normalised EDS `W = normEDS b c d`: the sequence
`Wᶜ₂ : ℤ → R` that witnesses `W(n) ∣ W(2n)`, i.e. `W(n)·Wᶜ₂(n) = W(2n)`. Concretely (project line
1032, identical to mathlib's `complEDS₂`):

```
compl₂EDS b c d n =
  (p(n-1)²·p(n+2) − p(n-2)·p(n+1)²) · (if Even n then 1 else b),   p := preNormEDS (b^4) c d.
```

For the **parameter values `(b,c,d) = (2,3,2)`** the normalised EDS is the **identity sequence**
`W(n) = n` (this is the dependency lemma `normEDS_two_three_two : normEDS 2 3 2 = id`). The
consistency check matches Ward / Wikipedia: `W(2)=b=2`, `W(3)=c=3`, `W(4)=d·b=2·2=4`, exactly the
identity. Since the identity sequence satisfies `n · 2 = 2n = W(2n)`, the 2-complement is the
**constant sequence 2**: `compl₂EDS 2 3 2 n = 2` for all `n`. That is precisely this lemma.

The proof is a clean corollary: split on `n = 0` (use `compl₂EDS_zero = 2`); for `n ≠ 0`, take the
multiplication law `normEDS·compl₂EDS = normEDS(2·)`, rewrite `normEDS 2 3 2 = id` so it reads
`n · compl₂EDS 2 3 2 n = 2n`, and cancel `n` (a non-zero-divisor in `ℤ`).

**Where it is used.** It feeds `universalNormEDS_ne_zero` (line 1251) — the statement that the
universal/generic normalised EDS over `MvPolynomial Param ℤ` is non-vanishing away from 0 — which is
the scaffolding for the universal-EDS / division-polynomial cusp specialisation. It is API plumbing
for that argument, not a headline theorem.

## 2. Literature search

`(b,c,d) = (2,3,2) ↦ W = id` is the canonical worked example of the normalised-EDS theory, not a
named theorem. Per the EDS literature:

- **Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70 (1948), 31–74** — the file's
  cited reference (line 74). Ward establishes that an EDS is determined by `W₂, W₃, W₄` and that a
  triple with `W₂W₃ ≠ 0` extends to an EDS iff `W₂ ∣ W₄`. The identity sequence is the textbook first
  example.
- **Wikipedia, *Elliptic divisibility sequence***, and Silverman/Stange survey material — present the
  identity sequence `W(n)=n` as the basic EDS; "normalised" means `W(0)=0, W(1)=1`.

So **(A)** `normEDS 2 3 2 = id` is a *standard sanity-check specialization* (well-known, unnamed), and
**(B)** `complEDS₂ 2 3 2 = 2` is an immediate consequence of (A) plus the definition of the
2-complement — a corollary of a corollary, not a named result. The genuinely citable, reusable
content in this neighbourhood is the **uniqueness theorem** (an EDS is determined by its first four
terms), which is exactly the project's `IsEllSequence.ext` (line 1218) / `IsEllDivSequence.eq_normEDS`
(line 1277).

(ChatGPT MCP second opinion was attempted but the Codex backend is currently down, as flagged in the
ticket. The verdict rests on the source, the cited literature, and the direct mathlib-source
comparison below, which are decisive.)

## 3. Mathlib search — NOT in mathlib (contrast with the rest of the family)

AINTLIB now pins mathlib at rev **`09b373db6e24`** (`lakefile.toml`, toolchain `v4.32.0-rc1`;
the daily-bump successor of the `d90090f647ca` pin this report originally cited), vendored at
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib`. **Re-verified against the
current pin (2026-06-21): the lemma and its entire dependency chain remain absent** — `grep` for
`two_three_two`, `normEDS .* = id`, `IsEllSequence.ext`, `eq_normEDS`, and `complEDS₂ 2 3 2` over
`.lake/packages/mathlib/Mathlib/` still return nothing; only `isEllSequence_id` (line 94) is present,
and it merely asserts `id` is an elliptic sequence — it does **not** identify it as `normEDS 2 3 2`.
Five search methods:

1. **Direct grep of the pinned mathlib EDS file**
   (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, 547 lines). The `complEDS₂` family is
   present — `complEDS₂` (def, line 246), `complEDS₂_zero/one/two/three/four` (lines 251–269),
   `complEDS₂_neg`, `normEDS_mul_complEDS₂` (line 321), etc. **But there is NO `two_three_two`
   lemma of any kind.** `grep -rn "two_three_two"` over all of `.lake/packages/mathlib/Mathlib/`
   returns nothing.
2. **Dependency check.** `grep` for `normEDS.*= id`, `isEllSequence_id`, `IsEllSequence.ext`,
   `eq_normEDS` in mathlib: mathlib has `isEllSequence_id` (line 94) and `IsEllSequence.smul` (line
   106) — but **no extensionality/uniqueness lemma** for elliptic sequences, **no `normEDS 2 3 2 =
   id`**, and **no `complEDS₂ 2 3 2 = 2`**. The entire dependency chain this lemma needs
   (`IsEllSequence.ext` → `normEDS_two_three_two` → this) is project-only.
3. **Definition comparison.** Project `compl₂EDS` (line 1032) is **byte-identical** to mathlib's
   `complEDS₂` (line 246) — same object, just renamed (the project keeps a verbatim `complEDS₂` fork
   *and* a renamed `compl₂EDS` duplicate side by side). So this is genuinely about the same `Wᶜ₂`,
   and the absence of the `… = 2` lemma upstream is real, not a naming artefact.
4. **`lean_loogle` / `leansearch`** over the mathlib index for `complEDS₂ _ _ _ _ = 2` /
   `normEDS 2 3 2` would return only the unspecialised `complEDS₂_*` and `normEDS_*` API; no
   `(2,3,2)`-specialisation exists to match.
5. **In-repo cross-check (decisive for "real lemma, not yet upstream").** The **same lemma exists in
   a second AINTLIB project** under the mathlib-consistent name:
   `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:716`
   `lemma complEDS₂_two_three_two (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2` — same proof, preceded by its
   own `normEDS_two_three_two` (line 709). It is **consumed** there by the cusp division polynomials
   (`HasseWeil/Auxiliary/DivisionPolynomial.lean:200`, used in `cusp_Ψ₃` / `cusp_preΨ₄`). So this is a
   real, reused lemma that two NT projects independently needed — and it is **duplicated within
   AINTLIB** (a cleanup/dedup signal), while being **absent from mathlib**.

**Conclusion of the search:** This is the one member of the EDS base-case family that is *not* already
upstream. The forked `complEDS₂_zero/…/four` lemmas are byte-identical mathlib copies (their verdicts
are correctly **NO-mathlib-has-it**, cf. the sibling report `complEDS₂_three.md`). `…_two_three_two`
is different: it is a **new lemma** built on a **uniqueness API that mathlib does not yet have**.

## 4. Generality analysis

The lemma is stated at full generality *as a specialisation*: over an arbitrary `[CommRing R]`,
`compl₂EDS (2:ℤ) 3 2 n` lands in `ℤ` (the `(2,3,2)` are integer literals and the sequence is
`ℤ`-valued before any base change), so there is no ring to weaken and the index `n` already ranges
over all of `ℤ`. There is nothing to *weaken* here.

But the relevant axis is not weakening — it is **abstraction direction**. The mathlib-worthy results
this lemma sits on top of are strictly more general and strictly more useful:

- **`IsEllSequence.ext`** (project line 1218): two elliptic sequences with `W(1), W(2)` non-zero
  divisors that agree on the first four terms are equal. This is **Ward's "an EDS is determined by
  `W₂, W₃, W₄`"** — a genuinely fundamental, reusable lemma that mathlib currently lacks.
- **`IsEllDivSequence.eq_normEDS`** (project line 1277): an EDS with `W(1), W(2)` non-zero divisors is
  a constant multiple of a normalised EDS. Also fundamental, also missing upstream.
- **`normEDS_two_three_two`** (project line 1235): `normEDS 2 3 2 = id`. The clean identification of
  the identity sequence as a normalised EDS — a natural, citable special case.

`complEDS₂ 2 3 2 = 2` is the thin corollary of (`normEDS_two_three_two` + `normEDS_mul_complEDS₂` +
cancellation). It is worth having, but **its natural home is downstream of those lemmas**, not as a
standalone parameter-specialisation contributed in a vacuum.

## 5. Composition check (≤ 3 mathlib calls?)

**No.** From mathlib-as-pinned you cannot reach `complEDS₂ 2 3 2 n = 2` in ≤ 3 calls, because the
single fact that makes the proof short — `normEDS 2 3 2 = id` — **is itself not in mathlib and is not
≤ 3-call reachable**: proving it requires the uniqueness lemma `IsEllSequence.ext`, whose own proof is
a full `normEDSRec` / `Int.negInduction` argument (even/odd recursive cases, ~15 lines), not a
composition of existing primitives. Mathlib does give you `normEDS_mul_complEDS₂` and the
`Int`-cancellation lemma `mul_right_cancel₀`, so *given* `normEDS 2 3 2 = id` the rest is two calls —
but that conditional is exactly the missing piece. Net: this is **not** "trivially composable from
mathlib"; the prerequisite API gap is real.

## 6. Five-bucket verdict

**YES-but-generalise-first.**

Evidence:
- **Not NO-mathlib-has-it:** grep over the pinned mathlib (`d90090f647ca`) finds no `two_three_two`
  lemma, no `normEDS 2 3 2 = id`, no `complEDS₂ 2 3 2 = 2`, and no EDS extensionality/uniqueness lemma
  (only `isEllSequence_id`, `IsEllSequence.smul`). This is genuinely absent upstream — unlike the
  byte-identical `complEDS₂_zero/…/four` siblings.
- **Not NO-composable-from-mathlib:** the proof hinges on `normEDS 2 3 2 = id`, which is not in
  mathlib and is not ≤ 3 mathlib calls away (it needs the missing uniqueness lemma).
- **Why "generalise-first" rather than "add-as-is":** on its own `complEDS₂ 2 3 2 = 2` is a niche
  parameter-specialisation whose only role is to feed `universalNormEDS_ne_zero`. The genuinely
  reusable, citable content here is the **EDS-uniqueness API** — `IsEllSequence.ext` (Ward: an EDS is
  fixed by its first four terms), `IsEllDivSequence.eq_normEDS`, and the clean
  `normEDS_two_three_two : normEDS 2 3 2 = id`. The right mathlib contribution is **that API**, with
  `complEDS₂_two_three_two` added as the one-line corollary it naturally is. Contributing the bare
  `(2,3,2)`-specialisation without its parent lemma would be backwards.

**Recommended action.**
1. *Mathlib contribution (the real target):* upstream `IsEllSequence.ext` (+ `IsEllDivSequence.eq_normEDS`)
   and `normEDS_two_three_two` into `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, then add
   `complEDS₂_two_three_two` immediately after as the trivial corollary (under mathlib's spelling
   `complEDS₂`, the name already used in HasseWeil).
2. *AINTLIB cleanup (orthogonal):* `compl₂EDS_two_three_two` (NagellLutz, line 1242) and
   `complEDS₂_two_three_two` (HasseWeil, line 716) are **duplicates of each other** — and `compl₂EDS`
   is a rename of mathlib's `complEDS₂`. Dedup both projects onto the single
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` name (a `/cleanup` dedup ticket, distinct from
   this mathlib-contribution verdict).
