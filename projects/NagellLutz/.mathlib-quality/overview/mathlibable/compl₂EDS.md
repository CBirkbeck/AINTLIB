# /mathlibable report — `compl₂EDS`

> **TL;DR — NO-mathlib-has-it.** The pinned mathlib (`09b373db6e24`, v4.32.0-rc1)
> already has this declaration verbatim as `complEDS₂` in
> `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`. The project file is
> a **fork** of that mathlib module: it even carries mathlib's `complEDS₂` *unchanged*
> at local line 844 (same docstring + body), while its live API uses a cosmetically
> renamed copy `compl₂EDS` at line 1031. Same ring, same definition, same companion
> lemma set. `compl₂EDS b c d k = complEDS₂ b c d k` holds by `rfl`.

(Re-confirms the earlier assessment of this decl on the prior pin; verdict unchanged on
the current mathlib pin.)

---

## Phase 0 — baseline

- **decl** `compl₂EDS` — resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1031`
- **kind:** `def` (data)
- **has sorry:** no
- **qualified name:** **`compl₂EDS`** (top-level). The enclosing `namespace EllSequence`
  (file line 90) closes at line 597; line 1031 sits in `section NormEDS` → `section Complement`,
  both *plain* `section`s. A namespace-stack walk over lines 1–1034 shows **zero open
  namespaces**, so the fully-qualified name is exactly `compl₂EDS`.
- **build:** not run (local build stale per task brief; reasoned from source + the shipped
  mathlib module, which the file is forked from).

## The declaration

```lean
section Complement
variable (b c d : R) (m : ℤ)

/-- The "complement" of W(m) in W(2m) for a normalised EDS W is the witness of W(m) ∣ W(2m). -/
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
```

`R` a `CommRing`, `b c d : R`, `m : ℤ`. `compl₂EDS b c d m` is the **2-complement**: the
explicit witness of `normEDS b c d m ∣ normEDS b c d (2 * m)`, i.e. `W(m) · Wᶜ₂(m) = W(2m)`,
written division-free at the `preNormEDS` level.

---

## Phase 1 — literature search

The 2-complement is the classical EDS **duplication identity**. For a normalised elliptic
divisibility sequence `W`, Ward's duplication formula is

> `W(2n)·W(2) = W(n)·(W(n+2)·W(n−1)² − W(n−2)·W(n+1)²)`,

so `W(2n)/W(n) = (W(n+2)W(n−1)² − W(n−2)W(n+1)²)/W(2)`. `compl₂EDS` is exactly this quotient,
with the trailing `if Even m then 1 else b` factor and the `b⁴`-parameter shift absorbing the
ring division by `W(2) = b`.

- Wikipedia, *Elliptic divisibility sequence* — gives `W₂ₙW₂ = Wₙ(Wₙ₊₂Wₙ₋₁² − Wₙ₋₂Wₙ₊₁²)` and
  the divisibility `W(n) ∣ W(2n)` — verbatim the content of `compl₂EDS` +
  `normEDS_mul_compl₂EDS` / `normEDS_dvd_two_mul`.
- M. Ward, *Memoir on Elliptic Divisibility Sequences* — the file's own cited reference; source
  of the duplication formula.
- *On Elliptic Sequences over Commutative Rings* (arXiv 2604.05280) — the commutative-ring
  generalisation behind the mathlib formalisation; matches the `CommRing R` setting here.

Standard, named, classical material — not novel to the project. (The *novel* content in this
section is the **general** n-complement `compl`/`complEDS`, not the 2-complement.)

## Phase 2 — mathlib search (five methods)

**Already in mathlib, verbatim.** Mathlib ships
`Mathlib.NumberTheory.EllipticDivisibilitySequence.complEDS₂`:

```lean
-- .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246
/-- The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for any `k ∈ ℤ`. -/
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
```

The only differences from local `compl₂EDS` are (i) bound variable `k` vs `m`, and (ii) the
local `letI p := preNormEDS (b ^ 4) c d` alias. After inlining `p` the body is
**character-for-character identical**; same `variable (b c d : R)` context; same
`if Even · then 1 else b` factor. Hence `compl₂EDS b c d k = complEDS₂ b c d k` by `rfl`.

**Smoking gun:** the local file *also* contains mathlib's `complEDS₂` **unchanged** at line 844
(identical docstring + body to mathlib line 246), alongside the renamed live copy at line 1031.
Two copies of one definition in the same file — one keeping mathlib's exact name. This is a pure
fork artefact.

The full companion lemma suite is mirrored (confirms same object, not coincidence):

| local (`compl₂EDS…`)     | mathlib (`complEDS₂…`)         |
|--------------------------|--------------------------------|
| `compl₂EDS_zero = 2`     | `complEDS₂_zero = 2`           |
| `compl₂EDS_one = b`      | `complEDS₂_one = b`            |
| `compl₂EDS_two = d`      | `complEDS₂_two = d`            |
| `compl₂EDS_neg`          | `complEDS₂_neg`               |
| `normEDS_mul_compl₂EDS`  | `normEDS_mul_complEDS₂`       |
| `normEDS_dvd_two_mul`    | `normEDS_dvd_normEDS_two_mul` |
| `compl₂EDS_mul_b`        | `complEDS₂_mul_b`             |

Five-method resolution:
- **Exact name** — `complEDS₂` found by name in the mathlib EDS file (31 references); the local
  `compl₂EDS` is the project's pre-rename spelling (`₂` before vs after `EDS`).
- **Statement / type** — identical `R`-valued `def` in `b c d m` (above).
- **`exact?`/`apply?` analogue** — `normEDS_mul_compl₂EDS` ≡ `normEDS_mul_complEDS₂`;
  `normEDS_dvd_two_mul` ≡ `normEDS_dvd_normEDS_two_mul`.
- **Loogle / leansearch** — the mathlib4 docs page for
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` lists `complEDS₂` with this exact docstring
  (confirmed via web search).
- **Library / module docstring** — the local file's own module docstring references `complEDS₂`
  (line 48), evidence the project knows the upstream name and is tracking a forked-then-renamed copy.

Provenance: header + `normEDSRec'`/`normEDSRec` are identical to mathlib's; author David Kurniadi
Angdinata. Mathlib copy has genuine upstream PR history (golf #38833, toolchain bumps). AINTLIB pin
is mathlib `09b373db6e24` on `v4.32.0-rc1`. The fork predates/parallels the upstream
`compl₂EDS → complEDS₂` rename; the project keeps the old spelling because it builds its general
complement track (`compl`, `compl'`, `complEDS`) on these names.

## Phase 3 — generality analysis

Local and mathlib definitions are at the **same** generality: arbitrary `CommRing R`, parameters
`b c d : R`, index `m/k : ℤ`. No assumption could be weakened or strengthened to distinguish them —
they are the same definition. Nothing to generalise.

## Phase 4 — composition check

`compl₂EDS` is a `def` (data), so the question is whether mathlib already provides the *object*, not
whether ≤3 lemma calls reconstruct it. It does, verbatim (`complEDS₂`), with its full API: witness
equation `normEDS_mul_complEDS₂`, divisibility `normEDS_dvd_normEDS_two_mul`, `*_mul_b`, special
values, `neg`. Nothing to compose — a consumer should `import` and use `complEDS₂` directly.

## Phase 5 — verdict: NO-mathlib-has-it

`compl₂EDS` is a byte-for-byte duplicate (modulo bound-variable name and a cosmetic `letI` alias) of
mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence.complEDS₂`, with the identical companion
lemma suite — and the project even keeps mathlib's `complEDS₂` verbatim in the same file (line 844).
This is a forked-file artefact, not new mathematics. **Do not submit.** When consolidating, the project
should depend on upstream `complEDS₂` (or treat `compl₂EDS` as a local re-export aligned to that name)
and drop the duplicate.

(For completeness: the genuinely new, potentially-mathlibable material in this section is the
**general** n-complement `compl`/`complEDS` and its theorems — assessed separately. `compl₂EDS`
itself is not new.)

---

### Evidence index
- Local renamed copy + API: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1016–1077`
- Local forked-in mathlib copy: `…/EllipticDivisibilitySequence.lean:844–846` (`complEDS₂`, verbatim mathlib)
- Mathlib decl + API: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246–340`
- Mathlib docs: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html>
- Duplication formula / divisibility: <https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence>
- M. Ward, *Memoir on Elliptic Divisibility Sequences* (file's cited reference)
