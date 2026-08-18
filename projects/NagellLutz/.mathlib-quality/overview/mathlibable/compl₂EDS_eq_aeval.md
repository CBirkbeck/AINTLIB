# Mathlibable assessment — `compl₂EDS_eq_aeval`

**Verdict: `NO-composable-from-mathlib`**

**Qualified name:** `compl₂EDS_eq_aeval` (root-level; `section Map` is not a namespace).

**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1191`

> Step-9 mathlibable assessment, NagellLutz project. Re-run 2026-06-21.

---

## 1. The declaration (verified from source)

```lean
lemma compl₂EDS_eq_aeval :
    compl₂EDS b c d =
      (aeval (Param.rec b c d) <| compl₂EDS (X (R := ℤ) B) (X C) (X D) ·) := by
  simp_rw [map_compl₂EDS, aeval_X]
```

Section context (lines 85–86, 1116–1118):
```lean
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)
...
section Map
variable {b c d}            -- b c d : R, from `variable (b c d : R)` higher up
```

Supporting infrastructure, all **project-local** (lines 1177–1194):
```lean
inductive Param : Type | B : Param | C : Param | D : Param
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)
lemma normEDS_eq_aeval  : normEDS  b c d = (aeval (Param.rec b c d) <| universalNormEDS ·)
lemma compl₂EDS_eq_aeval : compl₂EDS b c d = (aeval (Param.rec b c d) <| compl₂EDS (X B) (X C) (X D) ·)
lemma complEDS_eq_aeval : complEDS b c d = (aeval (Param.rec b c d) <| complEDS (X B) (X C) (X D) · ·)
```

**What it says (mathematics).** `compl₂EDS b c d` (the "2-complement" sequence — the witness of
`W(m) ∣ W(2m)` for a normalised EDS, with `b c d ∈ R`) equals the image, under the evaluation
`ℤ`-algebra map `aeval (Param.rec b c d) : MvPolynomial Param ℤ →ₐ[ℤ] R` (sending `X B ↦ b`,
`X C ↦ c`, `X D ↦ d`), of the **universal** 2-complement sequence `compl₂EDS (X B) (X C) (X D)`
living in `MvPolynomial Param ℤ`. It is the `compl₂`-instance of the universal-property / naturality
device used throughout the file to reduce identities about `normEDS`/`compl₂EDS`/`complEDS` over an
arbitrary ring to the universal polynomial ring, where every nonzero term is a non-zero-divisor (so
cancellation lemmas apply).

---

## 2. Literature search

EDSs (Ward's *Memoir on Elliptic Divisibility Sequences*) and the 2-complement / division-polynomial
witness are standard mathematics. But `compl₂EDS_eq_aeval` is **not a mathematical theorem** in the
literature: it is a *formalization device* — "specialize the universal/free object via the
polynomial-ring universal property (`aeval` at the generators)". WebSearch for the EDS-universal-`aeval`
pattern (arXiv 2604.05280 *On Elliptic Sequences over Commutative Rings*; 1101.3839; the mathlib EDS /
DivisionPolynomial doc pages) surfaces the underlying mathematics but nothing resembling this
naturality lemma — because it is plumbing, not a result. The generic underlying fact is the
**universal property of `MvPolynomial`** (`aeval` / `MvPolynomial.aeval_X`), which mathlib already has.

---

## 3. Mathlib search (5 methods; authoritative source = local cache)

The mathlib pin is present at `.lake/packages/mathlib/`. Searched the cached source directly
(more reliable than the index; `lean_loogle`/`lean_leansearch` were unavailable in this env).

- **Same-name / EDS file.** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) is
  the file this project FORKS. It contains the **same concept under a different name**:
  `complEDS₂` (line 246) = the project's `compl₂EDS` (renamed; mathlib defines it via `normEDS`,
  the project via `preNormEDS (b^4)`). It also has a full **`section Map`** (line 505) with the
  **general ring-hom pushforward** lemmas:
  ```lean
  variable {S} [CommRing S] (f : R →+* S)
  @[simp] lemma map_complEDS₂ (n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n
  @[simp] lemma map_normEDS  (n : ℤ) : f (normEDS  b c d n) = normEDS  (f b) (f c) (f d) n
  @[simp] lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n
  ```
- **`aeval` / universal forms.** `grep -rln "universalNormEDS|normEDS_eq_aeval|compl₂EDS_eq_aeval|complEDS_eq_aeval"`
  over all of `.lake/packages/mathlib/Mathlib/` → **zero hits.** `aeval` / `MvPolynomial` / `Param`
  counts in the EDS file and in `DivisionPolynomial/Basic.lean` → **0**. The `Param` /
  `universalNormEDS` / `_eq_aeval` device exists **only** in this project (and a partial copy in
  `projects/HasseWeil/.../EllipticDivisibilitySequence.lean`, which doesn't even define the
  `compl₂EDS` variant).
- **Conclusion of search:** mathlib has the *general* lemma (`map_complEDS₂`) and the *universal
  property* (`aeval_X`); it does **not** have this specialized corollary, and shouldn't need to.

---

## 4. Generality analysis

`compl₂EDS_eq_aeval` is **strictly less general** than `Mathlib.map_complEDS₂`:

| | ring hom | statement |
|---|---|---|
| `map_complEDS₂` (mathlib) | arbitrary `f : R →+* S` | `f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n` |
| `compl₂EDS_eq_aeval` (project) | the single hom `aeval (Param.rec b c d)` | `compl₂EDS b c d = aeval (Param.rec b c d) ∘ compl₂EDS (X B) (X C) (X D)` |

The project lemma is exactly `map_complEDS₂` instantiated at `f := aeval (Param.rec b c d)`, with
`aeval_X` collapsing `aeval (Param.rec b c d) (X B) = b` etc. Promoting a one-off specialization of
an existing general lemma into mathlib would be redundant API.

---

## 5. Composition check (≤ 3 mathlib calls)

**Yes — 2 mathlib calls.** The proof is literally:

```lean
simp_rw [map_compl₂EDS, aeval_X]
```

where the project's `map_compl₂EDS` **is** mathlib's `map_complEDS₂` (general pushforward), and
`aeval_X` is mathlib (`MvPolynomial.aeval_X`). So over a clean mathlib:

```
compl₂EDS_eq_aeval  =  map_complEDS₂ (at f := aeval (Param.rec b c d))  ∘  aeval_X
```

Two existing mathlib lemmas compose to give it directly. (The `Param` enumeration + `aeval` setup is
trivial scaffolding, not mathematical content.)

---

## 6. In-project signal

`compl₂EDS_eq_aeval` is **referenced nowhere** in the repository (grep across all `.lean`):
only `normEDS_eq_aeval` and `complEDS_eq_aeval` are actually used downstream. The HasseWeil duplicate
of this file omits the `compl₂` variant entirely. It is dead/redundant convenience even locally.

---

## 7. Verdict

**`NO-composable-from-mathlib`.**

- The concept (`complEDS₂`) and the general pushforward (`map_complEDS₂`) are **already in mathlib**.
- This lemma is a ≤3-call composition: `map_complEDS₂` specialized to `aeval (Param.rec …)` plus
  `aeval_X` — both mathlib.
- It is the universal-property reduction device (`aeval` at `X`), bespoke formalization plumbing,
  strictly less general than what mathlib provides, and unused even in-project.
- (Adjacent buckets considered: `NO-mathlib-has-it` slightly overstates — the *exact* `_eq_aeval`
  form is not literally present; but it is fully recovered by composing two mathlib lemmas, so the
  composability bucket is the precise call.)

**Rationale (≤20 words):** Mathlib has general `map_complEDS₂`; this is just it specialized to `aeval (Param.rec …)` plus `aeval_X` — two-call composition.
