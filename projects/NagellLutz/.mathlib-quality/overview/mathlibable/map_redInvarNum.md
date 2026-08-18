# /mathlibable report — `EllSequence.map_redInvarNum`

> Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic divisibility sequences).
> Target: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (lemma at L1424; task-cited L1419 is the adjacent `redInvarDenom_two`).
> Full workflow. **Local build stale** — reasoned from source + mathlib source read directly from `.lake/packages/mathlib` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`).

---

## Verdict: **YES-add-as-is**

*Companion `map_*` naturality lemma; bound to its parent def `redInvarNum`. Ship them together (with `compl₂EDS`/`compl₂EDSAux` and ideally the whole `ωₙ` division-polynomial track that discharges mathlib's standing `ωₙ` TODO). Must NOT be PR'd alone.*

---

### Baseline (Phase 0)
- lake build:               n/a (stale per task; reasoned from source + mathlib source).
- decl `map_redInvarNum`:    ✓ resolved in `EllipticDivisibilitySequence.lean` (lemma body L1424–1426).
- **qualified name (VERIFIED):** `EllSequence.map_redInvarNum`.
  - The parsed guess `EllSequence.map_redInvarNum` is **correct**. Namespace trace: a top-of-file
    `namespace EllSequence` (L90) closes at `end EllSequence` (L597). A **second** `namespace EllSequence`
    (L1356) re-opens it; the lemma sits before its `end EllSequence` (L1431). Intervening
    `section Complement` / `variable` blocks add no name component. ⇒ root-qualified name is
    `EllSequence.map_redInvarNum` (no double `EllSequence.EllSequence`). Note this is **unlike** the
    sibling `map_compl₂EDS`/`map_compl₂EDSAux`, which live in a later `section Map` *outside* any
    namespace and are therefore root-level (`map_compl₂EDSAux`); `map_redInvarNum` is genuinely inside
    `EllSequence`.
- kind:                      lemma (theorem). **has sorry: no.**
- module docstring summary:  This file **forks + extends** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  and `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`; it develops the `ω` division-polynomial
  family and the "reduced invariant" (`invarNum`/`invarDenom` → `redInvarNum`/`redInvarDenom`) machinery
  used to prove Nagell–Lutz. Same author as the mathlib EDS file (David Angdinata).

---

### Statement (Phase 1)

`map_redInvarNum` states that the **reduced-invariant numerator** `redInvarNum` **commutes with any
ring homomorphism** `f : R → S`:

> For a ring hom `f`, ring elements `b, c, d : R`, and index `m : ℤ`,
> `f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m`.

where (def at L1364)
```lean
def redInvarNum (b c d : R) (m : ℤ) : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m
```
Its docstring (L1362–1363): *"The numerator of the reduced invariant expression
`(W(m-1)²W(m+2) + W(m-2)W(m+1)² + W₂²W(m)³)/W₂` for a normalised EDS W, obtained by cancelling
`W₃W₂ = b*c` from `invarNum`."* So `redInvarNum` is `invarNum (normEDS b c d) 1 m / b` made integral
(`invarNum_eq_redInvarNum_mul`: `invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`, L1372), and
this reduced numerator is exactly the numerator of the **`ωₙ` division polynomial** in `normEDS` form.

Variables / typeclasses (Lean side, from file header L85–86):
- `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` — source/target commutative rings.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — a ring homomorphism in **bundled-class** form.
- `(b c d : R)` (made explicit by `variable (b c d)` at L1360), `(m : ℤ)` — the EDS parameters + index.

Hypotheses: none beyond the typeclasses.

Proof (2 lines, L1425–1426):
```lean
simp only [redInvarNum, map_add, map_mul, map_pow, map_compl₂EDS, map_normEDS,
  map_compl₂EDSAux, map_ofNat]
```
i.e. unfold the def and push `f` through `+`, `*`, `^`, the literal `2`, and the three building blocks
via their own `map_*` lemmas: **`map_normEDS`** (a *mathlib* lemma) + **`map_compl₂EDS`**,
**`map_compl₂EDSAux`** (project lemmas, themselves naturality companions).

---

### Size classification (Phase 2)

Verdict: **SMALL** (companion lemma). A `map_*` naturality lemma for one def; 2-line `simp only` proof;
not a named theorem, not a structure. **Its fate is bound to its parent def `redInvarNum`.**
Kind is `lemma`, not `def` ⇒ one-liner-`def` check n/a. (Literature width still run wide because the
*parent* object is a classical division polynomial.)

---

### Literature search (Phase 3)

The lemma itself ("ring hom commutes with `redInvarNum`") is Lean infrastructure with no standalone
literature identity; the search targets the **parent object** — the `ωₙ` division polynomial / reduced
EDS invariant — which is what decides whether the companion `map_*` is mathlib-worthy.

| #  | Channel                       | Query / action                                                                                  | Hit? | Standard form found | Notes |
|----|-------------------------------|--------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific)          | "elliptic divisibility sequence invariant numerator division polynomial ring homomorphism functoriality" | yes | `ωₙ = (ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²)/(4y)`; EDS `W` of division-polynomial type | classical Silverman/Washington/Ward form; the `(W(m-1)²W(m+2)+W(m-2)W(m+1)²+…)` numerator in the docstring is exactly the `ωₙ` numerator |
| 2  | WebSearch (EDS background)    | EDS recursion `W_{n+m}W_{n-m}W_r² + … = 0`; Ward's `Wₙ = λ^{n²-1}ψₙ`                              | yes  | EDS over an integral domain; `ψₙ`/`ωₙ`/`φₙ` over a Weierstrass model | Wikipedia "Elliptic divisibility sequence"; arXiv math/0404412 (p-adic props of division polys & EDS); arXiv 0710.1316 (elliptic nets) |
| 3  | WebSearch (named-after)       | covered by #1/#2 — concept is just "the ω division polynomial" / "reduced EDS invariant"          | yes  | same; no person-name attached to the *reduced* numerator | the reduction `÷W₂` (cancel `W₃W₂=bc`) is a normalisation bookkeeping step, not a named theorem |
| 4  | ChatGPT MCP                   | standard form + generality of the `ωₙ` numerator                                                  | n/a  | — | MCP down per task; substituted by arXiv/textbook hits #1/#2 which already pin the standard form and its generality (any comm ring via the universal curve) |
| 5  | Local references              | `ls projects/NagellLutz/.mathlib-quality/references/`                                              | n/a  | — | directory absent (`.mathlib-quality/` has only `overview/`) — recorded n/a |
| 6  | nLab / Stacks                 | "division polynomial" / "elliptic divisibility sequence"                                          | n/a  | — | no dedicated `ωₙ`/EDS recurrence page; concept is classical-AG, covered by textbooks |
| 7  | MathOverflow / MSE            | "omega division polynomial second coordinate" generality                                          | yes  | `[n]P=(φₙ/ψₙ², ωₙ/ψₙ³)`, over any base ring | matches the universal-curve approach mathlib uses |

**Summary.** The parent object is the **`ωₙ` (omega) division polynomial numerator**, equivalently the
*reduced invariant numerator* of a normalised EDS — classical, and **defined over an arbitrary
commutative ring** via the universal Weierstrass curve (exactly mathlib's `WeierstrassCurve` setting;
the project builds directly on mathlib `preΨ₄`/`Ψ₃`/`Ψ₂Sq`/`ψ₂`/`ψ`/`φ`). `map_redInvarNum` is the
assertion that this numerator is **natural in the coefficient ring**. No literature disagreement — a
polynomial defined uniformly over all coefficient rings is automatically functorial.

---

### Generality analysis (Phase 4)

Literature-standard form: the `ωₙ`-numerator over an arbitrary commutative ring; a ring hom carries it
to the corresponding numerator over the target ring.

| # | Parameter / hypothesis                      | Current Lean form          | Literature-standard | Weaker form? | Reason |
|---|---------------------------------------------|----------------------------|---------------------|--------------|--------|
| 1 | `[CommRing R] [CommRing S]`                 | commutative rings          | arbitrary comm ring | NO           | `normEDS`/`compl₂EDS`/`compl₂EDSAux` use subtraction in the recurrence; cannot drop to semiring |
| 2 | `{F} [FunLike F R S] [RingHomClass F R S] (f)` | bundled ring-hom class  | a ring homomorphism | NO — already maximal | `RingHomClass F R S` is the most general "ring hom" form: it subsumes `R →+* S` and every bundled subclass (algebra homs, …). Strictly **more general** than mathlib's own EDS map-lemmas, which use the concrete `f : R →+* S`. |
| 3 | `(b c d : R)`, `(m : ℤ)`                     | three ring params + ℤ index| same                | NO           | intrinsic to the def; EDS are ℤ-indexed (`m-2`, `m+1` need subtraction) |

**Generality verdict:** **MAXIMALLY GENERAL** — in fact *more* general than mathlib's sibling map-lemmas
(`map_preNormEDS`/`map_normEDS`/`map_complEDS₂`/`map_complEDS` all use `R →+* S`; this uses
`RingHomClass F`). 0 weakening opportunities. **Modern-idiom check:** no gap — this is already the
mathlib idiom (a `map_*` naturality lemma stated with `RingHomClass`). The only nicety vs. mathlib's
siblings is the missing `@[simp]` attribute (mathlib's `map_normEDS` etc. carry `@[simp]`) — a cleanup
item before upstreaming, not a generality issue.

> NB: the *parent* `redInvarNum` is separately ledgered **YES-but-generalise-first**. That refers to the
> **def's** packaging (e.g. could be phrased as `invarNum/W₂` or unified with the `ωₙ` numerator), not to
> the map-lemma. Whatever final shape the def takes upstream, it will still need this naturality companion;
> the *lemma* needs no generalisation of its own.

---

### Diamond / defeq risk (Phase 4.5)
**n/a — kind is `lemma`** (introduces no defeqs, instances, or typeclass-search paths). The parent
`def redInvarNum` is a sealed expression over `compl₂EDS`/`normEDS`/`compl₂EDSAux` with no
`@[reducible]`, no instance, no coercion ⇒ its own risk is NONE/LOW, but that is a separate decl.

---

### Mathlib search-status (Phase 5)

| Ch | Method | Query / action | Result |
|----|--------|----------------|--------|
| [A] | Lean-Finder / LeanSearch | "ring hom commutes redInvarNum", "naturality reduced EDS invariant / omega numerator" | no hits (mathlib index has no such name; not exposed as MCP here — fell back to authoritative source grep [D]) |
| [B] | Loogle | `f (redInvarNum _ _ _ _) = redInvarNum _ _ _ _` | no hits — `redInvarNum` is not a mathlib name |
| [D] | **Grep mathlib src (authoritative)** | `grep -rn "redInvarNum\|invarNum\|compl₂EDSAux\|compl₂EDS\|EllSequence" .lake/packages/mathlib/Mathlib/` | **0 hits** for `redInvarNum`, `redInvarDenom`, `invarNum`, `invarDenom`, `compl₂EDSAux`, `compl₂EDS`, and no `EllSequence` namespace anywhere in mathlib |
| [D'] | Grep mathlib EDS `section Map` | `grep -nE "map_preNormEDS\|map_normEDS\|map_complEDS₂\|map_complEDS"` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` | **HITS** L510/522/526/530/534/544 — the *sibling family* exists; this exact member does not |
| [D''] | Grep mathlib `ωₙ` | `grep -n "ω\|TODO" Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` | `ωₙ` is an **explicit TODO**: L71 *"TODO: the bivariate polynomials `ωₙ`"*, L83 *"TODO: implementation notes for the definition of `ωₙ`"* (with the defining formula sketched at L28–37) |
| [E] | Name pattern | `map_redInvarNum`, `redInvarNum`, `EllSequence.*` over mathlib | no hits |

Searched for **both** the user's current form (`map_redInvarNum`) and the literature-standard parent
(the `ωₙ`-numerator naturality). **Conclusion: NOT in mathlib.** Mathlib has the *convention and the
siblings* — its `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` `section Map` (L507–544) gives
**every** EDS building block a `@[simp] map_*` naturality lemma (`map_preNormEDS'`, `map_preNormEDS`,
`map_complEDS₂`, `map_normEDS`, `map_complEDS'`, `map_complEDS`), and `DivisionPolynomial/Basic` does the
same (`map_Ψ`, `map_Φ`, `map_ψ`, `map_φ`). But it has **no** `redInvarNum`, because the object it is a
numerator of — `ωₙ` — **is itself absent from mathlib** (the standing TODO). So `map_redInvarNum` is the
*missing member of an existing family*, blocked only by the missing `ωₙ` track.

> **Important — this is not "mathlib has it" (≠ `NO-mathlib-has-it`).** The superficially-similar ledger
> entries `map_normEDS` and `map_compl₂EDS` are `NO-mathlib-has-it`, but for different reasons:
> `map_normEDS` is *literally in mathlib* (L530); `map_compl₂EDS` is a project naturality lemma for the
> ℤ-indexed `compl₂EDS` whose **value** mathlib already provides through `complEDS₂` (the ℕ-indexed
> twin) + `map_complEDS₂`. Neither applies here: `redInvarNum` has **no** mathlib analogue at all, so
> `map_redInvarNum` genuinely adds new content.

---

### Call sites (Phase 6.0)

`map_redInvarNum` internal/external uses:
- **In-file:** consumed inside the proof of `invar_normEDS` (`EllipticDivisibilitySequence.lean:~1505`,
  via `simpa only [map_redInvarNum, …]` in the universal-curve `aeval` transfer).
- **Cross-repo twin:** the **same lemma is independently restated in HasseWeil** —
  `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:931`
  (`lemma map_redInvarNum : redInvarNum (f b) (f c) (f d) m = f (redInvarNum b c d m)`, equation
  flipped), used at L1001 (`map_redInvarNum (X B) (X C) (X D) m`) in *its* universal-curve transfer.
  This is the **forked General/PID-track duplication** the task flagged: the NagellLutz EDS file and the
  HasseWeil `Auxiliary` EDS file are two copies of the same Angdinata development. **That is an
  intra-repo dedup matter (one canonical copy), NOT evidence that "mathlib has it."**

Inline-derivation grep (was it re-derived without the lemma?): no — every consumer `simp`/`simpa`s with
it; nobody re-expands `redInvarNum` by hand. (`EllipticDivisibilitySequenceOriginal.lean` is a
pre-refactor snapshot of the same file, not an independent derivation.)

**Composability signal:** a `map_*` `simp`-lemma consumed by universal-curve `aeval`-transfer proofs in
*two* projects — real naturality API, used exactly as mathlib's `map_normEDS`/`map_complEDS₂` are used to
build `map_ψ`/`map_Ψ`. → leans **YES-*** (bound to parent).

### Composition check (Phase 6)

Can `map_redInvarNum` be obtained from mathlib in ≤3 chained calls **without introducing a lemma**?

- Attempt: `by simp only [redInvarNum, map_add, map_mul, map_pow, map_compl₂EDS, map_normEDS, map_compl₂EDSAux, map_ofNat]`.
  - Mathlib decls used: `map_add`, `map_mul`, `map_pow`, `map_ofNat`, and **`map_normEDS`** (mathlib).
  - **But** it also requires `map_compl₂EDS` and `map_compl₂EDSAux` — naturality lemmas for two defs
    (`compl₂EDS`, `compl₂EDSAux`) that **do not exist in mathlib**. And the whole `simp only` is driven by
    unfolding `redInvarNum`, a name that exists only once `redInvarNum` is a mathlib def.
  - **Result:** succeeds as a *proof*, but is **not a call-site-inlinable mathlib redundancy**: it presupposes
    three project defs (`redInvarNum`, `compl₂EDS`, `compl₂EDSAux`) being upstreamed, and mathlib's house
    style gives *every* such def its own `@[simp] map_*` companion rather than re-`simp`-unfolding at each
    use site.

**Conclusion: NOT-COMPOSABLE as a stand-alone redundancy.** Modulo its parent + sibling defs it is a
2-line `simp`, but it is the canonical companion `map_*` lemma, not an inline-able accident. Its inclusion
question is **identical to its parent def's** (verdict inheritance).

---

## Verdict — `EllSequence.map_redInvarNum`

**Category: YES-add-as-is** — *bound to its parent def `redInvarNum`; ship them together (with
`compl₂EDS`/`compl₂EDSAux` and ideally the `ωₙ` track that discharges mathlib's `ωₙ` TODO). Do NOT PR it
alone.*

**Evidence:**
- **Literature (Phase 3):** parent is the classical **`ωₙ` division-polynomial numerator** = reduced EDS
  invariant numerator, standard over any commutative ring; `map_redInvarNum` is its expected naturality
  lemma. No disagreement. Sources: leanprover-community `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  docs; Wikipedia *Elliptic divisibility sequence*; arXiv `math/0404412`, `0710.1316`, `1108.3051`.
- **Generality (Phase 4):** **MAXIMALLY GENERAL** — uses `RingHomClass F R S`, *more* general than
  mathlib's own sibling `map_*` EDS lemmas (which use `R →+* S`). No modern-idiom gap. (Only nit: add
  `@[simp]` to match mathlib siblings.)
- **Mathlib search (Phase 5):** **not in mathlib** — `redInvarNum`/`compl₂EDS`/`compl₂EDSAux` all absent
  (grep = 0), no `EllSequence` namespace in mathlib; the object `ωₙ` is an explicit mathlib TODO
  (`DivisionPolynomial/Basic.lean:71,83`). The sibling family `map_preNormEDS`/`map_normEDS`/
  `map_complEDS₂`/`map_complEDS` exists (`EllipticDivisibilitySequence.lean:507–544`) — this is the
  missing member.
- **Composition (Phase 6):** **NOT-COMPOSABLE** as a redundancy — canonical companion `map_*` lemma; real
  consumers (in-file `invar_normEDS`, plus a cross-repo twin in HasseWeil), no inline re-derivation.

**Rationale.** `map_redInvarNum` is a *glue/companion lemma* whose inclusion is inseparable from its
parent `def redInvarNum`. Mathlib has an established, explicit **convention** — its EDS `section Map`
gives every building block a `@[simp] map_*` naturality lemma, and `DivisionPolynomial/Basic` does the
same for `Ψ/Φ/ψ/φ`. `redInvarNum` is a genuinely new member of this family (the numerator of the `ωₙ`
division polynomial in `normEDS` form, obtained by cancelling `W₃W₂` from `invarNum`), and **mathlib does
not have `ωₙ` at all** — it is a standing TODO whose defining formula is already sketched in the mathlib
docstring (`DivisionPolynomial/Basic.lean:28–37, 71, 83`). The project implements exactly that `ωₙ`
(`DivisionPolynomialOmega.lean`, `def ω`) on top of mathlib's `preΨ₄`/`Ψ₃`/`Ψ₂Sq`/`ψ₂`/`ψ`/`φ`. When that
`ωₙ` work is upstreamed (discharging the TODO), `redInvarNum` goes with it, and — by mathlib's own
convention — so must its `@[simp] map_*` companion. The lemma is at the right (in fact maximal)
generality, has a clean 2-line proof reusing the mathlib lemma `map_normEDS`, and is used precisely the
way mathlib uses `map_normEDS` to build `map_ψ`. It is **not** independently mathlib-worthy in isolation —
a `map_*` lemma for a def that isn't in mathlib makes no sense alone — which is why the verdict is
explicitly *bound to the parent*.

**WHY add it (refactor-actionable):**
- **New content + named mathlib gap:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
  lists `ωₙ` as a TODO (L71, L83). `redInvarNum` is the `normEDS`-form numerator of that missing `ωₙ`, and
  `map_redInvarNum` is the naturality lemma the eventual `map_ω` will require — the project's `map_ω`
  (`DivisionPolynomialOmega.lean`) already lives in this ecosystem and the in-file `invar_normEDS` already
  consumes `map_redInvarNum`.
- **Composes with mathlib's API:** its proof already calls the mathlib lemma `map_normEDS`; once upstreamed
  it sits in the same `section Map` next to `map_normEDS`/`map_complEDS₂` and feeds the `map_ω`/`map_Ψ`-style
  naturality lemmas, completing the `map_*` family for the ω track.

**Proposed mathlib location:** alongside the `ωₙ` implementation —
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (the `ωₙ` def + its `map_*`), **or**
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` `section Map` if `redInvarNum`/`compl₂EDS`/
`compl₂EDSAux` are upstreamed first as pure-EDS auxiliaries (they use only `preNormEDS`/`normEDS`, so they
can live in the EDS file next to `map_complEDS₂`).

**PR grouping (REQUIRED — the right grain):** ship `map_redInvarNum` **in the same PR as**
  1. its parent `def redInvarNum` (mandatory — the lemma is meaningless without it),
  2. the sibling building blocks it unfolds to: `def compl₂EDS`, `def compl₂EDSAux` + their `map_*`
     companions `map_compl₂EDS`, `map_compl₂EDSAux` (the proof needs them), and
  3. ideally the broader `ωₙ` track discharging the `DivisionPolynomial/Basic` TODO (`def ω`, `map_ω`,
     `redInvarDenom`/`map_redInvarDenom`, `invarNum`/`invarDenom`, …) — one coherent contribution.

**Pre-PR checklist:**
  - [ ] Assess/upstream the **parent** `redInvarNum` first (`/mathlibable redInvarNum` → ledger says
        *YES-but-generalise-first*; resolve the def's packaging before adding the companion). Its verdict
        gates this lemma.
  - [ ] Likewise gate on `compl₂EDS` / `compl₂EDSAux` (and `map_compl₂EDS` / `map_compl₂EDSAux`) being
        upstreamed — the proof depends on them.
  - [ ] **Dedup across the repo first:** `map_redInvarNum` is duplicated in HasseWeil
        (`Auxiliary/EllipticDivisibilitySequence.lean:931`, equation flipped). Pick one canonical copy /
        statement orientation before upstreaming — this is a `lane:cleanup` dedup, not an upstream blocker
        but should precede the PR.
  - [ ] Add `@[simp]` to match mathlib's sibling convention (`map_normEDS`/`map_complEDS₂` carry `@[simp]`;
        this copy does not).
  - [ ] Reviewer: a recent `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` committer (the
        division-polynomial / EDS author, David Angdinata).

---

## Next step
Do **not** PR `map_redInvarNum` alone. Treat it as a companion of `redInvarNum`: first run
`/mathlibable redInvarNum` (resolve its *generalise-first* verdict) and the `compl₂EDS`/`compl₂EDSAux`
assessments; dedup the HasseWeil twin to a single canonical copy. When the parent (and ideally the full
`ωₙ` implementation discharging mathlib's `DivisionPolynomial/Basic.lean:71` TODO) is upstreamed, include
`map_redInvarNum` in that same PR, `@[simp]`-tagged, next to the existing `map_normEDS`/`map_complEDS₂`
family.
