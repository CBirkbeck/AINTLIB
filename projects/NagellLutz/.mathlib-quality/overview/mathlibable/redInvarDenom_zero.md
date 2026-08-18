# Mathlibable assessment — `EllSequence.redInvarDenom_zero`

**Verdict: NO-composable-from-mathlib**
(a trivial `@[simp]` base-case of a project-only definition; one-line `simp` from its own adjacent
API. See §6 for the *parent-layer* upstreaming question, which is the only genuinely human-facing call.)

- **Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)
- **File:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1412`
- **Qualified name (verified):** `EllSequence.redInvarDenom_zero`
  File-level `namespace EllSequence` (L90); re-opened inside `section Complement` (L1284) /
  `section Divisibility` (L1261) at L1356 (closed L1431). Declaration at L1412 sits in that
  `EllSequence` namespace; no enclosing namespace ⇒ full name `EllSequence.redInvarDenom_zero`.
- **Date:** 2026-06-21

---

## 1. Exact statement and proof (from source)

```lean
@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom, complEDS, compl', compl]
```

Scope: `{R} [CommRing R]`, `(b c d : R)`. The proof is a pure `simp` unfolding/computation — no
nontrivial mathematical content; it evaluates the bespoke definition at `m = 0` (the `m % 6 = 0`
branch, whose `W(0+1)·W(0-1)`-type factors collapse via the `normEDS`/`compl'` base values).

### The definition it evaluates

```lean
/-- The expression `W(m+1)W(m)W(m-1)/W₃W₂` for a normalised EDS. -/
def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2 -- W₆/W₃W₂
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  ... (six-way split on m % 6) ... else 0
```

It is the **denominator** `invarDenom (normEDS) 1 m = W(m+1)·W(m)·W(m-1)` of a Ward-style
elliptic-sequence invariant (`invarNum/invarDenom` is constant in `m`), with the common factor
`W₃·W₂ = b·c` cancelled and computed **division-free** via the project's `complEDS`/`compl`/`compl'`
complement machinery. The general identity is the sibling lemma
`invarDenom_eq_redInvarDenom_mul : invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`.

`redInvarDenom_zero` is one of three base-case `@[simp]` evaluations alongside
`redInvarDenom_one = 0` and `redInvarDenom_two = 1`.

### Role / consumers

Bespoke scaffolding for the **`ω` family of division polynomials** and the group-law
scalar-multiplication formulas:
- `LutzNagell/DivisionPolynomialOmega.lean` (`ψc`, `ω`, normalisation + `map_…` lemmas),
- `LutzNagell/ZSMul.lean:279` (`smulY`, the `Y`-coordinate of `[n]P`).
The `_zero` lemma exists purely to discharge `simp` goals in those downstream computations.

---

## 2. Literature search

- **WebSearch** ("elliptic divisibility sequence invariant W(n+s)W(n)W(n-s) denominator Ward
  division polynomial omega") returned the standard EDS corpus — Ward's *Memoir on Elliptic
  Divisibility Sequences* (the file's own cited reference), the EDS Wikipedia page, Stange's
  elliptic nets, Silverman/Streng-style valuation papers, the p-adic division-polynomial literature
  (arXiv:math/0404412). Ward-type EDS invariants are classical, **but the specific
  `W(n+s)·W(n)·W(n-s)` denominator, its `b·c`-reduced form `redInvarDenom`, and the division-free
  `% 6` `complEDS` evaluation are the project's own engineering**, not a named literature object.
  An evaluation-at-`0` of this construction is far below the granularity of anything in the
  literature.
- ChatGPT MCP: not consulted — unnecessary; the mathlib search below is decisive for a trivial
  base case of a private helper.

## 3. Mathlib search — five methods (against the in-tree pin `.lake/packages/mathlib`, EDS file dated 2026-06-17)

The pinned mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is itself already an
*expanded* EDS file (`complEDS₂`, `complEDS'`, `complEDS`, `complEDSRec`, `normEDS_mul_complEDS₂`,
the `map_*` family, …).

1. **Exact name** — `grep -rn "redInvarDenom"` over all `Mathlib/`: **0 hits**. The only file
   matching `complEDS`/`compl₂EDS` is the EDS file, which does **not** define `redInvarDenom`.
2. **Definition `redInvarDenom`** — absent. Mathlib's `complEDS` has a **different signature**
   (`complEDS b c d k n`, a two-index complement `W(n·k)/W(k)`); mathlib has **no** `compl₂EDSAux`,
   no `compl`/`compl'` (the project's `Int.sign · compl'` track), and no `invar*` track. This decl
   lives in the project's *forked/extended* EDS layer that has not been upstreamed.
3. **Concept `invarDenom`/`invarNum`/`redInvar`** — `grep -rln "invarDenom\|InvarDenom\|invarNum\|redInvar"`
   over all `Mathlib/`: **0 hits**. The invariant numerator/denominator machinery is absent under any
   synonym.
4. **Supported `ω` division-polynomial family** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`
   has only `Basic.lean` + `Degree.lean`; **no Omega/`ω` file**. The construction `redInvarDenom`
   feeds has no mathlib counterpart, so no host lemma exists for this to slot into.
5. **Statement shape** — a `*_zero` base-case rewriting a *named project definition* to `0`. By
   construction it cannot pre-exist in mathlib unless the definition does (it doesn't). A
   loogle/leansearch shape query (`?f _ _ _ 0 = 0`) would only return generic `_zero` simp-lemmas for
   *other* definitions, none equal to this.

**Search conclusion:** neither the declaration, nor its definition, nor the surrounding `invar`/`ω`
machinery exists anywhere in the pinned mathlib. The `complEDS` name-match is a **false friend**
(same name, different upstream definition with an extra index).

## 4. Generality analysis

Already maximal for what it is: `{R} [CommRing R]`, arbitrary `b c d`, evaluated at literal `0`.
Nothing to weaken — it is a closed-form value of a specific definition. "Generalising the index away
from `0`" is not a stronger lemma; it is the separately-proved general identity
`invarDenom_eq_redInvarDenom_mul`. So **not** `YES-but-generalise-first`.

## 5. Composition check (≤ 3 mathlib calls)

The lemma is not a corollary of mathlib *primitives*, because its subject (`redInvarDenom`, hence
`complEDS b c d`, `compl`, `compl'`, `normEDS`) is project-defined. But once those adjacent project
definitions are in hand, the proof is literally **one** `simp` unfolding —
`simp [redInvarDenom, complEDS, compl', compl]` — and carries no reusable, definition-independent
content. It is exactly the kind of local `@[simp]` evaluation lemma that must live beside its
definition. Hence **NO-composable-from-mathlib** (trivially composable from the project's own
immediately-adjacent API; nothing for mathlib to gain).

---

## 6. Verdict

**NO-composable-from-mathlib.**

`EllSequence.redInvarDenom_zero` is a one-line `@[simp]` base-case (`redInvarDenom b c d 0 = 0`) of a
**project-specific** definition absent from mathlib (the `invar`/`redInvar`/`ω` division-free
EDS-invariant machinery is the NagellLutz project's own fork-and-extend of the EDS /
division-polynomial files). It is not a standalone mathematical result, has no literature identity,
and is dischargeable in a single `simp` from its adjacent project definitions. It belongs next to
`redInvarDenom` in the project — **do not add to mathlib in isolation.**

### Human-facing caveat (the only BORDERLINE element — recorded, not blocking this leaf)

The *broader* `redInvarDenom`/`invarNum`/`invarDenom`/`ω` layer (of which this is a leaf) **is**
genuinely new relative to mathlib and could be a worthwhile upstreaming target as one coherent unit.
That is a curation decision about the **whole `invar`/`ω` machinery**, not about this trivial
base-case lemma. If and only if `redInvarDenom` itself is upstreamed, `redInvarDenom_zero` rides
along automatically as one of its `@[simp]` base cases. As an isolated declaration, this lemma's
verdict is unambiguous: NO-composable-from-mathlib.
