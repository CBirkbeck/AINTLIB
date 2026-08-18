# /mathlibable report — `WeierstrassCurve.baseChange_preΨ`

> **Name note.** The /overview triage passed base name `baseChange_preΨ₄` for the
> declaration *at line 492*. That is a parse artifact: line 492 is the **proof body**
> of `baseChange_preΨ` (the ℤ-indexed lemma, head on line 491). The actual
> `baseChange_preΨ₄` lemma is a *different* declaration at line 485. This report
> assesses the declaration whose proof is at line 492, i.e.
> **`WeierstrassCurve.baseChange_preΨ`** (the ℤ-indexed one). The verdict below
> applies verbatim to `baseChange_preΨ₄`, `baseChange_preΨ'`, and every other lemma
> in this `section BaseChange` as well — they are all the same verbatim fork (see
> "Scope" at the end).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; assessment reasons from source — both project and mathlib source read directly)
- decl `WeierstrassCurve.baseChange_preΨ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:491` (proof body line 492)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a **copy** of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation." (lines 12–16)

The module docstring is itself dispositive: the file announces it is a fork of a
named mathlib file. Phase 5 only needs to confirm the specific lemma survived the
copy unchanged — it did.

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_preΨ` is a **naturality/compatibility lemma** stating
that the (pre-normalised) division polynomial `preΨ n` commutes with base change
along an `S`-algebra homomorphism `f : A →ₐ[S] B`.

Concretely: let `W` be a Weierstrass curve over a commutative ring `R`, let `A` and
`B` be `R`-algebras that are also `S`-algebras with `R → S → A` and `R → S → B`
scalar towers, and let `f : A →ₐ[S] B`. Then base-changing `W` to `B` and forming
its `n`-th pre-division polynomial equals base-changing `W` to `A`, forming `preΨ n`
there, and then pushing the *coefficients* forward along `f` (via `Polynomial.map`).
In a square: `preΨ` of the `B`-curve = `(map f) ∘ preΨ` of the `A`-curve.

This is the standard "division polynomials are defined over the base and respect
ring maps" fact, restricted from a bare ring hom (the `map_preΨ` version) to an
`S`-algebra hom between two `R`-algebras (the `baseChange` version).

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]`, `(W : WeierstrassCurve R)` — the base curve.
- `[Algebra R S]` and the tower `{A} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]`, likewise `{B}` — two algebras in an `R → S → ·` tower.
- `(f : A →ₐ[S] B)` — the `S`-algebra hom along which we base-change.

Hypotheses (Lean side): none beyond the typeclass context; `(n : ℤ)` is the index.

Conclusion (math): the base-change square for `preₙΨ` commutes.

Conclusion (Lean): `(W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f`.

Proof (verbatim, line 492): `rw [← map_preΨ, map_baseChange]` — i.e. rewrite
`preΨ` of the base-changed curve through the bare-ring-hom naturality lemma
`map_preΨ` and the curve-level `map_baseChange`. Two-rewrite reduction to the
already-proved `map_*` layer.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A specialisation/corollary of the `map_preΨ` naturality lemma; not a named
theorem, not a new structure, not a `## Main results` entry. It is one of a dozen
mechanical `baseChange_*` wrappers generated from the `map_*` layer.

(Literature width is nominally EXHAUSTIVE, but see the framing note below: the
decl is a byte-identical copy of an existing mathlib lemma, so the literature
question — "is this the right standard form?" — is already answered by mathlib
having merged it. The lit channels are recorded for completeness but the verdict
does not turn on them.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rw [← map_preΨ, map_baseChange]`).
One-liner verdict: n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. The
one-line-*definition* gate does not apply to proof terms. (Recorded for the gate:
a one-line *proof* of a `lemma` is normal and carries no negative signal by itself.)

---

### Literature search (Phase 3)

**Framing.** This decl is a verbatim copy of a lemma that is *already in mathlib*
(see Phase 5). The literature question that /mathlibable normally answers — "what
is the standard form and is the Lean statement at the right generality?" — was
already adjudicated when David Angdinata's division-polynomial development was
reviewed into mathlib. The channels below are run for protocol completeness; none
can change a `NO-mathlib-has-it` verdict whose evidence is "mathlib contains the
identical declaration."

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" "base change" elliptic curve naturality          | n/a (web search not separately re-run — superseded) | — | The concept is classical (division polynomials of elliptic curves, Silverman AEC Ch. III/Exercise 3.7). Their compatibility with ring homomorphisms / base change is folklore: the polynomials have integer-coefficient universal formulas in `a₁..a₆`, so any ring map commutes with them. No web lookup can override mathlib already owning the decl. |
|  2 | WebSearch (general form)         | division polynomials defined over ℤ[a₁..a₆] universal                   | n/a — superseded | universal poly over `ℤ[a₁,…,a₆]` ⇒ commutes with all ring maps | This *is* the generality already captured by mathlib's `map_preΨ`; `baseChange_preΨ` is the algebra-hom specialisation of it. |
|  3 | WebSearch (named-after/aliases)  | "ψ_n" "division polynomial" functoriality                              | n/a — superseded | — | No eponymous name; it is infrastructure, not a theorem. |
|  4 | ChatGPT MCP                      | standard form + generality + history of division-poly base-change compat | n/a — MCP marked down in task env; reasoned from source instead | confirms universal-coefficient ⇒ functorial | The math is not in doubt; the question is purely "is it in mathlib", answered by Phase 5. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                 | n/a | (not consulted — verdict fixed by exact mathlib hit) | Even a perfect reference match cannot make a YES out of a decl mathlib already has. |
|  6 | nLab                             | division polynomial / elliptic divisibility sequence                   | n/a | — | nLab has no dedicated page; concept lives in AG/number-theory texts. Not load-bearing here. |
|  7 | nCatLab                          | —                                                                     | n/a | — | Not a categorical concept needing the higher-categorical channel. |
|  8 | Stacks Project                   | division polynomial                                                    | n/a | — | Stacks does not develop elliptic-curve division polynomials. Valid `n/a`. |
|  9 | MathOverflow / MSE               | division polynomial base change / reduction mod p compatibility        | n/a | folklore (universal formulae) | The fact is treated as obvious in the literature; no controversy over its form. |
| 10 | recent arXiv (≤5 yr)             | —                                                                     | n/a | — | A 1930s-era classical construction; no modern restatement relevant. |

### Literature summary (Phase 3)

Concept identified as: **base-change / functoriality of the elliptic-curve division
polynomial `preₙΨ`** (the pre-normalised `n`-division polynomial of a Weierstrass
curve). Standard, classical, expressed in mathlib via universal coefficient
polynomials.
Sources agree on the standard form: yes — division polynomials are defined by
universal formulae in the Weierstrass coefficients, hence commute with every ring
homomorphism; the algebra-hom/base-change version is the routine corollary.
Most general standard form: "for any ring hom, `preΨ` of the mapped curve = map of
`preΨ`" — which mathlib already states as `map_preΨ`, with `baseChange_preΨ` the
`A →ₐ[S] B` specialisation.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: division polynomials are functorial in the base ring.
Mathlib encodes the *maximally general* statement as `map_preΨ` (arbitrary
`f : R →+* S`); `baseChange_preΨ` is deliberately the **less general**
algebra-hom-in-a-tower specialisation, provided as ergonomic API for the
`baseChange` setting.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `(f : A →ₐ[S] B)` + scalar towers | `S`-algebra hom in an `R→S→·` tower | arbitrary ring hom | yes — `map_preΨ` (the bare-ring-hom form) is strictly more general | But this is **intentional**: mathlib ships *both*, `map_preΨ` as the general lemma and `baseChange_preΨ` as the `baseChange`-flavoured corollary. Generalising "away" the baseChange form would delete a deliberately-provided convenience lemma. |

### Generality verdict (Phase 4b)

The current form is: **a deliberate specialisation of the maximally-general
`map_preΨ`**, identical to mathlib's own `baseChange_preΨ`.
Number of weakening opportunities found: 0 actionable (the "more general" form is
`map_preΨ`, which mathlib *also* already has and which this fork *also* copies).
Proposed restatement: none — the decl is byte-identical to mathlib's.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses? | no | the `S`-algebra/tower context is already the idiomatic typeclass form | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic identity, no analysis | — |
| 3 | construction → universal property? | no | `preΨ` is a concrete polynomial; mathlib's chosen formulation | — |
| 4 | set+closure → bundled substructure? | no | — | — |
| 5 | field/metric → weaker typeclass? | no | already over a general `CommRing` | — |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index → general structure? | no | index is `ℤ`, intrinsic to division polynomials | — |

Modern idiom available: **no** — and crucially, even if one existed, it would be a
proposal for *mathlib's* version, not for this fork. mathlib already chose the
formulation. The fork must track mathlib, not diverge from it.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search
paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.baseChange_preΨ`

[A] Lean-Finder       n/a (mathlib index tool) — superseded by exact source hit below
[B] Loogle            type pattern `(W.baseChange _).preΨ _ = _` — superseded by exact source hit
[C] LeanSearch        "division polynomial base change map" — superseded by exact source hit
[D] **Grep mathlib src** `baseChange_preΨ` over `.lake/packages/mathlib/` → **HIT**
[E] Name pattern      `WeierstrassCurve.baseChange_preΨ` → **HIT** (same file)

**Direct source hit (decisive).** Mathlib contains the declaration verbatim:

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:568–569`
```lean
lemma baseChange_preΨ (n : ℤ) : (W⁄B).preΨ n = ((W⁄A).preΨ n).map f := by
  rw [← map_preΨ, map_baseChange]
```
(`W⁄B` is mathlib's notation for `W.baseChange B`.)

Project copy, `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:491–492`:
```lean
lemma baseChange_preΨ (n : ℤ) : (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f := by
  rw [← map_preΨ, map_baseChange]
```

These are the **same declaration**: same name `baseChange_preΨ`, same namespace
`WeierstrassCurve` (project opens `namespace WeierstrassCurve` at line 27; mathlib
likewise), **identical** `section BaseChange` variable context
(`[Algebra R S] {A …} [IsScalarTower R S A] {B …} [IsScalarTower R S B] (f : A →ₐ[S] B)`
— project line 473–474 == mathlib line 550–551), identical statement, identical
two-step proof. The project's own module docstring states the file is a copy of
exactly this mathlib file.

Searched for both:
  - the user's current form → identical hit (above).
  - the literature-standard (more general) form → also present in mathlib as
    `WeierstrassCurve.map_preΨ` (`Basic.lean:518`), which this fork also copies
    (project line 491's proof rewrites through it).

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_preΨ`; identical
form** (and the more-general `map_preΨ` is in mathlib too).

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.baseChange_preΨ`

Internal use count: **0** (whole-repo grep over `projects/`, excluding the
declaration line and excluding the distinct `baseChange_preΨ₄` / `baseChange_preΨ'`
lemmas, returns nothing).
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: none — the lemma is unused; it exists only because the
entire `Basic.lean` was copied wholesale to retarget its EDS import.

The `K = 0` call-site count reinforces the verdict: this lemma is not even consumed
inside NagellLutz. It is pure fork ballast. (Per Phase 6.0.1, `K = 0` with the
*identical thing present in mathlib* is the strongest NO signal.)

#### Composition attempt

Can `baseChange_preΨ` be derived from mathlib in ≤3 calls? **Yes, trivially —
it IS a mathlib lemma.** No composition needed: `exact WeierstrassCurve.baseChange_preΨ f n`
(or, since the fork only exists to dodge the `normEDS` name clash, the same two-line
proof `rw [← map_preΨ, map_baseChange]` against the mathlib `map_*` lemmas). This is
not "composable building blocks" — it is the literal lemma, so the verdict is
NO-**mathlib-has-it**, not NO-composable.

Conclusion: the result is *present in mathlib verbatim*; composition is moot.

---

## Verdict: `WeierstrassCurve.baseChange_preΨ`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): classical functoriality of division polynomials; the
  "right form" question was already settled when mathlib merged this development.
- Generality analysis (Phase 4): the decl is a *deliberate* specialisation of the
  more-general `map_preΨ`; both are already in mathlib. No weakening to propose.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.baseChange_preΨ`,
  byte-identical**, at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:568`.
- Composition check (Phase 6): 0 call sites in the project; the lemma is unused fork ballast.

**Rationale.**

The declaration is not a candidate for upstreaming because it is *already upstream,
unchanged*. `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` is, by its own
module docstring (lines 12–16), a verbatim copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The only reason
the copy exists is to retarget one import: NagellLutz maintains its *own* fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`
(`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, which redefines
`normEDS`, `complEDS`, …), so the division-polynomial file that depends on EDS had to
be copied too, dragging the entire `section BaseChange` along with it. `baseChange_preΨ`
is one of those dragged-along lemmas: same name, same `WeierstrassCurve` namespace,
identical `[Algebra R S] … (f : A →ₐ[S] B)` context, identical statement, identical
`rw [← map_preΨ, map_baseChange]` proof as mathlib `Basic.lean:568–569`.

So mathlib has the *exact* declaration (and also the strictly more general
`map_preΨ`). There is no gap to fill, no generalisation to ship, no composition to
inline — there is a duplicate to eliminate. The path to removing it is not a
NagellLutz-side edit to this one lemma; it is resolving the upstream EDS fork (below),
after which the whole copied `DivisionPolynomial.lean` can be deleted and replaced by
`import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

**WHY not (refactor-actionable).**
Mathlib already has it, verbatim.
- Existing mathlib decl: `WeierstrassCurve.baseChange_preΨ`
- Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:568`
- Our form follows in ≤1 line (it is literally the same lemma):
  ```lean
  example {R S A B : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
      [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
      [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
      (f : A →ₐ[S] B) (n : ℤ) :
      (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f :=
    WeierstrassCurve.baseChange_preΨ f n
  ```
- Call sites in our project (from Phase 6.0): **K = 0**.

**Refactor plan.**
1. This is not a one-lemma fix — `baseChange_preΨ` is unused (K = 0) and is part of a
   whole forked file. The lemma cannot simply be deleted in isolation while the rest
   of the fork stays, because the fork is copied as a unit (it would just be re-added
   on the next sync). Treat the *file* as the refactor target.
2. **Root cause = the EDS fork.** NagellLutz forks
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` into
   `LutzNagell/EllipticDivisibilitySequence.lean` (redefining `normEDS`/`complEDS`/…),
   which is *why* `DivisionPolynomial.lean` is a fork. The durable fix is to reconcile
   that EDS fork with mathlib's (file a dev ticket on `dev/nagell-lutz`):
   - If the fork no longer differs materially from mathlib's EDS → delete both forks
     (`EllipticDivisibilitySequence.lean` *and* `DivisionPolynomial.lean`) and replace
     their imports with the mathlib modules. `baseChange_preΨ` disappears with the file,
     resolving the duplicate at zero call-site cost.
   - If the fork still differs (e.g. the `module`/`public import` system migration, or
     a genuinely different `normEDS`) → that *difference* is the only thing worth
     assessing for mathlib; the `baseChange_*` wrappers are not. Run /mathlibable on the
     EDS *delta*, not on these copied division-polynomial lemmas.
3. Until the EDS fork is resolved, leave `baseChange_preΨ` as-is (it is harmless,
   sorry-free fork ballast). Do **not** open a mathlib PR for it.

**Next action:** Delete `WeierstrassCurve.baseChange_preΨ` from the project as part of
removing the forked `DivisionPolynomial.lean` once the upstream
`EllipticDivisibilitySequence` fork is reconciled with mathlib (file a dev ticket on
`dev/nagell-lutz` to do that reconciliation). No mathlib PR — mathlib already contains
the identical lemma at `DivisionPolynomial/Basic.lean:568`.

---

## Scope (whole `section BaseChange`)

`baseChange_preΨ` is representative, not special. The **entire**
`section BaseChange` (project lines 469–509: `baseChange_ψ₂`, `baseChange_Ψ₂Sq`,
`baseChange_Ψ₃`, `baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_preΨ`,
`baseChange_ΨSq`, `baseChange_Ψ`, `baseChange_Φ`, `baseChange_ψ`, `baseChange_φ`),
and indeed the whole file, is a byte-identical copy of mathlib `Basic.lean`
(lines 546–586 for this section). Every one of these lemmas independently earns
**NO-mathlib-has-it** for the same reason. They should be resolved together by
deleting the forked file, not lemma-by-lemma. The same conclusion applies to the
specific `baseChange_preΨ₄` named in the /overview triage handle (mathlib
`Basic.lean:562`).

---

## Next step

Delete `WeierstrassCurve.baseChange_preΨ` (and the whole forked `DivisionPolynomial.lean`)
once the upstream `LutzNagell.EllipticDivisibilitySequence` fork is reconciled with
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; file a dev ticket on
`dev/nagell-lutz` for that reconciliation. Do not open a mathlib PR — the identical
lemma already lives at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:568`.
