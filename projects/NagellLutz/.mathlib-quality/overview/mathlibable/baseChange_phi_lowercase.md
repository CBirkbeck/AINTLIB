# /mathlibable report — `WeierstrassCurve.baseChange_φ` (lowercase φ)

> FILENAME NOTE: the requested path `baseChange_φ.md` (U+03C6, lowercase phi) collides on this
> case-insensitive (APFS) filesystem with the pre-existing `baseChange_Φ.md` (U+03A6, uppercase
> Phi) — both map to the same inode. The uppercase-Φ report (for the sibling lemma at
> `DivisionPolynomial.lean:500`) already occupies that inode, so this lowercase-φ report is written
> here to avoid clobbering it. Same five-bucket verdict applies (`NO-mathlib-has-it`).

> One-line verdict: **NO-mathlib-has-it.** This is a *verbatim fork* of
> `WeierstrassCurve.baseChange_φ` from
> `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:583`.
> Same statement, same proof, same `φ` definition. The whole file is, by its own docstring,
> "a copy of `Mathlib...DivisionPolynomial.Basic`".

---

### Baseline (Phase 0)
- lake build:               not run (sandbox build stale; reasoned from source — decl text + deps confirmed by grep).
- decl `WeierstrassCurve.baseChange_φ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:506`.
  (The prompt cited line 513, which lands in/just after this `BaseChange` block; the lemma by base name
  `baseChange_φ` is line **506**. Note the lowercase-φ vs uppercase-Φ sibling pair: `baseChange_Φ` is line 500.)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
  that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.)."

Qualified name resolves cleanly: the file opens `namespace WeierstrassCurve` (line 27) and closes it at line 511,
with no intervening namespace; `φ` is `protected noncomputable def φ` directly in that namespace (line 371). So the
fully-qualified name is **`WeierstrassCurve.baseChange_φ`** (the `section BaseChange` does not add to the name path).
Matches the prompt's guessed `WeierstrassCurve.baseChange_φ`.

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_φ` is a *functoriality / naturality* lemma for the **bivariate** division-polynomial
numerator `φₙ ∈ R[X][Y]` of a Weierstrass curve under base change along an algebra homomorphism.

Setup: `R` a commutative ring, `W : WeierstrassCurve R`; `S` an `R`-algebra; `A, B` two `S`-algebras that are also
`R`-algebras compatibly (`[IsScalarTower R S A]`, `[IsScalarTower R S B]`); and an `S`-algebra homomorphism
`f : A →ₐ[S] B`. Then base-changing `W` to `B` and forming `φₙ` equals base-changing `W` to `A`, forming `φₙ`, and
pushing its coefficients along `f` **lifted to the bivariate ring** via `mapRingHom f`:

  $$(W_B).\varphi_n \;=\; \big((W_A).\varphi_n\big).\mathrm{map}\,(\mathrm{mapRingHom}\,f) \qquad (n \in \mathbb Z).$$

Here `φₙ ∈ R[X][Y]` is the bivariate numerator of the `x`-coordinate of `[n]` (note: this is the lowercase-φ object,
living in `R[X][Y]`, transported by `mapRingHom f`; contrast the uppercase `Φₙ ∈ R[X]`, the univariate version,
transported by plain `f`). The lemma is the `φ`-instance of the general principle that division polynomials, being
built from *universal* integer recurrences in the Weierstrass coefficients `aᵢ`, commute with every ring map.

Variables / typeclasses (Lean side):
- `R S A B : Type _` `[CommRing _]` — coefficient rings.
- `[Algebra R S]`, `[Algebra R A]`, `[Algebra S A]`, `[Algebra R B]`, `[Algebra S B]` — algebra structures.
- `[IsScalarTower R S A]`, `[IsScalarTower R S B]` — compatibility so `W.baseChange A`, `W.baseChange B` make sense.
- `W : WeierstrassCurve R` — the curve.
- `f : A →ₐ[S] B` — the algebra hom; `mapRingHom f` is its lift to `R[X][Y]`.

Hypotheses: none beyond the typeclass context; `n : ℤ` is universally quantified.

Conclusion (Lean): `(W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a one-step naturality/glue lemma (`rw [← map_φ, map_baseChange]`) about an existing mathlib
object; not a named theorem, not a project main result, introduces no new structure. (Literature width run to protocol.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-line *definition* check does not apply. The *proof* is a
single line, `rw [← map_φ, map_baseChange]`, reinforcing that it is glue over existing API.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve base change ring homomorphism commute compatibility"  | yes  | division polys ψₙ, φₙ ∈ ℤ[x,y,{aᵢ}] → commute with ring maps | universal-coefficient construction; base-change functoriality is standard |
|  2 | WebSearch (general / naturality) | (same query, "arbitrary commutative ring" facet)                                          | yes  | homogeneous division polys over arbitrary ring (arXiv:1303.4327); SageMath builds φₙ over the base ring | confirms div. polys are defined over an arbitrary commutative ring, hence natural |
|  3 | WebSearch (named-after / aliases)| "division polynomial" functorial base change field extension E(F)→E(K) (arXiv:2302.10640) | yes  | group-law formalisation handles base change to a field extension | naturality of the algebraic data under base change is treated explicitly |
|  4 | ChatGPT MCP                      | n/a — MCP down this session (per task note); compensated with extra WebSearch facets + primary-source reasoning | n/a | — | Silverman, *Arithmetic of Elliptic Curves* (2nd ed.) Ex. 3.7 / III §3 defines ψₙ, φₙ by integer recurrences ⇒ stable under base change |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` (and `refs/`) for "division polynomial" / base change | n/a | no references dir for this concept | recorded n/a — directory absent; concept settled by mathlib itself |
|  6 | nLab                             | "division polynomial"                                                                       | n/a  | no dedicated nLab page                                  | not an nLab-shaped (categorical) concept; naturality here is elementary |
|  7 | nCatLab (categorical)            | —                                                                                          | n/a  | —                                                     | no functor/2-cat content to chase |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                       | n/a  | no Stacks entry                                        | scheme-theoretic foundations; this concrete construction is out of Stacks' scope |
|  9 | MathOverflow / Math.StackExchange| "division polynomial defined over ℤ base change"                                            | yes  | folklore: ψₙ, φₙ universal over ℤ[aᵢ] ⇒ any ring map sends them to the base-changed curve's | corroborates the universal-coefficient argument |
| 10 | recent arXiv (last 5y)           | "homogeneous division polynomials Weierstrass" (arXiv:1303.4327, 2013) + group-law (2302.10640, 2023) | yes | div. polys over arbitrary rings; base-change-stable | modern treatments keep the over-any-ring formulation |

### Literature summary (Phase 3)

Concept: the **bivariate division-polynomial numerator `φₙ`** of a Weierstrass curve, and the **naturality of
division polynomials under base change / ring maps**.
Sources agree on the standard form: **yes** — division polynomials are universal polynomials with integer
coefficients in the Weierstrass coefficients `aᵢ` (Silverman III §3 / Ex. 3.7; arXiv:1303.4327; arXiv:2302.10640;
SageMath `ell_generic`). Being universal, they are *defined over an arbitrary commutative ring* and therefore
**commute with every ring homomorphism** — i.e. they are natural under base change. This is folklore; it is exactly
the content of `baseChange_φ`.
Most general standard form: for a Weierstrass curve over any commutative ring and any ring map of the coefficient
ring, the division polynomials transport along the map. The mathlib statement (over an `R`-algebra tower with an
`S`-algebra hom `f`, using `mapRingHom f` to lift to `R[X][Y]`) is exactly this naturality, packaged for base change.
Generality dimensions where the literature varies:
  - coefficient ring: literature uses *arbitrary commutative ring* — matches mathlib (`CommRing`), no field/PID assumed.
  - the map: literature uses *any ring homomorphism*; mathlib phrases it as base change + coefficient `.map (mapRingHom f)`,
    the standard packaging for the bivariate object.
Disagreement with the literature: **none.** mathlib's form is the literature-standard naturality, at full generality.

---

### Generality analysis — `WeierstrassCurve.baseChange_φ`

Literature-standard form (Phase 3): division polynomials over an *arbitrary commutative ring* commute with
*arbitrary ring maps* (base change). No field, no domain, no PID, no algebraically-closed hypothesis.

| # | Parameter / hypothesis                         | Current Lean form                | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------------|----------------------------------|------------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]` (and `S A B`)                    | arbitrary commutative ring       | arbitrary commutative ring         | NO                  | already maximally general for the coefficient ring |
| 2 | `f : A →ₐ[S] B`                                 | `S`-algebra homomorphism         | any ring map of coefficients       | borderline          | the *base-change* packaging is the canonical mathlib idiom; the more-primitive `map_φ` (along a plain ring hom, via `mapRingHom`) already exists upstream and `baseChange_φ` is the tower-relative corollary. Not a defect — intended specialisation, siblinged with `map_φ`. |
| 3 | `n : ℤ`                                          | integer index                    | integer index                      | NO                  | division polynomials are indexed by ℤ; correct index type |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it *is* mathlib's own form, verbatim).
Weakening opportunities found: 0. Proposed restatement: none. Cost: n/a.

### Modern-idiom check (Phase 4c)

Already fully typeclass-driven (`Algebra`, `IsScalarTower`); purely algebraic identity (no topology/filters);
a naturality equation, not a construction (no universal-property class to introduce); no substructure content;
already at `CommRing` (nothing to weaken); elementary (not higher-categorical); `ℤ` is the intrinsic index.
**Modern idiom available: no** — the lemma is already the contemporary mathlib formulation (it *is* the mathlib decl).

### Diamond / defeq risk (Phase 4.5)

n/a — kind is `lemma` (no definitional equalities or instances introduced).

---

### Mathlib search-status: `WeierstrassCurve.baseChange_φ`

[A] Lean-Finder       n/a (mathlib-index tools available but unnecessary — direct source hit below)
[B] Loogle            type `(W.baseChange _).φ _ = _` — n/a; superseded by exact-source grep
[C] LeanSearch        "division polynomial base change algebra hom" — n/a; superseded by exact-source grep
[D] Grep mathlib src  `grep -rn "baseChange_φ" .lake/packages/mathlib/` → **HIT**
[E] Name pattern      `baseChange_φ` in `WeierstrassCurve` namespace → **HIT**

Direct source evidence:
```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:583:
  lemma baseChange_φ (n : ℤ) : (W⁄B).φ n = ((W⁄A).φ n).map (mapRingHom f) := by
    rw [← map_φ, map_baseChange]
```
*Identical* to the project decl modulo notation: mathlib writes `W⁄B` for `W.baseChange B` (`⁄` is the scoped
base-change notation, `scoped notation:max W:max "⁄" S:max => baseChange W S`, at
`EllipticCurve/Affine/Basic.lean:268`). So `(W⁄B)` and `(W.baseChange B)` are the *same term*; the two statements are
the same proposition. The project's underlying `φ` definition (line 371) matches mathlib's `protected def φ`
(line 448), and the two proof dependencies both exist upstream:
- `WeierstrassCurve.map_φ` — `DivisionPolynomial/Basic.lean:541` (project copy: `DivisionPolynomial.lean:464`).
- `WeierstrassCurve.map_baseChange` — imported from mathlib unchanged (not re-defined in the project file).

Searched for both the current form `(W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f)` → found,
identical; and the more-primitive `map_φ` (plain ring hom) → also found upstream, with `baseChange_φ` its tower corollary.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_φ`; identical form** (verbatim fork, same statement
and same proof).

---

### Call sites — `WeierstrassCurve.baseChange_φ`

Internal use count: **0** within the NagellLutz project (excluding the declaring file).
External-to-file callers: 0 `.lean` files.

| Caller file:line               | Usage pattern (one-line excerpt) |
|--------------------------------|----------------------------------|
| (none)                         | — |

Grep `baseChange_φ` across `projects/**.lean` (excluding `.lake`) returns *only* the declaration site
(`DivisionPolynomial.lean:506`); every other hit is in `.mathlib-quality/` markdown, not Lean code.

Inline-derivation grep (was the equivalent re-derived elsewhere?): (none) — no project code uses `φ` base change.

Interpretation: `K = 0`, no inline re-derivation. This is **forked dead-weight** — present only because the whole
`DivisionPolynomial.Basic` file was copied to dodge the `normEDS` import clash; nothing in the project consumes it.

---

### Composition check (Phase 6)

Can `baseChange_φ` be derived from mathlib in ≤3 chained calls? — **It IS mathlib**, so trivially yes; the
mathlib-native proof is the 2-call composition:

Attempt 1: `by rw [← map_φ, map_baseChange]`
  - Mathlib decls used: `WeierstrassCurve.map_φ` (`DivisionPolynomial/Basic.lean:541`),
    `WeierstrassCurve.map_baseChange` (`EllipticCurve/Weierstrass.lean`).
  - Result: succeeds (verbatim the upstream proof).
  - Notes: composition is moot — the *fully assembled, identically-named* lemma already exists upstream, so the
    correct action is to reuse the mathlib decl, not inline its proof.

Conclusion: the form is **already in mathlib verbatim** (strictly stronger than "composable"). Verdict is
NO-mathlib-has-it, not NO-composable-from-mathlib.

---

## Verdict: `WeierstrassCurve.baseChange_φ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature (Phase 3): division-polynomial naturality under base change is standard folklore (universal integer
  coefficients ⇒ commute with ring maps); mathlib already encodes it. No generality gap.
- Generality (Phase 4): MAXIMALLY GENERAL — it is mathlib's own statement, at `CommRing`, no idiom gap (4c: no).
- Mathlib search (Phase 5): found as `WeierstrassCurve.baseChange_φ`, identical form
  (`DivisionPolynomial/Basic.lean:583`); proof deps `map_φ` / `map_baseChange` also upstream.
- Composition (Phase 6): the assembled lemma already exists upstream verbatim (stronger than composable).

**Rationale:**
This declaration is a **verbatim fork** of `WeierstrassCurve.baseChange_φ` from mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:583`. The statement is identical (the project
spells `W.baseChange B` where mathlib uses `W⁄B` for the same term, and both transport the bivariate `φₙ ∈ R[X][Y]`
via `mapRingHom f`), the proof is identical (`rw [← map_φ, map_baseChange]`), the underlying `φ` definition matches,
and both proof dependencies exist upstream (one, `map_baseChange`, is imported from mathlib unchanged). The file's own
module docstring states it is "a copy of `Mathlib...DivisionPolynomial.Basic`", forked solely to import the project's
local `EllipticDivisibilitySequence` (avoiding the `normEDS`/`complEDS` clash). Mathlib does not need this — mathlib
*is* the source. The literature search (run to protocol despite the open-and-shut source hit) confirms no added
generality: division polynomials are universal over `ℤ[{aᵢ}]`, so commuting with ring maps is the maximally-general
standard fact, already stated at `CommRing` in mathlib.

**WHY not (refactor-actionable):**
Mathlib already has the exact result — same name, same statement, same proof, same `φ`. The project copy exists purely
as collateral of copying the whole `DivisionPolynomial.Basic` file to swap one import. Proper resolution is the
project-level de-fork (drop the file copy once the upstream `normEDS` clash is otherwise managed), not a per-lemma
edit; as a mathlibable verdict, this lemma contributes nothing new to mathlib.

Existing mathlib decl:        `WeierstrassCurve.baseChange_φ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:583`
Our form follows in ≤1 line (it is the *same* lemma — exact reuse):
```lean
open scoped Polynomial Polynomial.Bivariate in
example {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) [Algebra R S]
    {A : Type*} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {B : Type*} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[S] B) (n : ℤ) :
    (W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f) :=
  WeierstrassCurve.baseChange_φ f n   -- the mathlib lemma, used directly
```
Call sites in our project: **K = 0**. No in-project consumers to migrate; the decl is dead-weight carried by the file
copy. Correct fix is file-level: eliminate the fork of `DivisionPolynomial.Basic` (and its siblings `baseChange_ψ₂`,
`baseChange_Ψ₂Sq`, `baseChange_Ψ₃`, `baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_preΨ`, `baseChange_ΨSq`,
`baseChange_Ψ`, `baseChange_Φ`, plus the `map_*`/`φ`/etc. copies) by resolving the `EllipticDivisibilitySequence`
import clash, then importing mathlib's `DivisionPolynomial.Basic` directly. Do **not** PR this to mathlib — it is
already there.

---

## Next step

Already in mathlib verbatim (`WeierstrassCurve.baseChange_φ`,
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:583`). Nothing to upstream. Fold into the
file-level de-fork cleanup of the copied `DivisionPolynomial.Basic` (the import-clash workaround), alongside its
identically-forked `baseChange_*` / `map_*` / `φ` siblings; zero in-project call sites, so no consumer migration for
this decl.
