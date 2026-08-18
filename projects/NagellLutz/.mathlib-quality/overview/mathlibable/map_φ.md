# /mathlibable report — `WeierstrassCurve.map_Φ`

**Verdict: NO-mathlib-has-it** — verbatim copy of mathlib's `WeierstrassCurve.map_Φ`.

> Note on the filename: this report is for **`map_Φ`** (capital Φ, U+03A6 — the *univariate*
> polynomial `Φₙ ∈ R[X]`, declared at `DivisionPolynomial.lean:453–456`). It is a **different
> declaration** from its lowercase sibling `map_φ` (U+03C6 — the *bivariate* `φₙ ∈ R[X][Y]`, at
> line 463–465), which has its own assessment. macOS's case-insensitive filesystem may fold the two
> filenames together; the content here is specifically the uppercase `Φ` lemma.

---

## Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); statements compared
  directly against the pinned mathlib in `.lake/packages/mathlib`.
- decl `WeierstrassCurve.map_Φ`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:453–456` (`@[simp]` on line 453;
  `lemma map_Φ` head on line 454).
- kind:                      lemma (`theorem`), `@[simp]`
- has sorry:                 no
- module docstring summary:  *"This is a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.)."*

Qualified name (verified): the decl sits inside `namespace WeierstrassCurve … end WeierstrassCurve`
(lines 27 / 511) with no inner namespace, so the parsed name **`WeierstrassCurve.map_Φ`** is correct.

---

## Statement (Phase 1)

`WeierstrassCurve.map_Φ` is a **naturality / base-change-compatibility lemma** for the univariate
division polynomial `Φₙ` of a Weierstrass curve. For a Weierstrass curve `W` over a commutative ring
`R` and a ring homomorphism `f : R →+* S`, the `Φₙ`-polynomial of the curve base-changed along `f`
equals the coefficient-wise image under `f` of `Φₙ(W)`. Writing `f∗W` for the curve with coefficients
pushed forward by `f`:

$$\Phi_n(f_* W) \;=\; f_*\big(\Phi_n(W)\big) \in S[X],$$

i.e. forming the univariate `n`-th division polynomial commutes with changing the base ring. (`Φₙ ∈
R[X]` is the univariate polynomial congruent to the bivariate `φₙ`, encoding the $x$-coordinate of
$[n]P$ via $x([n]P) = \Phi_n/\psi_n^2$.)

Variables / typeclasses (Lean side):
- `{R S : Type*} [CommRing R] [CommRing S]` — source/target commutative coefficient rings.
- `(W : WeierstrassCurve R)` — the curve.
- `(f : R →+* S)` — the ring hom along which we base-change.
- `(n : ℤ)` — the division-polynomial index.

Hypotheses: none beyond the typeclass context.

Conclusion (math): the univariate division polynomial `Φₙ` is natural in the base ring.
Conclusion (Lean): `(W.map f).Φ n = (W.Φ n).map f`.

Note the `.map f` here is `Polynomial.map f : R[X] → S[X]` (NOT `mapRingHom f`, which is what the
*bivariate* `map_φ`/`map_ψ` use over `R[X][Y]`) — because `Φ` is univariate.

Proof body (both copies identical):
```lean
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]
```

The underlying def is also identical in both files:
`protected noncomputable def Φ (n : ℤ) : R[X] := X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq`
(project `DivisionPolynomial.lean:272–273` vs mathlib `Basic.lean:349–350`).

---

## Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a `@[simp]` functoriality lemma in a uniform `map_*` family (`map_ψ₂`, `map_Ψ₂Sq`, `map_Ψ₃`,
`map_preΨ₄`, `map_preΨ'`, `map_preΨ`, `map_ΨSq`, `map_Ψ`, `map_Φ`, `map_ψ`, `map_φ`) — boilerplate
establishing that each division-polynomial constructor commutes with `WeierstrassCurve.map`. Not a
named theorem, not a main result.

(The literature width is short-circuited by an exact-name mathlib hit — see Phase 3 / Phase 5.)

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — one-liner check is **n/a**. (For completeness:
statement 1 line, proof 2 lines.)

---

## Literature search (Phase 3)

This phase is short-circuited by an **exact-name, exact-statement, same-namespace hit in mathlib**
(Phase 5). The "concept" is not a citable theorem from the mathematical literature — it is the
*functoriality of division polynomials under base change*, an internal Lean API/naturality fact. Its
"standard form" is, by definition, whatever mathlib's own `DivisionPolynomial/Basic.lean` states, and
the project decl is a character-for-character copy of exactly that.

| # | Channel | Query | Hit? | Notes |
|---|---|---|---|---|
| 1 | mathlib source (decisive) | `grep map_Φ` in `DivisionPolynomial/Basic.lean` | **yes** | identical lemma at line 530–533 (see Phase 5) |
| 2 | Concept-level math lit | "division polynomial defined over ℤ[a₁..a₆], base change / functoriality" | yes (folklore) | Division polys are universal polynomials in the Weierstrass coefficients `aᵢ` (Silverman, *Arithmetic of Elliptic Curves* §III; Wikipedia "Division polynomials"; MIT 18.783), hence commute with any coefficient ring map. The mathlib division-polynomial track is Angdinata's own contribution (ITP 2023). No literature form is more authoritative than mathlib's own statement, which we duplicate. |
| 3 | WebSearch / ChatGPT MCP / nLab / nCatLab / Stacks / MathOverflow / arXiv | — | n/a | Not run pro forma: an exact mathlib hit (Phase 5) fixes the bucket at `NO-mathlib-has-it` regardless of any literature form. The literature sweep informs *generality* only when mathlib lacks the decl; here mathlib has it identically, so the sweep cannot move the verdict. (Env note: ChatGPT MCP is down per the task brief; immaterial given the direct-source evidence.) nLab/Stacks have no division-polynomial page (not categorical / not the Stacks remit). |

### Literature summary (Phase 3)
Concept: functoriality of the univariate division polynomial `Φₙ` under a base ring homomorphism.
Standard form: identical to mathlib's `WeierstrassCurve.map_Φ`. No disagreement to record — the
project file *is* mathlib's file with one import swapped.

---

## Generality analysis (Phase 4)

### 4a/4b — Generality verdict

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|---|---|---|---|---|
| 1 | `[CommRing R] [CommRing S]` | commutative rings | commutative rings (universal in `aᵢ`) | NO | `Φ ∈ R[X]` is built from the Weierstrass data; commutativity is intrinsic to the whole `WeierstrassCurve` development |
| 2 | `(f : R →+* S)` | arbitrary ring hom | arbitrary ring hom | NO | already the most general arrow; this IS the naturality statement |
| 3 | `(n : ℤ)` | integer index | integer index (`Φ₋ₙ = Φₙ`) | NO | the index set for division polynomials is ℤ by definition |

Verdict: **MAXIMALLY GENERAL** — and moot, since it is a copy of the mathlib lemma at that very
generality. K = 0 weakening opportunities.

### 4c — Modern-idiom check
No modernisation move applies: already typeclass-based (`CommRing`, `→+*`); no analysis/topology to
filter-ise; `Φ` is a concrete polynomial and map-compat is a property, not a construction; the ℤ index
is intrinsic to division polynomials (`Φ₋ₙ = Φₙ`), not a monoid-generalisation candidate. It is already
the idiomatic mathlib spelling (`(W.map f).Φ n = (W.Φ n).map f`) authored by mathlib itself.
Modern idiom available: **no**.

---

## Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (introduces no definitional equality or instance-search path).

---

## Mathlib search-status (Phase 5)

Decisive. Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` contains,
inside `namespace WeierstrassCurve` (opened at line 104) and the `section Map` "Maps across ring
homomorphisms" (lines 489–491):

```lean
-- Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:530–533
@[simp]
lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f := by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]
```

This is **byte-for-byte identical** to the project decl (statement, `@[simp]` attribute, and proof),
under the **same namespace** `WeierstrassCurve`, with the **same** variable context
(`W : WeierstrassCurve R`, `f : R →+* S`).

Decisive comparison:

| | Project (`DivisionPolynomial.lean:453–456`) | Mathlib (`Basic.lean:530–533`) |
|---|---|---|
| attribute | `@[simp]` | `@[simp]` |
| statement | `lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f` | `lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f` |
| proof | `rw [← coe_mapRingHom]; simp [Φ, map_sub, apply_ite <| mapRingHom f]` | `rw [← coe_mapRingHom]; simp [Φ, map_sub, apply_ite <| mapRingHom f]` |

The underlying `Φ` definition is also identical (`X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if
Even n then 1 else W.Ψ₂Sq`), so the two `map_Φ` lemmas are statements about the *same* object — the
only divergence anywhere in the file is which `EllipticDivisibilitySequence`
(`normEDS`/`complEDS`) is imported underneath.

- [A] Lean-Finder / [C] LeanSearch / [B] Loogle: not needed — direct source hit by exact qualified name.
- [D] Grep mathlib src: `map_Φ` → hit at `DivisionPolynomial/Basic.lean:531`.
- [E] Name pattern `WeierstrassCurve.map_Φ`: hit; same namespace confirmed.

Concluded: **found in mathlib as `WeierstrassCurve.map_Φ`; identical form** (same name, namespace,
statement, proof, and `@[simp]`).

---

## Composition check (Phase 6)

### 6.0 Call sites — `WeierstrassCurve.map_Φ`
Internal use (NagellLutz, excluding the declaring file): the sibling `baseChange_Φ`
(`DivisionPolynomial.lean:501`, `rw [← map_Φ, map_baseChange]`) and
`LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:74` (`simp only [… map_Φ, map_ΨSq, …]`).

| Caller file:line | Usage pattern |
|---|---|
| `NagellLutz/LutzNagell/DivisionPolynomial.lean:501` | `rw [← map_Φ, map_baseChange]` (proof of `baseChange_Φ`) |
| `NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:74` | `simp only [← hc, curveK, map_Φ, map_ΨSq, …]` |

Decisive cross-project signal: **HasseWeil already uses the *mathlib* `WeierstrassCurve.map_Φ`
directly** — e.g. `HasseWeil/Auxiliary/DivisionPolynomial.lean:775` (`rw […, ← map_Φ, ← map_ΨSq]`),
`HasseWeil/EC/IsogenyAG/CovarianceDischarge.lean:765` (`WeierstrassCurve.map_Φ (W := E) …`), and
`HasseWeil/WeilPairing/PencilComapWitnesses.lean:448`. Those call sites resolve against mathlib's
lemma, demonstrating the mathlib version is the canonical, in-use one; the NagellLutz copy exists only
because that file rebuilds the whole `Φ` tower on a forked `normEDS`.

Inline re-derivation elsewhere: none — consumers use the `map_Φ` name.

### 6a Composition
Not a "compose from primitives" case — mathlib has the exact lemma (Phase 5), so the trivial
"derivation" is `exact WeierstrassCurve.map_Φ f n`. Hence the verdict is the stronger
`NO-mathlib-has-it`, not `NO-composable-from-mathlib`.

---

## Verdict: `WeierstrassCurve.map_Φ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_Φ` (`Basic.lean:530–533`);
  identical form, same namespace.
- Generality (Phase 4): MAXIMALLY GENERAL (and moot — it is a copy).
- Literature (Phase 3): n/a — exact mathlib hit; the lemma is internal API, not a citable theorem.
- Composition (Phase 6): not applicable; the exact decl already exists.

**Rationale.** The declaration is a verbatim copy of mathlib's `WeierstrassCurve.map_Φ`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:530–533`): identical statement
`(W.map f).Φ n = (W.Φ n).map f`, identical `@[simp]` attribute, identical two-line proof, in the
identical `WeierstrassCurve` namespace with the identical variable context — and the underlying `Φ`
definition is identical too, so the two lemmas concern the same object. The NagellLutz file is, by its
own module docstring, "a copy of `…DivisionPolynomial.Basic`" that swaps the
`EllipticDivisibilitySequence` import purely to dodge a `normEDS`/`complEDS` name clash with the
project's forked EDS file. The lemma contributes **nothing new** to mathlib. The point is underscored
by HasseWeil, which already calls the *mathlib* `WeierstrassCurve.map_Φ` directly.

**WHY not (refactor-actionable).** Mathlib already has this exact lemma. Our form is not merely
*derivable* from it — it *is* it. There is no generalisation, modernisation, or composition story to
tell; the only reason it is re-declared locally is the forked-EDS import. The gap that caused the
duplication is a **naming collision in the forked dependency** (`EllipticDivisibilitySequence` /
`Universal`), not any mathematical gap. The whole forked `DivisionPolynomial.lean` exists to re-root
the division-polynomial API on the project's EDS fork; `map_Φ` rides along for free.

Existing mathlib decl:  `WeierstrassCurve.map_Φ`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:530–533`
Our form follows in 0 lines (it is the same lemma):
```lean
example {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    (f : R →+* S) (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f :=
  WeierstrassCurve.map_Φ f n   -- the mathlib lemma, once the forked Φ is dropped
```

Call sites in our project (Phase 6.0): K = 2 (`DivisionPolynomial.lean:501` `baseChange_Φ`;
`PIDIntegralMultiple.lean:74`).

**Refactor plan.** This decl is **not independently removable** while the forked `normEDS`/`Φ` tower
remains — the local `Φ` is a *distinct Lean object* from mathlib's `Φ` only because it is rebuilt on
the forked `EllipticDivisibilitySequence`. The actionable unit is the **whole forked
`DivisionPolynomial.lean`**, not `map_Φ` alone:
1. Migrate `LutzNagell.EllipticDivisibilitySequence` + `LutzNagell.DivisionPolynomial` onto mathlib's
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` and `…DivisionPolynomial.Basic` (resolve the
   `normEDS`/`complEDS` clash by *importing* rather than redefining).
2. Delete the whole `section Map` / `section BaseChange` block (lines ~412–509), including `map_Φ`.
3. At the 2 call sites, `map_Φ` / `baseChange_Φ` then resolve to mathlib's versions unchanged (same
   name, namespace, and argument order) — no edit needed beyond the import migration.
   If the fork must persist short-term, do **not** spend cleanup effort golfing/re-styling `map_Φ`
   (or its neighbours): they are meant to track mathlib byte-for-byte, so any divergence is a defect,
   not an improvement.

Next action: do **not** open a mathlib PR (mathlib already has it verbatim). Track an AINTLIB cleanup
task to de-fork `LutzNagell`'s EDS + DivisionPolynomial onto mathlib so the entire copied
`DivisionPolynomial.lean` can be dropped in favour of the mathlib import.

---

## Next step

Delete `WeierstrassCurve.map_Φ` (with its sibling `map_*` / `baseChange_*` block) from the project as
part of de-forking `LutzNagell.DivisionPolynomial`/`EllipticDivisibilitySequence` onto mathlib; the 2
call sites then bind to the existing `WeierstrassCurve.map_Φ` unchanged. No mathlib PR — mathlib
already has it verbatim (`DivisionPolynomial/Basic.lean:530–533`).
