# Mathlibable assessment: `WeierstrassCurve.isEllSequence_ψ`

**Verdict: YES-but-generalise-first**

- **Qualified name:** `WeierstrassCurve.isEllSequence_ψ`
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:53`
- **Date:** 2026-06-18
- **One-line summary:** the target is a *defeq one-liner* specialising the genuinely-mathlibable
  general lemma `IsEllSequence.normEDS`; what belongs upstream is that general lemma (it closes a
  standing mathlib TODO), not this curve-specific `ψ` wrapper.

## Statement (verified from source)

```lean
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open WeierstrassCurve (ψ₂ ψ φ)

/-- `WeierstrassCurve.isEllSequence_ψ`: the `ψ` family forms an elliptic sequence. -/
lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS
```

Context:
- `W.ψ : ℤ → R[X][Y]` is the division-polynomial family, **defined** (project
  `DivisionPolynomial.lean:324`, upstream-equivalent `…/DivisionPolynomial/Basic.lean:401`) as
  ```lean
  protected noncomputable def ψ : ℤ → R[X][Y] := normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)
  ```
  i.e. `W.ψ` is *definitionally* `normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`.
- `IsEllSequence W` (mathlib `EllipticDivisibilitySequence.lean:82`, identical in the project fork
  at line 135, factored through `Rel₃`) is the Ward/Stange elliptic-sequence relation
  `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²`.
- `IsEllSequence.normEDS : IsEllSequence (normEDS b c d)` is the project's own lemma
  (`EllipticDivisibilitySequence.lean:1212`): *every normalised EDS is an elliptic sequence*.

Because `W.ψ` unfolds to `normEDS …` by `rfl`, the term `IsEllSequence.normEDS` already has the
required type `IsEllSequence W.ψ` (the three `normEDS` arguments are inferred). **The lemma performs
no mathematical work**; it is a name for the specialisation.

## 1. Literature search

- The fact that the elliptic-curve division polynomials form an elliptic divisibility sequence is
  the foundational result of the area — Ward, *Memoir on elliptic divisibility sequences* (1948);
  Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316); Silverman, *AEC* Ex. 3.7 / the
  division-polynomial recurrences. So the *general* statement ("`normEDS` is an `IsEllSequence`",
  hence so is `ψ`) is textbook-canonical and squarely mathlib-appropriate.
- Background sources surfaced: Shipsey/Swart EDS theses; "On Elliptic Sequences over Commutative
  Rings" (arXiv:2604.05280); "EDS, Squares and Cubes" (arXiv:1101.3839); homogeneous division
  polynomials (arXiv:1303.4327).
- The *specific* corollary "`IsEllSequence W.ψ` for a `WeierstrassCurve`" has no independent name in
  the literature — it is the immediate instantiation of the general normalised-EDS fact at the
  curve's `(ψ₂, Ψ₃, preΨ₄)` seed. No standalone citation; it is not a named theorem.

## 2. Mathlib search (five methods) — checked the forked files first

Per project context, NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether
this lemma (or its general form) is already upstream.

- `grep -rn "isEllSequence_ψ\|IsEllSequence W.ψ\|IsEllSequence (W.ψ"` across the mathlib checkout
  (`mathlib4-up1`, `eb15debe777`, 2026-06-07, ≈ the rc2 pin `d90090f`) → **no hits**.
- Mathlib `DivisionPolynomial/Basic.lean` (upstream + live docs) contains **no `IsEllSequence`
  mention at all** — no `isEllSequence_ψ`, no `IsEllSequence W.ψ`. It still carries a TODO for the
  `ωₙ` family.
- Mathlib `EllipticDivisibilitySequence.lean` (upstream + **live mathlib4 docs, fetched 2026-06-18**)
  still carries the open TODOs:
  > * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
  > * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
  So mathlib does **not** yet have `IsEllSequence.normEDS` either — the very lemma the target
  re-exports is the unfinished mathlib TODO. (The project's own audit notes this:
  `analysis/04-mathlib-api-audit.md:19`, and that the `ω/ψc/invar` machinery discharges that TODO,
  `:99`.)
- loogle / leansearch (mathlib index): consistent — no upstream decl of either shape.
- No merged mathlib PR found upstreaming `IsEllSequence.normEDS`; the file's authors (Xu, Angdinata)
  have an in-flight Mathlib upstreaming effort for `EllipticDivisibilitySequence.lean`, but as of the
  live docs the result is **not yet merged**.

**Conclusion:** neither the target nor its general form is in mathlib today. The general form is a
known, still-open mathlib TODO.

## 3. Generality analysis

- The target is the *least* general member of a chain: the mathlibable object is the **general**
  `IsEllSequence.normEDS : IsEllSequence (normEDS b c d)` over an arbitrary `CommRing` and arbitrary
  seeds `b c d` (literally the mathlib TODO). `isEllSequence_ψ` is that lemma frozen at one
  curve-derived seed `(ψ₂, C Ψ₃, C preΨ₄)` in the ring `R[X][Y]`.
- Adding the `ψ`-specialised wrapper *as is* would be strictly redundant once the general lemma is
  upstream: `W.ψ` is defeq `normEDS …`, so any consumer can write `IsEllSequence.normEDS` (or a
  `simp [WeierstrassCurve.ψ]`) directly. The project's own junk audit reaches the same conclusion:
  `analysis/07-api-and-junk.md:181` flags `isEllSequence_ψ` **INLINE** — "`:= IsEllSequence.normEDS`
  (pure mathlib re-export); unused project-wide. Inline the mathlib lemma at use sites or drop."
  (Inventory confirms it is public API but has **no in-file consumer**:
  `inventory/LutzNagell_DivisionPolynomialOmega.md:207`.)

## 4. Composition check (≤3 mathlib calls)

- **Against mathlib *as it exists today*:** the target is **not** composable, because its one
  ingredient `IsEllSequence.normEDS` is not in mathlib (it is the open TODO). So "NO-composable-from-
  mathlib" is *false right now*.
- **Against mathlib *after* the general lemma lands:** the target becomes a **0-work, 1-step defeq**
  corollary — `IsEllSequence (normEDS …)` *is* `IsEllSequence W.ψ`. At that point it does not deserve
  its own lemma; it is a one-liner at the use site.

This is the textbook "thin wrapper around a missing general lemma" shape: the wrapper is worthless to
add, but the general lemma it wraps is exactly what mathlib wants.

## 5. Five-bucket verdict

**YES-but-generalise-first.**

- Not **NO-mathlib-has-it**: mathlib has neither the `ψ` corollary nor the general
  `IsEllSequence.normEDS` (live-docs TODO still open).
- Not **NO-composable-from-mathlib**: the single primitive it composes from is itself absent from
  mathlib today, so it cannot be composed from current mathlib.
- Not **YES-add-as-is**: the curve-specific `ψ` wrapper is a defeq one-liner, unused project-wide,
  and would be redundant the moment the general lemma is upstream — adding it verbatim is wrong.
- Not **BORDERLINE**: the path is unambiguous.

**What to upstream:** the *general* lemma `IsEllSequence.normEDS`
(`EllipticDivisibilitySequence.lean:1212`) — *every normalised EDS is an elliptic sequence* — which
closes the standing mathlib TODO "prove that `normEDS` satisfies `IsEllDivSequence`" (together with
its partner `IsDivSequence.normEDS` to give the full `IsEllDivSequence.normEDS`). Once that is in
mathlib's `EllipticDivisibilitySequence.lean`, the present `isEllSequence_ψ` is recovered for free as
the defeq instantiation at `(W.ψ₂, C W.Ψ₃, C W.preΨ₄)` and need not exist as a separate declaration
(at most a trivial `@[simp]`/one-liner in `DivisionPolynomial/Basic.lean` if a named hook is wanted).

## Notes / cross-refs

- The substantive proof actually lives in `IsEllSequence.normEDS` and the `invar_of_net` / Stange-net
  machinery (`EllipticDivisibilitySequence.lean`), plus the `ω/ψc/invar` files
  (`DivisionPolynomialOmega.lean`) that the project audit identifies as discharging the mathlib TODO
  (`analysis/04-mathlib-api-audit.md:92-99`, `analysis/05-duplications.md:174-177`). The mathlibable
  weight belongs to *those*, assessed separately.
- The fork's `IsEllSequence` is identical to mathlib's (just routed through `Rel₃`), so no
  re-statement issue blocks upstreaming the general lemma.
