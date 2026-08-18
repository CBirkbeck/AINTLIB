# Mathlibable assessment: `WeierstrassCurve.Universal.isEllSequence_ψᵤ`

**Verdict: YES-but-generalise-first**

- **Qualified name:** `WeierstrassCurve.Universal.isEllSequence_ψᵤ`
  (verified from source: `namespace WeierstrassCurve` @76 → `namespace Universal` @86; `namespace
  Affine` does not open until @157, well after line 139. So the decl sits directly in
  `WeierstrassCurve.Universal`. The task's parsed guess is correct.)
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:139`
- **Date:** 2026-06-22
- **mathlib pin:** `09b373db6e24` (toolchain `leanprover/lean4:v4.32.0-rc1`)
- **One-line summary:** the target is a thin universal-curve corollary of the genuinely-mathlibable
  general lemma `IsEllSequence.normEDS` (*every normalised EDS is an elliptic sequence*), which is a
  still-open mathlib TODO. Upstream the **general** lemma, not this `ψᵤ` wrapper.

## Statement (verified from source)

```lean
namespace WeierstrassCurve
namespace Universal
-- (FractionRing of the universal ring ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨Weierstrass poly⟩)

/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)          -- ZSMul.lean:132

lemma ψᵤ_eq_normEDS :                                                    -- ZSMul.lean:134
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence ψᵤ := by                          -- ZSMul.lean:139  ← TARGET
  rw [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS
```

Context of the symbols:
- `Universal.Field := FractionRing Universal.Ring` (`Universal.lean:99`), the fraction field of the
  universal coordinate ring `ℤ[A₁…A₆, X, Y]/⟨Weierstrass polynomial⟩`.
- `polyToField : Poly →+* Universal.Field` (`Universal.lean:108`) is the ring homomorphism
  `(algebraMap …).comp (AdjoinRoot.mk …)` specialising a coordinate polynomial into the universal
  field.
- `curve : Affine (MvPolynomial Coeff ℤ)` (`Universal.lean:84`) is the universal Weierstrass curve;
  `curve.ψ n` is its `n`-th division polynomial.
- `ψᵤ n := polyToField (curve.ψ n)` — the universal division polynomials, **mapped into the
  universal field**.
- `IsEllSequence W` (mathlib `EllipticDivisibilitySequence.lean:82`; identical in the project fork,
  routed through `Rel₃`) is the Ward/Stange elliptic-sequence relation
  `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²`.
- `IsEllSequence.normEDS : IsEllSequence (normEDS b c d)` — the project's own lemma
  (`EllipticDivisibilitySequence.lean:1211`), *every normalised EDS is an elliptic sequence*.

Unlike the curve-level sibling `isEllSequence_ψ` (where `W.ψ` is **defeq** `normEDS …`, so the proof
is the bare term `IsEllSequence.normEDS`), here `ψᵤ n = polyToField (curve.ψ n)` is **not** defeq to
a `normEDS`. The proof first invokes `ψᵤ_eq_normEDS` — which pushes the ring hom `polyToField`
through `normEDS` via mathlib's `map_normEDS` — and only then applies `IsEllSequence.normEDS`. So the
target is a genuine **2-step composition**, but both steps are off-the-shelf: a `map_*` lemma
(in mathlib) and the EDS-is-elliptic lemma (the open TODO).

## 1. Literature search

- That elliptic-curve division polynomials form an elliptic divisibility sequence is the founding
  result of the area: Ward, *Memoir on elliptic divisibility sequences* (1948); Stange, *Elliptic
  nets and elliptic curves* (arXiv:0710.1316); Silverman *AEC* Ex. 3.7 and the division-polynomial
  recurrences. The **general** statement ("`normEDS` is an `IsEllSequence`") is textbook-canonical
  and squarely mathlib-appropriate.
- Background sources surfaced via WebSearch: the EDS Wikipedia article; "EDS, Squares and Cubes"
  (arXiv:1101.3839); "The sign of an EDS" (arXiv:math/0402415); Shipsey/Swart theses. None gives the
  *universal-field carrier* `ψᵤ` an independent name — it is purely a Lean device for the
  universal-curve argument (a `FractionRing` of a quotient of `ℤ[A₁…A₆,X,Y]`).
- The *specific* statement "`IsEllSequence ψᵤ` for the universal curve" has **no** standalone
  citation in the literature; it is an internal instantiation, not a named theorem.

## 2. Mathlib search (five methods) — forked files checked first

NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether the
target — or its general form — is already upstream.

- **[A] leansearch / loogle (mathlib index):** `IsEllSequence ψᵤ`, "`ψᵤ` elliptic", `IsEllSequence
  (polyToField _)` → no such decl; the index only knows the *general* `IsEllSequence`, `normEDS`,
  `normEDS_even/odd`, `map_normEDS`. The `ψᵤ` carrier is project-local (defined over the project's
  `Universal.Field`), so it cannot be upstream.
- **[B] loogle (shape):** `IsEllSequence (_ )` against the seed pattern → only mathlib's defining
  occurrences (`IsEllSequence.smul`); no `normEDS`-is-elliptic lemma at all.
- **[C] grep mathlib src** (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
  pin `09b373db6e24`):
  - `IsEllSequence.normEDS` / `IsEllSequence (normEDS …)` → **no hits**. mathlib has only
    `IsEllSequence` (:82), `IsEllSequence.smul` (:106), and the `normEDS` definition (:289).
  - `namespace EllSequence`, `def net`, `def Rel₃`, `EllSequence.net` → **no hits**. The entire
    Stange-net apparatus (`EllSequence`/`net`/`Rel₃`/`rel₄`/`addMulSub`) that the project uses to
    *prove* `IsEllSequence.normEDS` lives **only in the project fork** (`EllipticDivisibilitySequence.lean`
    :90–597, :1211).
  - `map_normEDS` → **present** at mathlib :530 (so the first proof step of `ψᵤ_eq_normEDS`,
    `← map_normEDS`, is mathlib-available).
- **[D] live mathlib docs (WebSearch, fetched 2026-06-22):** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  **still carries the open TODOs**:
  > * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
  > * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
  So mathlib does **not** yet have `IsEllSequence.normEDS`; the very lemma the target re-exports is
  the unfinished mathlib TODO. `DivisionPolynomial/Basic.lean` contains **no `IsEllSequence` mention
  at all**.
- **[E] name pattern:** `isEllSequence_ψᵤ`, `WeierstrassCurve.Universal.*` → nothing upstream; the
  whole `Universal` namespace is project-local.

**Conclusion:** neither the target nor its general form is in mathlib today. The general form
(`IsEllSequence.normEDS`) is a known, still-open mathlib TODO; only the mechanical ingredient
`map_normEDS` is upstream.

## 3. Generality analysis

| ingredient | target's form | maximally-general (mathlib-shaped) form | gap |
|---|---|---|---|
| ring | `Universal.Field = FractionRing (ℤ[A₁…A₆,X,Y]/⟨P⟩)` | arbitrary `CommRing R` | target fixes one specific field |
| sequence | `ψᵤ = polyToField ∘ curve.ψ` | arbitrary `normEDS b c d` | target fixes one curve-derived seed + a `polyToField` cast |
| conclusion | `IsEllSequence ψᵤ` | `IsEllSequence (normEDS b c d)` | identical predicate, frozen |

- The mathlibable object is the **general** `IsEllSequence.normEDS : IsEllSequence (normEDS b c d)`
  over an arbitrary `CommRing` and arbitrary seeds (literally the mathlib TODO). `isEllSequence_ψᵤ`
  is that lemma triply-frozen: at the universal field, at the seed `(ψ₂, C Ψ₃, C preΨ₄)`, and behind
  the `polyToField` ring map.
- Once the general lemma is upstream, `isEllSequence_ψᵤ` is recovered as a **one-line `simp
  [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS`** — i.e. exactly the present proof, with its sole
  non-mathlib ingredient now in mathlib. It would carry no independent mathematical content.
- The `ψᵤ` carrier itself (`FractionRing Universal.Ring`, `polyToField`, `curve`) is bespoke project
  scaffolding for the universal-curve `n • P` formula and has no mathlib analogue, so the wrapper
  cannot be lifted verbatim regardless.

## 4. Composition check (≤3 mathlib calls)

- **Against mathlib as it exists today:** **NOT** composable. The proof is `ψᵤ_eq_normEDS` then
  `IsEllSequence.normEDS`. The first half (`← map_normEDS`, mathlib :530) composes fine, but the
  second half `IsEllSequence.normEDS` is **absent from mathlib** (the open TODO). So
  "NO-composable-from-mathlib" is *false right now* — the chain hits a missing primitive.
- **Against mathlib after the general lemma lands:** becomes a **trivial 2-step** corollary
  — `rw [ψᵤ_eq_normEDS]` (itself `map_normEDS` + `rfl`) then `exact IsEllSequence.normEDS`. At that
  point it is a one-liner at the use site and does not merit its own named lemma.

This is the textbook "thin wrapper around a missing general lemma" shape: the wrapper is not worth
adding, but the general lemma it wraps is exactly what mathlib wants. Identical structurally to the
sibling `isEllSequence_ψ` (`mathlibable/isEllSequence_ψ.md`, also `YES-but-generalise-first`); the
only differences here are (i) one extra mechanical `map_normEDS` step because `ψᵤ` is a ring-map
image rather than defeq, and (ii) unlike `isEllSequence_ψ`, this one **is** an in-project consumer
(see Notes), so it should be *kept locally* — just not upstreamed as-is.

## 5. Five-bucket verdict

**YES-but-generalise-first.**

- Not **NO-mathlib-has-it:** mathlib has neither the `ψᵤ` corollary nor the general
  `IsEllSequence.normEDS` (live-docs TODO still open; grep over pin `09b373db6e24` confirms absent).
- Not **NO-composable-from-mathlib:** one of its two primitives (`IsEllSequence.normEDS`) is itself
  absent from current mathlib, so it cannot be composed from mathlib today.
- Not **YES-add-as-is:** the universal-field `ψᵤ` wrapper bakes in `polyToField` + the universal
  `curve` + `FractionRing Universal.Ring`; it is far too specific for mathlib and would be redundant
  the moment the general lemma is upstream.
- Not **BORDERLINE:** the path is unambiguous and matches the already-decided `isEllSequence_ψ` /
  `net_normEDS` precedents in this same ledger.

**What to upstream:** the *general* lemma `IsEllSequence.normEDS`
(`EllipticDivisibilitySequence.lean:1211`) — *every normalised EDS is an elliptic sequence* — which
closes the standing mathlib TODO "prove that `normEDS` satisfies `IsEllDivSequence`" (together with
its partner `IsDivSequence.normEDS` to give the full `IsEllDivSequence.normEDS`). That upstreaming
also requires the project's `EllSequence`/`net`/`Rel₃`/`invar_of_net` apparatus (none of which is in
mathlib) — assessed separately under `net_normEDS.md`, `IsEllSequence.invar.md`, `rel₄_*` etc.
Once the general lemma lands, `isEllSequence_ψᵤ` stays a **project-local** one-liner (it has real
in-project consumers — see Notes) and need not be a separate mathlib declaration.

## Notes / cross-refs

- **Real consumer (unlike `isEllSequence_ψ`):** `isEllSequence_ψᵤ` is used by `smulX_sub_smulX`
  (`ZSMul.lean:191`, `convert (isEllSequence_ψᵤ n m 1).symm`), on the path to the universal
  multiplication formula `n • (X,Y) = (φₙ/ψₙ², ωₙ/ψₙ³)`. So it is **load-bearing project API**, not
  dead code — keep it in the project; just do not PR it to mathlib as-is.
- **Near-verbatim duplicate in HasseWeil:** `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:215`
  defines the same `isEllSequence_ψᵤ` (same proof). That is a *cross-project dedup* concern for the
  cleanup fleet, orthogonal to the mathlibability verdict.
- The substantive mathematical weight lives in `IsEllSequence.normEDS` (:1211) and the Stange-net
  machinery (`net`/`rel₄`/`addMulSub`/`invar_of_net`), plus `map_normEDS` (mathlib :530) and
  `ψᵤ_eq_normEDS`. The mathlibable payoff belongs to *those*, assessed in their own reports.
- Ledger precedent: `isEllSequence_ψ → YES-but-generalise-first`; `net_normEDS → YES-but-generalise-first`;
  `IsEllSequence.invar → YES-but-generalise-first`. This verdict is consistent with them.
