# Mathlibable assessment — `WeierstrassCurve.Universal.ringEval_comp_eq_specialize`

- **Declaration (verified qualified name):** `WeierstrassCurve.Universal.ringEval_comp_eq_specialize`
- **Location:** `projects/NagellLutz/LutzNagell/Universal.lean:229`
- **Author:** Junyan Xu (file header).
- **Assessed:** 2026-06-22 (AINTLIB `/overview` Step-9 pass).

## Verdict: NO-composable-from-mathlib

A naturality-square glue lemma. Its statement only has meaning relative to this project's
bespoke `ringEval`/`polyEval`/`specialize` definitions; **given** those definitions it is
immediate from mathlib primitives (`AdjoinRoot` quotient + `RingHom.comp_assoc`) plus two
sibling project lemmas. The only genuinely open question — should mathlib host the whole
universal-Weierstrass-curve scaffold at all — is a **package-level human decision**, and it is
already tracked at the scaffold roots (`specialize.md`, `ringEval.md`, `curve.md`, all
recommending the bundled PR). This individual one-line corollary is not itself the place where
that decision lives, so it is filed `NO-composable-from-mathlib` consistently with its direct
structural twin `polyEval_comp_eq_specialize` (also `NO-composable-from-mathlib`).

## The statement and proof

```lean
lemma ringEval_comp_eq_specialize :
    (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk,
      polyEval_comp_eq_specialize]
```

Here, for a Weierstrass curve `W` over a commutative ring `R` and a point `(x, y)` on the affine
plane with `eqn : W.Equation x y`:

- `P := MvPolynomial Coeff ℤ = ℤ[A₁,A₂,A₃,A₄,A₆]` — the universal coefficient ring.
- `Universal.Ring := curve.CoordinateRing` — the coordinate ring of the universal curve, i.e.
  `AdjoinRoot` of the Weierstrass polynomial inside `P[X][Y]`.
- `W.specialize : P →+* R` — the coefficient-specialization hom `Aᵢ ↦ aᵢ(W)`
  (`Universal.lean:190`, defined as `(MvPolynomial.aeval (Coeff.rec W.a₁ … W.a₆)).toRingHom`).
- `ringEval eqn : Universal.Ring →+* R` — the point-evaluation hom (`Universal.lean:215`),
  an `AdjoinRoot.lift` of `eval₂RingHom W.specialize x` at `y`.
- `algebraMap _ _ : P →+* Universal.Ring` — the structure map.

The lemma asserts that **restricting the universal point-evaluation hom back along the structure
map `P → Universal.Ring` recovers coefficient specialization**: `ringEval eqn ∘ algebraMap = W.specialize`.
This is the "outer" naturality triangle; it is consumed two lines later by
`curveRing_map_ringEval` (`Universal.lean:237`), which proves `curveRing.map (ringEval eqn) = W`.

Mathematically it is one face of the commuting diagram
`P → P[X][Y] → Universal.Ring → R`, where the long composite to `R` is `specialize` whether you
route through the coordinate ring or not.

## (1) Literature search

The **universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]`** and its coordinate ring are a
standard, named object:

- The ring `A = ℤ[a₁,a₂,a₃,a₄,a₆]` parametrizes Weierstrass curves
  `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`; there is a universal generalized elliptic curve over
  the open `Spec(A)°` where `c₄`/`Δ` do not simultaneously vanish. The Hopf algebroid
  `(A[Δ⁻¹], A[r,s,t])` representing nonsingular Weierstrass curves + strict isomorphisms is the
  basis of the **moduli stack of elliptic curves** and underlies **TMF**.
  - Behrens/Hopkins-style TMF notes (e.g. *Topological modular forms with level structure*,
    arXiv:1312.7394) and *An overview of abelian varieties in homotopy theory* (arXiv:0810.0507).
  - Katz–Mazur / N. Katz, *Universal Weierstrass families* (Princeton notes, ch. 10).
  - SageMath / Magma "elliptic curves over a general ring": the specialization-by-coefficients
    mechanism is exactly `W.map f` for a ring hom `f`.

**Conclusion of (1):** the *surrounding infrastructure* (the universal curve, its coordinate ring,
the specialization hom) is genuinely standard and mathlib-worthy. But
`ringEval ∘ algebraMap = specialize` is **not** a separately citable theorem — no textbook states
it; it is an internal compatibility lemma that only arises once you have *chosen* these particular
`ringEval`/`polyEval`/`specialize` constructions. It is "the naturality square commutes" plumbing.

## (2) Mathlib search — is it there, or a more general form?

Searched the pinned mathlib source (`.lake/packages/mathlib`, the daily-bump pin) by all five
methods:

- `grep` over the whole `Mathlib/` tree for `namespace Universal` / `WeierstrassCurve.Universal` /
  `Universal.curve` / `def specialize` / `def ringEval` / `def polyEval` /
  `ringEval_comp_eq_specialize` → **no hits** in the EllipticCurve area (only the unrelated
  `UniversallyOpen` morphism namespace and `UniversalEnvelopingAlgebra`).
- `grep -i universal` over `Mathlib/AlgebraicGeometry/EllipticCurve/**` → the **only** occurrence is
  a *prose docstring* in `DivisionPolynomial/Basic.lean:36–38`:
  > "…in the characteristic `0` universal ring `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` of `W`,
  > where the … associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`."
  i.e. mathlib **describes** the universal ring + specialization morphism informally but **does not
  define them as objects**. That `𝓡[X,Y] → R[X,Y]` morphism is the polynomial-ring analogue of
  `polyEval`; there is no coordinate-ring (`AdjoinRoot`) version, hence nothing like `ringEval` or
  this lemma.
- `grep` for `specialize` / `ringEval` / `polyEval` as decl names on Weierstrass curves anywhere in
  `Mathlib/` → **none**.
- mathlib4 docs page for `…/EllipticCurve/Affine/Point.html` (where `CoordinateRing` lives) — fetched
  and confirmed it defines `CoordinateRing`, `basis`, ideals, points, but **no** `Universal`,
  `specialize`, `ringEval`, `polyEval`, or `ringEval_comp_eq_specialize`.
- Released `DivisionPolynomial/` directory holds only `Basic.lean`, `Degree.lean` — no universal
  scaffold.

**No more-general form exists in mathlib.** The building blocks the proof *uses* do:
`AdjoinRoot.lift`/`AdjoinRoot.lift_mk`/`AdjoinRoot.mk` (`Mathlib/RingTheory/AdjoinRoot.lean:280,289,94`)
and `RingHom.comp_assoc` (`Mathlib/Algebra/Ring/Hom/Defs.lean:546`).

## (3) Generality analysis

The lemma is **already at maximal generality** for its content: arbitrary `R : Type* [CommRing R]`,
arbitrary `W : WeierstrassCurve R`, arbitrary point `(x, y)` with `eqn : W.Equation x y`. The base
of the universal ring is `ℤ` (initial), so there is nothing to weaken. `/generalise` is expected to
find no improvement. No typeclass can be dropped: `CommRing R` is needed for `CoordinateRing`,
`eval₂RingHom`, and `AdjoinRoot.lift` to make sense.

## (4) Composition check — can ≤3 mathlib calls give it?

**Two readings, both leading to NO-composable-from-mathlib:**

- *As stated* (referencing `ringEval`, `specialize`, `Universal.Ring`): you cannot write the
  statement at all from mathlib primitives, because those three definitions do not exist in mathlib.
  So it is not a "mathlib lemma waiting to be discovered."
- *Given the project's defs already in place*: the proof **is** essentially a ≤3-step composition —
  `algebraMap_ring_eq_comp` (defeq `rfl`, the structure map factors as `AdjoinRoot.mk ∘ algebraMap`)
  + `RingHom.comp_assoc` (mathlib) + the two sibling lemmas `ringEval_comp_mk` and
  `polyEval_comp_eq_specialize`. The genuinely-mathlib content reduces to `AdjoinRoot.lift_mk` and
  `RingHom.comp_assoc`. So once the scaffold is admitted, this corollary carries **no independent
  mathematical weight** — it is glue between two already-stated facts.

Either way the right single-declaration disposition is `NO-composable-from-mathlib`: it is a
naturality-square corollary that, conditional on the (separately-assessed) scaffold, mathlib's
primitives + the sibling API produce immediately. This matches the bucket assigned to its direct
structural twin one layer down, `polyEval_comp_eq_specialize`
(`…/mathlibable/polyEval_comp_eq_specialize.md` → `NO-composable-from-mathlib`), and to the other
per-layer glue lemmas in this file (`ringEval_comp_mk`, `ringEval_mk` → `NO-composable-from-mathlib`).

## (5) Five-bucket synthesis

| Bucket | Fit |
|---|---|
| YES-add-as-is | ✗ — not a standalone fact; references project-only defs; trivial proof. |
| YES-but-generalise-first | ✗ — already maximally general; nothing to weaken. |
| NO-mathlib-has-it | ✗ — verified absent (only a prose docstring mention in `DivisionPolynomial/Basic.lean`). |
| **NO-composable-from-mathlib** | **✓ — naturality-square glue; given the scaffold it is `AdjoinRoot.lift_mk` + `RingHom.comp_assoc` + two sibling lemmas (≤3 essential steps).** |
| BORDERLINE-needs-human | partial — the *package* decision (upstream the whole universal-curve scaffold? represented-functor framing? dedup) is a real human call, but it is owned by the scaffold roots `specialize.md`/`ringEval.md`/`curve.md`, not by this corollary. |

**Chosen bucket: `NO-composable-from-mathlib`.** This individual lemma is a thin corollary; the
human-judgement question belongs to its parent definitions, which are separately bucketed
`BORDERLINE-needs-human` (`specialize`) / packaged-PR (`ringEval`, `curve`). Filing the corollary
itself as `NO-composable` keeps the verdict consistent across the file's per-layer glue lemmas and
avoids double-counting the same package decision.

## Cross-project duplication (dedup ticket, independent of the mathlib decision)

The **entire `Universal.lean` is forked near-byte-identically** between this project and HasseWeil:

- `projects/NagellLutz/LutzNagell/Universal.lean:229` (this decl)
- `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:232` — same lemma, **verbatim** statement
  and proof; same author.

The two files differ only in the module docstring wording, line offsets, and one trivial
`.toAffine` coercion in `Affine.point`. Regardless of any mathlib outcome, the AINTLIB cleanup
fleet's **dedup lane** should consolidate the shared `Universal` scaffold into `Common/` (one copy),
as already flagged in `specialize.md`, `ringEval.md`, and `polyEval_comp_eq_specialize.md`.

## Next step

None blocking for this decl as a single declaration (`NO-composable-from-mathlib`). The live
decisions are at the package level and already recorded:
1. **(human / scaffold-level)** whether to upstream the universal-Weierstrass-curve package — see
   `specialize.md` (`BORDERLINE-needs-human`), `ringEval.md`, `curve.md`. If it lands, this lemma
   rides along automatically as part of the `ringEval` API bundle (it is listed there).
2. **(fleet / dedup)** consolidate the NagellLutz ↔ HasseWeil verbatim `Universal.lean` fork into
   `Common/`.

---

### Evidence anchors

- This decl: `projects/NagellLutz/LutzNagell/Universal.lean:229–230`; consumed at L237–239
  (`curveRing_map_ringEval`).
- Sibling lemmas in the proof: `ringEval_comp_mk` (L223), `polyEval_comp_eq_specialize` (L226),
  `algebraMap_ring_eq_comp` (L116, `rfl`).
- Underlying defs: `ringEval` (L215, `AdjoinRoot.lift`), `polyEval` (L203), `specialize` (L190),
  `Universal.Ring := curve.CoordinateRing` (L96), `curve` (L84).
- Verbatim duplicate: `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:232`.
- mathlib primitives the proof relies on: `AdjoinRoot.lift`/`lift_mk`/`mk`
  (`.lake/packages/mathlib/Mathlib/RingTheory/AdjoinRoot.lean:280,289,94`);
  `RingHom.comp_assoc` (`…/Mathlib/Algebra/Ring/Hom/Defs.lean:546`).
- No universal-curve scaffold in mathlib: `grep` over `Mathlib/AlgebraicGeometry/EllipticCurve/**`
  empty; only the prose mention `DivisionPolynomial/Basic.lean:36–38`. Docs page for
  `EllipticCurve/Affine/Point.html` confirms `CoordinateRing` carries no such API.
- Direct structural twin (one layer down) and its matching bucket:
  `…/mathlibable/polyEval_comp_eq_specialize.md` → `NO-composable-from-mathlib`.
- Package-level human decision owned by: `…/mathlibable/specialize.md` (`BORDERLINE-needs-human`),
  `…/mathlibable/ringEval.md`, `…/mathlibable/curve.md`.
- Literature: TMF / moduli of Weierstrass curves — arXiv:1312.7394, arXiv:0810.0507; N. Katz,
  *Universal Weierstrass families* (Princeton notes ch. 10).
