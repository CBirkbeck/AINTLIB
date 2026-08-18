# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.point_point`

> **Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz / elliptic curves /
> division polynomials / EDS).** Single declaration. Read-only on `.lean`; this report is the
> only file written.

## 0. Resolution & exact statement

- **Parsed qualified name (from brief):** `WeierstrassCurve.Universal.Jacobian.point_point` — **VERIFIED**.
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:411`.
- **Namespace nesting (confirmed from source):** `namespace WeierstrassCurve` (ZSMul.lean has
  `WeierstrassCurve` opened via the `Universal` re-open; the `Universal` namespace is opened at
  `Universal.lean:86` under `namespace WeierstrassCurve` line 76) → `namespace Universal` →
  `namespace Jacobian` (ZSMul.lean:395, closed line 544). So the fully-qualified name is
  **`WeierstrassCurve.Universal.Jacobian.point_point`**. The parse-time guess matches.

Exact source line:

```lean
lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl
```

Here:
- `Jacobian.point` (`Universal.lean:155`) `:= Jacobian.Point.fromAffine Affine.point` — the project's
  distinguished universal point in Jacobian coordinates.
- `Affine.point` (`Universal.lean:151`) `:= .mk equation_point` — i.e. the mathlib affine point
  `Point.some (polyToField (C X)) (polyToField Y) h` (since `Affine.Point.mk` wraps an `Equation`
  proof into `Nonsingular` and emits `.some`).
- `.point` is mathlib's structure projection `Jacobian.Point.point : PointClass R` (the underlying
  `⟦·⟧`-class of the homogeneous coordinate triple).
- `polyToField : Poly →+* Universal.Field` (`Universal.lean:108`); `C X`, `Y` are the bivariate
  polynomial generators (`Poly := (MvPolynomial Coeff ℤ)[X][Y]`).

**Plain-English statement.** *The underlying Jacobian point-class of the project's distinguished
universal point equals the homogeneous triple `[X : Y : 1]` (with `X,Y` the universal field's
tautological coordinates).* In short: the Jacobian coordinates of `Jacobian.point` are `[X : Y : 1]`.

**Proof.** `rfl` — a pure definitional unfolding (`fromAffine` on the `some` constructor stores
`⟦![X,Y,1]⟧` as its `.point`, and `.point` is a structure projection).

**Kind:** `lemma` (a `rfl`-accessor lemma), not a `def`. (Contrast the sibling **`point.md`**, which
assesses the *object* `Jacobian.point` — a `def`. This report is about the **coordinate lemma**.)

---

## Phase 0 — size gate

Tiny `rfl` accessor lemma. **Classified SMALL** → the lightweight literature pass applies (brief was
not `--exhaustive`). Nevertheless the search below is deliberately thorough because the object it
references (`Jacobian.point`) was a `NO-composable` borderline in the sibling report, and we must rule
out that the *lemma* carries independent mathlib value.

---

## Phase 1 — literature search

| # | Source | Query | Hit? | Finding |
|---|--------|-------|------|---------|
| 1 | WebSearch (general) | "Weierstrass affine point to Jacobian coordinates `[X:Y:1]` fromAffine, generic/universal point" | yes (background only) | The affine→Jacobian embedding `(x,y) ↦ [x : y : 1]` (recover via `x = X/Z², y = Y/Z³`, set `Z=1`) is the **textbook chart inclusion**. It is *not* a named theorem — it is the definition of "Jacobian coordinates with `Z = 1`". |
| 2 | WebSearch (named objects nearby) | division polynomials / homogeneous division polynomials for the generic Weierstrass point | yes | The **named** objects in this vicinity are the *division polynomials* `ψ_n,φ_n,ω_n` (Mazur–Tate, arXiv:1303.4327 *Homogeneous division polynomials*), giving `n•P = [φ_n : ω_n : ψ_n]`. The base case `1•P = [X:Y:1]` (which is what `point_point` records) is the trivial `n=1` instance, not separately named. |
| 3 | EFD (hyperelliptic.org) | Jacobian coordinates standard reference | yes | Confirms `(X:Y:Z) ↔ (X/Z², Y/Z³)`; the `Z=1` representative of an affine point is `[x:y:1]`. Standard, unnamed. |

**Literature verdict:** `point_point` records the **`n = 1` / base representative** of the standard
affine→Jacobian chart. There is **no named theorem** for "the Jacobian coordinates of a given affine
point are `[x:y:1]`"; it is definitional. The genuinely-named neighbours are the *division polynomials*
(handled elsewhere in this overview: `zsmul_point_eq_smulField`, the `φ/ω/ψ` API), not this lemma.

Sources:
- https://arxiv.org/pdf/1303.4327 (Homogeneous division polynomials for Weierstrass elliptic curves)
- https://www.hyperelliptic.org/EFD/oldefd/jacobian.html (Explicit-Formulas DB, Jacobian coords)
- https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf (division polynomials, Sutherland)

---

## Phase 2 — mathlib search (five methods)

Target of the search: is there in mathlib **(a)** this exact lemma, or **(b)** a more general
"`.point` of `fromAffine (some …)`" lemma?

| Method | Query / locus | Result |
|---|---|---|
| [A] `leansearch`-style intent | "Jacobian point of affine point is `[x,y,1]`" | resolves to `fromAffine` + the `Point.point` projection — covered by (b) below. |
| [B] `loogle` signature | `Jacobian.Point.fromAffine _ |>.point = _` ; `(Jacobian.Point.mk _).point = _` | **HIT**: `Jacobian.Point.mk_point` and the `fromAffine_some` `rfl` body. |
| [C] exact?/simp-normal | what `rfl`/`simp` would use to prove `(fromAffine (some x y h)).point = ⟦![x,y,1]⟧` | `Point.fromAffine_some` then `Point.mk_point` (both `rfl`). |
| [D] grep mathlib src | `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean` | `mk_point` (L380, `:= rfl`), `zero_point` (L389), **`fromAffine` (L397–399)** — the `some` branch is `⟨(nonsingularLift_some ..).mpr h⟩`, whose `.point` is `⟦![X,Y,1]⟧` — **`fromAffine_some` (L404, `:= rfl`)**, `fromAffine_some_ne_zero` (L408). |
| [E] name pattern | `point_point`, `fromAffine_some_point`, `*_point` in EC tree, `Universal` namespace | **No** `Universal` namespace anywhere in mathlib's EC tree; **no** named distinguished point; **no** lemma literally named `*_point_point`. |

**Decisive mathlib facts:**

- `WeierstrassCurve.Jacobian.Point.mk_point` (Point.lean:380): `(mk h).point = P` — `rfl`.
- `WeierstrassCurve.Jacobian.Point.fromAffine_some` (Point.lean:404):
  `fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩` — `rfl`. The underlying `PointClass`
  of `Point.some x y h` is `⟦![x, y, 1]⟧` (this is exactly how mathlib's Jacobian `some`/`fromAffine`
  is built).

So the **general statement** behind `point_point` —
`(Jacobian.Point.fromAffine (.some x y h)).point = ⟦![x, y, 1]⟧` —
**is already in mathlib**, factored as `fromAffine_some ⬝ mk_point` (and is itself a single `rfl`).
What `point_point` adds is purely the **specialisation to the project's particular point**
`Affine.point` (coordinates `polyToField (C X), polyToField Y` in `Universal.Field`).

The *object* `Jacobian.point` is **not** in mathlib (no `Universal` namespace, no named point) — this
matches the sibling **`point.md`** finding, which classified the `def` itself as
`NO-composable-from-mathlib`.

---

## Phase 3 — generality analysis

- **Generality knobs on `point_point`:** none. It is pinned to one specific point with one specific
  coordinate pair `(polyToField (C X), polyToField Y)` over one specific ring (`Universal.Field`),
  inside the project's `Universal` scaffolding.
- **Maximally-general standard form:** `(fromAffine (some x y h)).point = ⟦![x,y,1]⟧` for arbitrary
  `x y` over any `Nontrivial` base — and **mathlib already has it** (`fromAffine_some`/`mk_point`).
  `point_point` is the universal-curve instance of that general fact; it cannot be "generalised into
  mathlib" because the general form is the one already present, and stripping the project coordinates
  just *recovers* `fromAffine_some`.
- **Hidden-hypothesis check:** none — `rfl` uses no hypotheses beyond the definitional shapes.

**Generality verdict:** the lemma is a **non-general specialisation**; the general version is in
mathlib. No `YES-but-generalise-first` move exists (generalising = deleting it in favour of
`fromAffine_some`).

---

## Phase 4 — composition check (can ≤3 mathlib calls give it?)

Given the project objects `Jacobian.point` and `Affine.point` (which are themselves project-local,
not mathlib), `point_point` is obtained in **≤2 mathlib lemma applications**:

```lean
-- after unfolding the two project defs:
--   Jacobian.point  = fromAffine Affine.point   (Universal.lean:155, def-unfold)
--   Affine.point    = .some _ _ equation_point  (Universal.lean:151, def-unfold)
example : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := by
  rw [Jacobian.point, Affine.point]      -- unfold project defs
  rw [Point.fromAffine_some]             -- mathlib (rfl)
  -- ⊢ (⟨…⟩ : Point).point = ⟦![…,…,1]⟧   closed by mk_point/rfl
```

In practice the project just writes `:= rfl`, because `fromAffine_some` and `mk_point` are themselves
`rfl`, so the whole chain collapses definitionally. **Either way the content is ≤2 mathlib calls
(`fromAffine_some`, `mk_point`) plus unfolding two project-local definitions.** The lemma carries
**zero mathematical content** of its own beyond reading off a definition.

**Composition verdict:** **COMPOSABLE** from mathlib (`fromAffine_some` + `mk_point`) once the
project's own `Jacobian.point`/`Affine.point` are in scope.

---

## Phase 4.5 — diamond / defeq / API-shape risk

- It is a *lemma* (no instance, no `def`), so no diamond/reducibility concern.
- It is `rfl`, deliberately exposing the `[X:Y:1]` representative — an intended transparency for
  downstream Jacobian-coordinate computations (the same role flagged in `point.md`'s defeq table).
- **Duplication risk (found):** `point_point` is **duplicated verbatim** — identical statement **and**
  identical `rfl` proof — in **`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:477`**.
  Both projects fork the same universal-curve scaffolding. This is a **cross-project dedup target**
  (`Common/`), *not* a mathlib target.
- **Usage:** `grep` finds **no consumers** of `NagellLutz.…point_point` outside its own file/the two
  forks — it is a local convenience/accessor lemma. (Its sibling object `Jacobian.point` *is* used:
  `zsmul_point_ne_zero`/`zsmul_point_ne`/`zsmul_point_eq_smulField` reference `Jacobian.point`; but
  those use the `def`, not this `rfl` lemma.)

---

## Phase 5 — five-bucket verdict

**Category: `NO-composable-from-mathlib`.**

**Rationale.**
- The **general fact** — `.point` of `fromAffine (some x y h)` is `⟦![x,y,1]⟧` — is **already in
  mathlib**, factored as `Jacobian.Point.fromAffine_some` + `Jacobian.Point.mk_point` (both `rfl`,
  Point.lean:404 & :380).
- `point_point` is a **`rfl` specialisation** of that fact to the project's own point
  `Jacobian.point = fromAffine Affine.point` with the project's coordinates
  `(polyToField (C X), polyToField Y)`. Its object lives in the project-local `Universal` namespace,
  which has **no analogue in mathlib** (confirmed: no `Universal` namespace, no named distinguished
  point in the EC tree — consistent with sibling `point.md`, `NO-composable`).
- It is **composable in ≤2 mathlib calls** (`fromAffine_some`, `mk_point`) given the project defs, and
  carries **no mathematical content** of its own (literature: the `[x:y:1]` chart inclusion is
  definitional/unnamed; the *named* neighbours are the division polynomials, handled elsewhere).
- It is also **duplicated** in HasseWeil → a dedup/`Common/` action, reinforcing that it is
  project glue, not a mathlib contribution.

**Why not the other buckets.**
- *NO-mathlib-has-it*: rejected — mathlib does **not** contain this exact lemma (the project's specific
  universal point does not exist in mathlib); it contains the **general** form, which is a different
  (more general) statement. The precise "mathlib already has *this*" bucket would over-claim.
- *YES-add-as-is* / *YES-but-generalise-first*: rejected — there is nothing to add; the maximally
  general version is already in mathlib, and "generalising" this lemma just **is**
  `fromAffine_some`/`mk_point`. Adding the universal-curve instance to mathlib would be pure noise.
- *BORDERLINE-needs-human*: rejected — the call is clear-cut. The sibling `def` `Jacobian.point` was
  the borderline-ish case (still `NO-composable`); this **`rfl` accessor lemma** about that def is
  unambiguously a notch below it. A `rfl` specialisation of an existing mathlib `rfl` lemma is the
  textbook `NO-composable-from-mathlib`.

**One-line verdict:** `rfl` specialisation of mathlib's `fromAffine_some`/`mk_point` to the project's
universal point — composable in ≤2 calls, not for mathlib (and duplicated in HasseWeil → dedup).

---

### Appendix — evidence pointers

- Target: `projects/NagellLutz/LutzNagell/ZSMul.lean:411`.
- `Jacobian.point` def: `projects/NagellLutz/LutzNagell/Universal.lean:155`
  (`:= Jacobian.Point.fromAffine Affine.point`).
- `Affine.point` def: `projects/NagellLutz/LutzNagell/Universal.lean:151` (`:= .mk equation_point`).
- `polyToField`: `projects/NagellLutz/LutzNagell/Universal.lean:108`.
- mathlib `Point` structure + `.point` projection: `…/Jacobian/Point.lean:372`.
- mathlib `mk_point` (`rfl`): `…/Jacobian/Point.lean:380`.
- mathlib `fromAffine` / `fromAffine_some` (`rfl`): `…/Jacobian/Point.lean:397`, `:404`.
- mathlib `Affine.Point.mk` (emits `.some`): `…/Affine/Point.lean:537`; `inductive Point … | some`:
  `…/Affine/Point.lean:469–471`.
- Verbatim duplicate: `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:477`.
- Sibling object report: `projects/NagellLutz/.mathlib-quality/overview/mathlibable/point.md`
  (`Jacobian.point` → `NO-composable-from-mathlib`).
