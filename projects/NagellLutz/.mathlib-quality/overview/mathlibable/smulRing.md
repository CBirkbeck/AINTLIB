# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulRing`

> Middle member of the universal division-polynomial 3-tuple triple
> `smulPoly` / **`smulRing`** / `smulField` (`LutzNagell/ZSMul.lean:413–418`). This report mirrors
> the already-assessed `curve*` base-change triple: `curve.md` (the genuinely-new object) →
> `YES-add-as-is`; `curvePoly.md`/`curveRing.md`/`curveField.md` → `NO-composable-from-mathlib`.
> `smulRing` is structurally identical to `curveRing`: a one-`∘` post-composition (here with
> `AdjoinRoot.mk`) of the "new" object `smulPoly`. Verdict: **NO-composable-from-mathlib**.

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoning from source)
- decl `WeierstrassCurve.Universal.Jacobian.smulRing`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:416`
- kind:                      `abbrev`  (reducible — a function `ℤ → (Fin 3 → Universal.Ring)`, not a `Prop`)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms of
  division polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval`, i.e.
  `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates, via the universal curve.

**Qualified-name verification.** `ZSMul.lean` opens `namespace WeierstrassCurve` (line 76) →
`namespace Universal` (line 86) → `namespace Jacobian` (line 395). `smulRing` is declared at line 416
inside all three. Parsed qualified name `WeierstrassCurve.Universal.Jacobian.smulRing` is
**CONFIRMED**.

---

### Statement (Phase 1)

```lean
/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
```

`smulRing n` is the 3-tuple `(φₙ, ωₙ, ψₙ)` of **universal** division polynomials, viewed as a triple
of elements of the **universal coordinate ring** `Universal.Ring = curve.CoordinateRing =
ℤ[A₁,A₂,A₃,A₄,A₆][X][Y]/⟨P⟩` (`P` = the Weierstrass polynomial). Concretely it is the bundle
`smulPoly n = ![φₙ, ωₙ, ψₙ] : Fin 3 → Poly` (in the bivariate polynomial ring
`Poly = ℤ[A₁..A₆][X][Y]`) post-composed, componentwise, with mathlib's quotient map
`AdjoinRoot.mk _ : Poly → Universal.Ring`.

Mathematically these are the prospective Jacobian coordinates of `n • (X, Y)` on the universal
pointed curve, **at the level of the coordinate ring** (not yet inverted): the file later shows
`(n • point).point = ⟦smulField n⟧` and proves the doubling/addition identities `dblXYZ_smulRing`,
`addXYZ_smulRing`, `smulRing_neg` directly in `Universal.Ring`, then transports them to a concrete
curve by `ringEval` (`ringEval_comp_smulRing : ringEval eqn ∘ smulRing n = smulEval W x y n`). The
ring-level version exists precisely because `Universal.Ring → Universal.Field` is injective, so the
polynomial identities can be proven once and specialized.

So `smulRing` is to `smulPoly` exactly as `curveRing` is to `curve`: take the genuinely-new object
(`smulPoly`, the bundled division-polynomial triple) and apply one mathlib map (`AdjoinRoot.mk`) to
land in the coordinate ring. `smulField n = polyToField ∘ smulPoly n` is the same triple over the
fraction field.

---

### Literature search (Phase 3)

The mathematical content is completely standard. The multiplication-by-`n` map on an elliptic curve
is given in Jacobian coordinates by the **division-polynomial triple** `[n]P = (φₙ : ωₙ : ψₙ)`, with
`φₙ = x ψₙ² − ψₙ₊₁ ψₙ₋₁`, `ωₙ = (4y)⁻¹(ψₙ₊₂ ψₙ₋₁² − ψₙ₋₂ ψₙ₊₁²)`, and `ψₙ` the division polynomials
(Silverman, *Arithmetic of Elliptic Curves*, Ex. 3.7; MIT 18.783 Lecture 6; Washington,
*Elliptic Curves* §3.2). The literature names:

- the three **polynomial families** `ψ, φ, ω` (individually), and
- the **affine/Jacobian multiplication formula** `[n]P = (φₙ/ψₙ² , ωₙ/ψₙ³)` resp. `(φₙ : ωₙ : ψₙ)`.

What the literature does **not** introduce is a separate named object for "the triple `(φₙ, ωₙ, ψₙ)`
reduced modulo the Weierstrass relation in the universal coordinate ring." That is a Lean-side
bookkeeping device: the standard proof reasons about the formula directly, and the universal
coordinate ring `ℤ[A₁..A₆,X,Y]/⟨P⟩` is itself a formalisation convenience (the "generic point"
trick) rather than a textbook-named gadget. Conclusion: `smulRing` packages standard content but is
**not** itself a named mathematical object; it is an organisational `abbrev` two steps removed from
the literature object (`smulPoly`, and underneath it `ω`/`φ`/`ψ` and `curve`).

Sources:
- MIT 18.783, *Isogeny kernels and division polynomials* — https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf
- *Sequences associated to elliptic curves* (EDS survey) — https://arxiv.org/pdf/1909.12654

---

### Generality analysis (Phase 4)

`smulRing` is **specialised by design, and necessarily so** — it is *defined over the one universal
ring* `Universal.Ring`. It is not a `∀ R`-parametric construction; the entire point of the
"universal" track is that there is a single initial object (`ℤ[A₁..A₆,X,Y]/⟨P⟩`) over which one
proves the identities once. So there is no assumption to weaken: the universal ring is already the
most-general base (it specializes to every `(W, x, y)` via `ringEval`). This is inherited generality,
identical to the `curve`/`curveRing` situation. **No generalise-first target.**

A `∀ R`-parametric reformulation would be `fun n ↦ ![W.φ n, W.ω n, W.ψ n]` (over an arbitrary
`WeierstrassCurve.Affine R`, in `R[X][Y]`) — but that is just the bundling `smulPoly` re-stated, and
the `Ring`-valued `AdjoinRoot.mk ∘ —` form is meaningful only for the universal curve (a generic
`R[X][Y]/⟨P⟩` is exactly the universal construction base-changed). So generalising does not yield a
new mathlib object; it collapses back onto `smulPoly` + a base change.

---

### Mathlib search (Phase 5 — five methods)

Target: is `smulRing` (or anything subsuming it) already in mathlib?

1. **Name guess / grep.** `grep -rn "smulRing\|smulPoly\|smulField\|smulEval"` over all of
   `.lake/packages/mathlib/Mathlib/` → **0 matches.** (Corroborated by the sibling report
   `smulY_sub_negY.md`: a prior sweep of `smulX/smulY/smulRing/Universal.Ring/Universal.Field/
   polyToField/pointedCurve` over `Mathlib/` returned 0.)
2. **Component objects.**
   - `WeierstrassCurve.ψ` — **present** (`DivisionPolynomial/Basic.lean:401`).
   - `WeierstrassCurve.φ` — **present** (`Basic.lean:448`).
   - `WeierstrassCurve.ω` — **ABSENT** from mathlib's `DivisionPolynomial/Basic.lean`; supplied by
     this project at `DivisionPolynomialOmega.lean:74`. (This is the forked/added piece.)
   - The **bundled triple** `![φ, ω, ψ]` (`Fin 3 → …`) — **absent** (no `Fin 3`/3-tuple packaging of
     division polynomials anywhere in mathlib's EllipticCurve dir).
3. **Universal coordinate ring.** `Universal.Ring`, `Universal.curve`, `curve.CoordinateRing` for the
   universal curve, `polyToField`, `ringEval`, the universal `ℤ[A₁..A₆,X,Y]/⟨P⟩` — **none in
   mathlib** (the `Universal` namespace and `pointedCurve` machinery are wholly project-local, per
   `Universal.lean`'s own docstring and `curveRing.md`/`curveField.md`). `CoordinateRing` and
   `AdjoinRoot.mk` exist as general tools, but not this instance.
4. **loogle / leansearch (mathlib index).** A definition of shape
   `ℤ → (Fin 3 → AdjoinRoot _)` built from division polynomials returns nothing; there is no
   division-polynomial-tuple-in-a-quotient-ring object indexed.
5. **Downstream/Jacobian.** Mathlib's `Jacobian/` has `dblXYZ`, `addXYZ`, `dblZ`, `addZ` (the group
   law in Jacobian coordinates) — the *operations* `smulRing` is fed into — but **not** the
   division-polynomial coordinate witnesses themselves.

**Conclusion:** `smulRing` is **not in mathlib**, and neither are its essential ingredients
(`ω`, the bundled triple, the universal coordinate ring). The building blocks `ψ`, `φ`,
`AdjoinRoot.mk`, `CoordinateRing` are present. → rules out `NO-mathlib-has-it`.

---

### Composition check (Phase 6) — can ≤3 mathlib calls give it?

`smulRing` is *literally defined* as a one-step composition:

```lean
smulRing n  =  (AdjoinRoot.mk curve.polynomial) ∘ smulPoly n          -- 1 mathlib call (`AdjoinRoot.mk`)
            =  AdjoinRoot.mk _ ∘ ![curve.φ n, curve.ω n, curve.ψ n]   -- the underlying triple
```

Once the genuinely-new bundling `smulPoly n = ![φₙ, ωₙ, ψₙ]` is in hand, `smulRing n` is obtained by
post-composing with mathlib's quotient homomorphism `AdjoinRoot.mk` — exactly **one** function call,
zero new mathematics. (Its sibling `smulField` is the same with `polyToField` in place of
`AdjoinRoot.mk`; the link lemma `algebraMap_comp_smulRing` is one `ext; fin_cases; rfl`.)

The only non-mathlib inputs are the project-local objects `curve.ω`, `curve.φ`, `curve.ψ` and
`Universal.Ring`/`AdjoinRoot.mk curve.polynomial`. Of these the substantive new content is `ω`
(omega division polynomial — its own mathlibable question), the bundling into a `Fin 3` tuple
(`smulPoly`), and the universal coordinate ring (`curve`/`curveRing`, already assessed). Given those,
`smulRing` adds nothing beyond `_ ∘ AdjoinRoot.mk`.

→ **COMPOSABLE** in 1 mathlib call from `smulPoly`. This is the textbook `NO-composable-from-mathlib`
shape, identical to `curveRing = curve.baseChange Universal.Ring` (one `baseChange` call from
`curve`).

---

### Diamond / defeq risk (Phase 4.5)

**LOW.** `smulRing` is an `abbrev`, so it is reducible and "leaks" to `AdjoinRoot.mk _ ∘ smulPoly n` —
intended here (the proofs `simp_rw [smulRing, …]` rely on unfolding). No `instance` is anchored on
the name, so there is no priority/diamond exposure. Moot anyway under a NO bucket.

---

### Usage footprint (Phase 7 context)

`smulRing` is used **only inside `ZSMul.lean`** (≈8 occurrences: `algebraMap_comp_smulRing`,
`dblXYZ_smulRing`, `smulRing_neg`, `addXYZ_smulRing`, `addXYZ_smulRing₁`, `ringEval_comp_smulRing`,
…). No `.lean` file outside `ZSMul.lean` references it (all external hits are `.mathlib-quality/`
docs). It is a private organisational handle for one file's universal-ring identity proofs — not a
cross-project interface. This reinforces NO: it is not a reusable API surface, it is scaffolding for
the `zsmul_eq_smulEval` deliverable.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulRing`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- **Literature (Phase 3):** standard content (division-polynomial triple `(φₙ, ωₙ, ψₙ)` =
  Jacobian coordinates of `[n]P`), but the literature names the *triple* and the *formula*, not a
  separate "triple-in-the-universal-coordinate-ring" object. `smulRing` is two steps removed
  (post-compose `smulPoly` with `AdjoinRoot.mk`).
- **Generality (Phase 4):** maximally general by construction (the universal ring is initial); no
  assumption to weaken. A `∀ R` reformulation collapses to `smulPoly` + a base change — no new mathlib
  object. No generalise-first target.
- **Defeq/diamond (Phase 4.5):** LOW — intended `abbrev` reducibility, no instance on the name. Moot.
- **Mathlib search (Phase 5):** **not in mathlib**; nor are `ω`, the bundled triple, or the universal
  coordinate ring. Present building blocks: `ψ`, `φ`, `AdjoinRoot.mk`, `CoordinateRing`,
  `dblXYZ`/`addXYZ`. Rules out `NO-mathlib-has-it`.
- **Composition (Phase 6):** **COMPOSABLE in one mathlib call** — `AdjoinRoot.mk _ ∘ smulPoly n`,
  exactly its definition. Sibling `smulField` = same with `polyToField`; link lemma is `rfl`.

**Rationale (one line):** Not in mathlib, but it is literally `AdjoinRoot.mk ∘ smulPoly` — one mathlib
call over the project's bundled division-polynomial triple; composable, so NO.

**Action / handoff:** Do **not** propose `smulRing` as a standalone mathlib addition. It is
`NO-composable-from-mathlib`, the exact analogue of `curveRing` (→ `NO-composable`) within the
`smulPoly`/`smulRing`/`smulField` triple. The mathlib-relevant questions in this cluster live with
the *underlying* objects: `ω` (the omega division polynomial — genuinely missing from mathlib's
`DivisionPolynomial/Basic`), the universal curve `curve` (assessed → `YES-add-as-is`) and its
coordinate ring, and the bundled triple / multiplication formula `smulPoly` /
`zsmul_eq_smulEval`. If those land in mathlib, `smulRing` is recovered by a one-line
`AdjoinRoot.mk _ ∘ smulPoly n` and should *not* be re-named.
