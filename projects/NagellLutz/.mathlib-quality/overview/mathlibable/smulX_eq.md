# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_eq`

## Verdict: **BORDERLINE-needs-human**

One-line rationale: the *math* is a trivial field-arithmetic corollary of
mathlib's existing `φ = Xψₙ²−ψₙ₊₁ψₙ₋₁`, but it is stated in the project's bespoke
`smulX`/`ψᵤ` universal-curve vocabulary that mathlib lacks — so it can only ride
along with that whole development, whose packaging is the (already-flagged) human call.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.smulX_eq`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:176`
- kind:                      `lemma` (inside `noncomputable section`)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)`
  (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any integer `n` and nonsingular affine point `P`.

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157); `lemma smulX_eq` at line 176. The
parsed name `WeierstrassCurve.Universal.Affine.smulX_eq` is **correct**.

---

### Statement (Phase 1)

```
lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2
```

Here (all bespoke to the project, see the sibling `smulX.md` report):
- `Universal.Field = Frac(Universal.Ring)`, `Universal.Ring = ℤ[A₁..A₆,X,Y]/⟨W_univ⟩`
  — the function field of the **universal** Weierstrass curve over ℤ.
- `polyToField : R₀[X,Y] → Universal.Field` the structure map; `curve` the universal curve.
- `smulX n := polyToField (curve.φ n) / (ψᵤ n)^2` — candidate x-coordinate of `n•(X,Y)`.
- `ψᵤ n := polyToField (curve.ψ n)` — the n-th division polynomial in the field.
- `smulX 1 = polyToField (C X)` (the generic x-coordinate, by `smulX_one`).

**Math content.** Since `smulX n = φₙ/ψₙ²` and `smulX 1 = X`, the statement is exactly

  `φₙ/ψₙ² = X − ψₙ₊₁·ψₙ₋₁ / ψₙ²`   (for `ψₙ ≠ 0`),

i.e. the elementary algebraic rearrangement of the **definition of the division
polynomial `φ`**:

  `φₙ = X·ψₙ² − ψₙ₊₁·ψₙ₋₁`.

This is the classical formula `x(nP) = φₙ(x)/ψₙ(x)²` written with the standard
`φₙ` expansion (Wikipedia "Division polynomials"; Silverman AEC III; Washington §3.2).

Hypotheses: `n ≠ 0` (so `ψₙ ≠ 0`, justifying division by `ψₙ²` — `ψᵤ_ne_zero hn`).

Proof (4 lines): `rw [smulX, eq_sub_iff_add_eq]`; `simp only [φ, ψᵤ, map_sub,
map_mul, map_pow, ← add_div]`; `rw [div_eq_iff (pow_ne_zero 2 (ψᵤ_ne_zero hn)),
smulX_one]`; `abel`. The single non-trivial fact consumed is the **mathlib**
identity `curve.φ n = C X * curve.ψ n ^ 2 - curve.ψ (n+1) * curve.ψ (n-1)`
(`WeierstrassCurve.φ`, definitional), pushed through the ring map and the field.

---

### Size classification (Phase 2a)

Verdict: **BIG** (member of a BIG development).
Reason: a small API lemma, but a load-bearing step of a *main result*
(`zsmul_eq_smulEval`, named in the module docstring summary) built on a **new
mathematical structure mathlib lacks** (the universal Weierstrass curve + its
function field). Literature width is therefore EXHAUSTIVE regardless of the
lemma's own size.

### One-line check (Phase 2b)

Body: 4 substantive proof lines; kind is `lemma`. Not a `def`, so the one-liner
`def`-exemption framework does not apply. This is a normal short proof.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "division polynomial x-coordinate nP formula φₙ = x ψₙ² − ψₙ₊₁ψₙ₋₁" | yes | `x(nP) = fₙ(x)/gₙ(x)` with `fₙ = X ψₙ² − ψₙ₋₁ψₙ₊₁` | Wikipedia "Division polynomials"; arXiv:2102.07573 (EDS recurrences), arXiv:1801.02664; matches verbatim |
| 2 | WebSearch (mathlib / in-flight PR) | "mathlib4 WeierstrassCurve universal curve zsmul_eq division polynomial PR Junyan Xu EDS" | partial | mathlib `DivisionPolynomial/Basic` (φ, ψ, Φ, preΨ); NO universal layer, NO zsmul formula | docs confirm the *fixed-curve* `φₙ = C X * ψₙ² − ψₙ₊₁ψₙ₋₁` exists; the `smulX`/universal/zsmul layer is not upstream |
| 3 | ChatGPT MCP | (down per task) | n/a | — | substituted by WebSearch×2 + vendored-mathlib grep + sibling report |

Literature conclusion: the underlying mathematics (`x(nP) = X − ψₙ₊₁ψₙ₋₁/ψₙ²`) is
**fully standard and elementary** — it is just the `φ`-definition divided by `ψₙ²`.

---

### Mathlib search-status

[A] Lean-Finder/LeanSearch/Loogle index — unavailable in this environment (deferred tools not present); substituted by exhaustive grep over the **vendored mathlib source** (authoritative) + doc-fetch.
[B] Grep `smulX`/`ψᵤ`/`polyToField`/`Universal.Field`/`zsmul_eq_smul` over `.lake/packages/mathlib/Mathlib/` — **no hits**. No `Universal` EC namespace, no `Universal.Field`, no `smulX`, no n•P coordinate formula upstream.
[C] The **stated form** of `smulX_eq` is therefore **not expressible in mathlib today** — its subject `smulX`, `ψᵤ`, and `Universal.Field` do not exist upstream.
[D] The **mathematical content** *is* present as building blocks: `WeierstrassCurve.φ` is defined in mathlib as
  `protected noncomputable def φ (n : ℤ) : R[X][Y] := C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:448-449`).
  This is *exactly* the identity `smulX_eq` rearranges. Mathlib also has `Affine.CoordinateRing`, `Affine.FunctionField = FractionRing CoordinateRing`, and `Affine.CoordinateRing.mk_φ`/`mk_ψ` for a **fixed** curve — but neither the universal-over-ℤ curve nor any `n•P` x-coordinate equation.

Concluded: the lemma **as stated is not in mathlib** (its vocabulary is absent);
its **content is a one-step corollary of mathlib's `φ` definition**.

---

### Generality analysis (Phase 4)

Current form: **MAXIMALLY GENERAL** in its own setting — it lives over the
universal ring (the initial object among Weierstrass bases), and the `n ≠ 0`
hypothesis is exactly the minimal one (division by `ψₙ²` needs `ψₙ ≠ 0`, and
`ψᵤ n ≠ 0 ⟺ n ≠ 0`). Nothing to weaken; 0 weakening opportunities.

Modern-idiom check: the only organizational question is the *same packaging
question* the sibling `smulX.md` report raises — whether the universal coordinate
maps should be bundled. That is a property of the **development**, not of this
lemma. No weakening / reformulation of `smulX_eq` itself is available.

---

### Diamond / defeq risk (Phase 4.5)

Overall: **NONE**. It is a `Prop`-valued lemma (an equation in a fixed field), no
instances, no reducibility, no universe/coercion concerns.

---

### Call sites (Phase 5)

Internal (NagellLutz): used by `smulX_two` (line 184) and `smulX_sub_smulX`
(line 188), which in turn drive `smulX_sub_sub_smulX_add`, `smulX_ne_smulX`,
`smulX_eq_smulX_iff`, … i.e. it is a genuine internal API lemma of the ~30-lemma
`smulX_*` block that proves `zsmul_point_eq_smulX_smulY → zsmul_eq_smulEval`.

External: the **HasseWeil project carries a verbatim duplicate** —
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:251` (`lemma
smulX_eq …`), used at lines 266 and 275 of that file. This duplication is itself
evidence the construction is reusable *and* currently fork/duplicate code (a
standing AINTLIB dedup concern).

---

### Composition check (Phase 6)

Can the **math** be derived from mathlib in ≤3 chained calls? **Yes** (given the
universal layer exists to state it in):

1. `WeierstrassCurve.φ` (mathlib def): `φₙ = C X * ψₙ² − ψₙ₊₁ψₙ₋₁` — push through `polyToField` (ring-hom `map_sub/map_mul/map_pow`).
2. `div_eq_iff` / `eq_sub_iff_add_eq` with `pow_ne_zero … (ψᵤ_ne_zero hn)` — clear the `ψₙ²` denominator (mathlib field arithmetic).
3. `abel` / `ring` to finish.

So the proposition is a **≤3-call composition of mathlib primitives** — there is
no new mathematics in `smulX_eq` beyond mathlib's `φ` definition.

**BUT the composition can only be *written down* inside the bespoke
`smulX`/`ψᵤ`/`polyToField`/`Universal.Field` layer**, which mathlib does not have
(per Phase 5 / sibling `smulX.md`). The statement is inseparable from that layer:
delete `smulX` and `ψᵤ` and the lemma has no subject. Hence it is NOT a
free-standing "composable" addition one would file against today's mathlib — it
is glued to a development that must be upstreamed (or not) as a unit.

Conclusion: **content-composable, but not statement-separable from a missing layer.**

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_eq`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): the identity `x(nP) = X − ψₙ₊₁ψₙ₋₁/ψₙ²` is fully standard and elementary (Wikipedia, Silverman, Washington); mathlib already encodes its core as the **definition** of `WeierstrassCurve.φ`.
- Mathlib search (Phase 5): the lemma **as stated** is absent (no `smulX`/`ψᵤ`/`Universal.Field` upstream); its **content** is a one-step corollary of mathlib's `φ` def.
- Generality (Phase 4): MAXIMALLY GENERAL; minimal hypothesis `n ≠ 0`; only the (development-level) packaging question is open.
- Composition (Phase 6): the *proposition* is ≤3 mathlib calls, but **only statable inside the bespoke universal layer** mathlib lacks — so it is not a self-contained "composable-from-mathlib" PR target; it rides with `smulX`.

**Rationale.**
`smulX_eq` sits exactly on the seam between two buckets:

- It leans **NO-composable-from-mathlib**: its mathematical content adds nothing
  over mathlib's existing `φ = Xψₙ²−ψₙ₊₁ψₙ₋₁`; it is that identity divided by
  `ψₙ²` in the fraction field — three mathlib calls (`map_*` + `div_eq_iff` +
  `abel`). A reviewer who *already had* the universal layer would call this a
  trivial `simp`/`field_simp` corollary, not new API worth a standalone PR.

- It is pushed to **BORDERLINE-needs-human** because it is **not separable** from
  the bespoke `smulX`/`ψᵤ`/`polyToField`/`Universal.Field` infrastructure, whose
  anchor definition `smulX` was itself verdicted **BORDERLINE-needs-human** in
  the sibling report `…/mathlibable/smulX.md`. You cannot even *state*
  `smulX_eq` in mathlib without first deciding whether/how to upstream that
  universal-curve layer (free-standing `smulX`/`smulY` defs vs. a bundled
  generic-point scalar-multiplication object). That packaging decision determines
  whether `smulX_eq` survives at all, survives renamed, or collapses into a
  `simp` lemma — a judgment a mathlib EC maintainer makes, not one this skill
  should make alone.

The correct unit of upstreaming is **the whole universal-curve + n•P-formula
development** (`Universal.Ring/Field`, `curve`, `polyToField`, `ψᵤ`, `smulX`,
`smulY`, `zsmul_eq_smulEval`), and `smulX_eq` is a small lemma riding along with
it — "belongs iff `smulX` does, modulo packaging." So it inherits the sibling's
BORDERLINE verdict rather than getting an independent YES/NO.

**Numbered questions (for the user / a mathlib reviewer):**
1. Is the whole `Universal` Weierstrass-curve layer (incl. `smulX`/`ψᵤ` and
   `zsmul_eq_smulEval`) being upstreamed? If yes, `smulX_eq` rides along.
2. If `smulX`/`smulY` are kept as free-standing defs, keep `smulX_eq` as a named
   lemma; if they are bundled, `smulX_eq` likely collapses to a `simp`/`field_simp`
   corollary of mathlib's `φ` def — which form is wanted?
3. Is there an in-flight mathlib PR (likely the original division-polynomial /
   EDS author) for the universal curve + zsmul formula? If so this is
   **NO-mathlib-has-it (pending)** and the project should track that PR.
4. Independent of mathlib: the verbatim NagellLutz↔HasseWeil duplication of the
   `smulX_*` block (`HasseWeil/…/Auxiliary/DivisionPolynomial.lean:251`) should be
   consolidated into AINTLIB `Common/` — file a dedup ticket now?

**Next action:** answer Q1–Q3 (especially Q3 — check for an open mathlib PR on
the universal curve / n•P formula). Treat the *whole universal-curve development*
as the PR unit; do not upstream `smulX_eq` in isolation. File the AINTLIB dedup
ticket regardless.

Sources:
- [Division polynomials — Wikipedia](https://en.wikipedia.org/wiki/Division_polynomials)
- [A recurrence relation for elliptic divisibility sequences (arXiv:2102.07573)](https://arxiv.org/pdf/2102.07573)
- [On Division Polynomial PIT and Supersingularity (arXiv:1801.02664)](https://arxiv.org/pdf/1801.02664)
- [mathlib4 — Division polynomials of Weierstrass curves](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- mathlib source: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:448-449` (`WeierstrassCurve.φ`)
- sibling report: `projects/NagellLutz/.mathlib-quality/overview/mathlibable/smulX.md`
