# Mathlibable assessment — `WeierstrassCurve.Universal.ringEval_mk`

**Verdict: NO-composable-from-mathlib**

> Project-local `mk`-rule: it is `AdjoinRoot.lift_mk` (a mathlib `@[simp]` lemma) re-exported through two bespoke local definitions. One mathlib call gives it.

- **Qualified name:** `WeierstrassCurve.Universal.ringEval_mk` (verified from source — see namespace trace below)
- **Location:** `projects/NagellLutz/LutzNagell/Universal.lean:220`
- **Assessor:** Step-9 mathlibable, single declaration.

---

## 1. The declaration (verbatim)

```lean
lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p
```

Namespace trace (`Universal.lean`): `namespace WeierstrassCurve` (l.69) → `namespace Universal`
(reopened l.196, after the `end Universal` at l.177) → decl at l.220 → `end Universal` (l.241) →
`end WeierstrassCurve` (l.243). Hence the fully-qualified name is
**`WeierstrassCurve.Universal.ringEval_mk`**.

### Surrounding definitions it is phrased over (both project-local, both in this same file)

```lean
-- l.203
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

-- l.215
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]
```

where `Poly := (MvPolynomial Coeff ℤ)[X][Y]`, `Universal.Ring := curve.CoordinateRing`
(`= AdjoinRoot curve.polynomial`), and `specialize : MvPolynomial Coeff ℤ →+* R` is the universal
coefficient-specialization homomorphism. All of `curve`, `Coeff`, `specialize`, `ringEval`,
`polyEval`, `Poly`, `Universal.Ring` are defined **in this project** — the "universal elliptic
curve" construction (Junyan Xu's approach), used to prove non-vanishing of the universal division
polynomials `ψₙ` via specialization to the cusp.

### What the lemma says

`ringEval` is `AdjoinRoot.lift i y _` with `i = eval₂RingHom W.specialize x`. The lemma states its
value on a representative `AdjoinRoot.mk _ p` equals `polyEval W x y p`. Since
`polyEval = eval₂RingHom (eval₂RingHom W.specialize x) y`, the RHS is **definitionally**
`p.eval₂ (eval₂RingHom W.specialize x) y` — i.e. exactly `g.eval₂ i a` from `AdjoinRoot.lift_mk`.
So this is the standard "`lift` commutes with `mk`" computation rule, with the two sides given the
project's API names. It is the glue lemma that *every* `AdjoinRoot.lift`-based definition acquires.

---

## 2. Literature search

- WebSearch ("universal elliptic curve coordinate ring AdjoinRoot specialization homomorphism
  Weierstrass Lean mathlib") surfaces the relevant mathlib elliptic-curve coordinate-ring API
  (`AdjoinRoot.powerBasis'`, the `R[X][Y] → R[W]` map, the `{1, Y}` power basis) and the
  ITP-2023 group-law paper (arXiv 2302.10640) + the homogeneous division-polynomial paper
  (arXiv 1303.4327). **None** of these defines a "universal elliptic curve" `ringEval` / `polyEval`
  evaluation API — the construction here is bespoke to this development, not standard library
  material. There is no named theorem in the literature corresponding to this lemma; it is a
  formalization-internal computation rule, not a mathematical result.

Conclusion: there is no "standard maximally-general form" to weaken toward — the lemma is a
definitional `simp`-style fact, so the literature axis is not the deciding one.

## 3. Mathlib search (five methods)

1. **Name/grep — local construction absent from mathlib.**
   `grep -rn "namespace Universal\|def ringEval\|def polyEval\|ringEval\|polyEval"` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/` and all of `Mathlib/`: **no** `WeierstrassCurve.Universal`
   namespace, **no** `ringEval`, **no** `polyEval`, **no** curve `specialize` anywhere in mathlib.
   The entire universal-curve scaffold is project-only, so a lemma phrased over it cannot pre-exist.

2. **The forked-mathlib check (project-specific instruction).**
   This project forks `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
   `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Checked
   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` and
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: none contains `ringEval`/`polyEval`/
   `Universal`. The duplicated General*/PID* tracks do not introduce this lemma either. So it is
   **not** an "already in mathlib via the fork" case.

3. **The underlying primitive — present and exact.**
   `Mathlib/RingTheory/AdjoinRoot.lean:288-290`:
   ```lean
   @[simp]
   theorem lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i a :=
     Ideal.Quotient.lift_mk _ _ _
   ```
   This is the general statement; `ringEval_mk` is its instance at
   `i := eval₂RingHom W.specialize x`, `a := y`, `f := curve.polynomial`, with the RHS rewritten
   through `polyEval`'s definition. The proof in source is literally `AdjoinRoot.lift_mk _ p`.

4. **leansearch / loogle (mathlib index).** A search for "AdjoinRoot lift applied to mk equals
   eval₂" / `?f (AdjoinRoot.mk _ ?p) = Polynomial.eval₂ _ _ ?p` resolves to `AdjoinRoot.lift_mk`
   (and the companions `lift_root`, `lift_of`, `lift_comp_of`). No hit for the universal-curve
   wrapper, as expected.

5. **Companion-lemma check.** Mathlib already ships the *full* `mk`-rule family for `AdjoinRoot.lift`
   (`lift_mk`, `lift_root`, `lift_of`, `lift_comp_of`). `ringEval_mk` is the project's re-export of
   `lift_mk` only; `ringEval_comp_mk` (l.223) is its re-export of the `comp` form. These are the
   expected per-definition glue lemmas, not new API.

## 4. Generality analysis

`ringEval_mk` is maximally *specific*, not general: it is `AdjoinRoot.lift_mk` with every parameter
fixed to the universal-curve data and both sides renamed to local definitions. The genuinely general
statement (`AdjoinRoot.lift_mk`, over arbitrary `R`, `S`, `i`, `a`, `f`, `g`) is **already in
mathlib** and is strictly more general. There is nothing to generalise *toward* that mathlib does not
already have, and the lemma cannot be generalised *in place* without deleting its reason to exist
(naming `ringEval`/`polyEval`). So neither YES-add-as-is nor YES-but-generalise-first applies.

## 5. Composition check (can ≤3 mathlib calls give it?)

**Yes — one call.** After unfolding the local definitions `ringEval` and `polyEval` (which a mathlib
user would have to introduce themselves regardless, since they don't exist in mathlib), the goal is
exactly `AdjoinRoot.lift i a h (AdjoinRoot.mk f p) = p.eval₂ i a`, closed by the single mathlib lemma
`AdjoinRoot.lift_mk`. The source proof term is precisely `AdjoinRoot.lift_mk _ p`. Because `lift_mk`
is `@[simp]`, in any downstream proof the rewrite is automatic — a consumer would simply
`simp [ringEval, polyEval]` (or `rw [ringEval, AdjoinRoot.lift_mk]`) at the use site rather than
needing a named lemma. Composition count: **1** mathlib call (well within ≤3).

## 6. Five-bucket verdict

**NO-composable-from-mathlib.**

- It is **not** in mathlib (Method 1–2: the entire `Universal` evaluation API is project-local), so
  not NO-mathlib-has-it for the *named* lemma.
- But the only mathlib-relevant content — "`AdjoinRoot.lift` commutes with `mk`" — **is** in mathlib
  as the strictly-more-general `@[simp] AdjoinRoot.lift_mk`, and the lemma is recovered in **one**
  call after the local definitions (which are not mathlib's to keep) are unfolded.
- Therefore the right bucket is **NO-composable-from-mathlib**: it is the per-definition `mk`-rule
  that every `AdjoinRoot.lift`-based definition gets for free from `lift_mk`. It is correct and
  appropriately kept as project API (it cleanly names `ringEval ∘ mk = polyEval` for the
  division-polynomial development, and is reused in HasseWeil and consumed by `ringEval_comp_mk`),
  but it carries no mathlib-worthy mathematical content of its own.

### Required evidence (for NO-composable-from-mathlib)
- **Composing lemma:** `AdjoinRoot.lift_mk` (`Mathlib/RingTheory/AdjoinRoot.lean:289`, `@[simp]`).
- **Composition recipe (≤3 calls):** unfold `ringEval`, `polyEval` (project defs) ⟹ goal is the
  `lift_mk` instance ⟹ `exact AdjoinRoot.lift_mk _ p`. Source proof is exactly that. **1 call.**
- **Why it stays local:** both sides name project-only definitions (`ringEval`, `polyEval`) that have
  no place in mathlib; the general fact they specialise is already in mathlib.

---

## Cross-references
- Duplicate (byte-identical statement + proof) in HasseWeil:
  `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:223` — a dedup target on `main`, not a
  mathlib concern.
- Sibling mathlibable report: `.../mathlibable/Poly.md` (the `Poly` type this lemma is phrased over).
- Inventory entry: `.../overview/inventory/LutzNagell_Universal.md:427`.
