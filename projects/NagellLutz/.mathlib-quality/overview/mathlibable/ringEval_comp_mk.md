# Mathlibable assessment — `WeierstrassCurve.Universal.ringEval_comp_mk`

**Verdict: NO-composable-from-mathlib**

> The bundled `comp`-form of `AdjoinRoot.lift_mk`, over two bespoke local defs. `RingHom.ext (lift_mk …)` gives it — the exact pattern mathlib uses for `lift_comp_of`.

- **Qualified name:** `WeierstrassCurve.Universal.ringEval_comp_mk` (verified from source — see namespace trace below)
- **Location:** `projects/NagellLutz/LutzNagell/Universal.lean:223`
- **Assessor:** Step-9 mathlibable, single declaration.

---

## 1. The declaration (verbatim)

```lean
lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)
```

Namespace trace (`Universal.lean`): `namespace WeierstrassCurve` (l.69) → `namespace Universal`
(reopened l.196, after the `end Universal` at l.177) → decl at l.223 → `end Universal` (l.241) →
`end WeierstrassCurve` (l.243). Hence the fully-qualified name is
**`WeierstrassCurve.Universal.ringEval_comp_mk`**.

Binders in scope at l.223: `variable {R} [CommRing R] (W : WeierstrassCurve R)` (l.186),
`variable (x y : R)` (l.198), `variable {W x y} (eqn : Affine.Equation W x y)` (l.210). So
`eqn : Affine.Equation W x y` is the hypothesis that `(x, y)` lies on `W`, which is exactly what
makes `ringEval` well-defined.

### Surrounding definitions it is phrased over (both project-local, both in this same file)

```lean
-- l.203
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

-- l.215
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

-- l.220 (the unbundled companion this lemma bundles)
lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p
```

where `Poly := (MvPolynomial Coeff ℤ)[X][Y]`, `Universal.Ring := curve.CoordinateRing`
(`= AdjoinRoot curve.polynomial`), and `specialize : MvPolynomial Coeff ℤ →+* R` is the universal
coefficient-specialization homomorphism. All of `curve`, `Coeff`, `specialize`, `ringEval`,
`polyEval`, `Poly`, `Universal.Ring`, `ringEval_mk` are defined **in this project** — the "universal
elliptic curve" construction (Junyan Xu's approach), used to prove non-vanishing of the universal
division polynomials `ψₙ` via specialization to the cusp.

### What the lemma says

`ringEval_comp_mk` is the **bundled (`RingHom`-level, composition) form** of `ringEval_mk` (l.220).
`ringEval_mk` is the pointwise rule `ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p`;
`ringEval_comp_mk` packages it as an equality of ring homomorphisms
`(ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y`, proved by `RingHom.ext` from the pointwise
version. Since `ringEval = AdjoinRoot.lift i y _` with `i = eval₂RingHom W.specialize x`, and
`polyEval = eval₂RingHom (eval₂RingHom W.specialize x) y`, this is precisely "`AdjoinRoot.lift`
composed with `AdjoinRoot.mk` equals `eval₂`", i.e. the `comp` form of `AdjoinRoot.lift_mk`, with
the two sides given the project's API names. It is the glue lemma that lets the `algebraMap`
factorization rewrites fire (see §2).

---

## 2. Role in the project (not dead code)

The `comp` spelling is exactly what downstream rewrites need (a pointwise `simp` lemma would not
fire against a `RingHom.comp` goal). Consumers:

- `ringEval_comp_eq_specialize` (l.229-230):
  ```lean
  lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
    rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]
  ```
  Here `algebraMap_ring_eq_comp` rewrites `algebraMap … Universal.Ring` into a form ending in
  `AdjoinRoot.mk _`, and `ringEval_comp_mk` then collapses `(ringEval eqn).comp (AdjoinRoot.mk _)`
  to `polyEval`.
- `ZSMul.lean:561`: `rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]`.
- A **byte-identical** copy lives in the sibling HasseWeil project
  (`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:226`), consumed there at
  `Auxiliary/Universal.lean:233` and `Auxiliary/DivisionPolynomial.lean:638`. So it is duplicated
  across the consolidation fork, not unique — a `main`-side dedup target, not a mathlib concern.

## 3. Literature search

- WebSearch ("universal elliptic curve coordinate ring AdjoinRoot specialization homomorphism
  Weierstrass Lean mathlib") surfaces the mathlib elliptic-curve coordinate-ring API
  (`AdjoinRoot.powerBasis'`, the `R[X][Y] → R[W]` map, the `{1, Y}` power basis) and the ITP-2023
  group-law paper (arXiv 2302.10640) plus the homogeneous division-polynomial paper (arXiv
  1303.4327). **None** of these defines a "universal elliptic curve" `ringEval` / `polyEval`
  evaluation API — the construction here is bespoke to this development. There is no named theorem in
  the literature corresponding to this lemma; it is a formalization-internal computation rule (the
  universal property of `R[X]/(f)`: a hom out of the quotient, precomposed with the quotient
  projection, equals the hom out of `R[X]` it was lifted from), not a mathematical result.

Conclusion: there is no "standard maximally-general form" to weaken toward on the literature axis —
the lemma is a definitional `comp`-rule, so generality is decided purely against mathlib's
`AdjoinRoot` API (§4–§5).

## 4. Mathlib search (five methods)

1. **Name/grep — local construction absent from mathlib.**
   `grep -rn "namespace Universal\|def ringEval\|def polyEval\|ringEval\|polyEval"` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/` and all of `Mathlib/`: **no** `WeierstrassCurve.Universal`
   namespace, **no** `ringEval`, **no** `polyEval`, **no** curve `specialize` anywhere. The entire
   universal-curve scaffold is project-only, so a lemma phrased over it cannot pre-exist by name.

2. **The forked-mathlib check (project-specific instruction).**
   This project forks `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
   `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Inspected the mathlib copies of
   `DivisionPolynomial/{Basic,Degree}.lean` and `EllipticDivisibilitySequence.lean`: none contains
   `ringEval` / `polyEval` / `Universal`. The duplicated General*/PID* tracks do not introduce this
   lemma either. So it is **not** an "already in mathlib via the fork" case.

3. **The underlying primitive — present (pointwise form).**
   `Mathlib/RingTheory/AdjoinRoot.lean`:
   ```lean
   @[simp]
   theorem lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i a :=
     Ideal.Quotient.lift_mk _ _ _
   ```
   This is `ringEval_mk` (l.220) — already covered by the sibling report `ringEval_mk.md`
   (NO-composable-from-mathlib). `ringEval_comp_mk` is its `RingHom.ext`-bundled `comp` form.

4. **The companion `comp`-rule — NOT named in mathlib.**
   The `comp` family for `AdjoinRoot.lift` that mathlib *does* ship is for `of`, not `mk`:
   ```lean
   theorem lift_comp_of : (lift i a h).comp (of f) = i :=
     RingHom.ext fun _ => @lift_of _ _ _ _ _ _ _ h _
   ```
   There is **no** `AdjoinRoot.lift_comp_mk` in mathlib (confirmed by source grep of the `lift`
   family — `lift`, `lift_mk`, `lift_root`, `lift_of`, `lift_comp_of`, and the `liftHom_*`
   counterparts — and by the mathlib4 docs for `Mathlib.RingTheory.AdjoinRoot`). So the bundled
   `comp ∘ mk = eval₂` statement is not a single named mathlib lemma; it is obtained the same way
   `lift_comp_of` is obtained from `lift_of`: `RingHom.ext` over the pointwise rule. The project's
   proof `RingHom.ext (ringEval_mk eqn)` is *exactly* mathlib's `lift_comp_of` idiom.

5. **leansearch / loogle (mathlib index).** `?f.comp (AdjoinRoot.mk _) = _` /
   "AdjoinRoot lift comp mk eval₂" resolves to `lift_mk` and `lift_comp_of` (and `liftHom_*`), with
   **no** hit for a `mk`-composition lemma nor for the universal-curve wrapper — confirming both
   that the named `comp ∘ mk` lemma is absent and that the wrapper is project-only.

## 5. Generality analysis

`ringEval_comp_mk` is maximally *specific*: it fixes every parameter of `lift`/`mk` to the
universal-curve data (`i = eval₂RingHom W.specialize x`, `a = y`, `f = curve.polynomial`) and names
both sides with the project definitions `ringEval` / `polyEval`. The genuinely general content — the
pointwise `AdjoinRoot.lift_mk` over arbitrary `R, S, i, a, f, g` — is **already in mathlib** and is
strictly more general; the bundled `comp` form, if mathlib wanted it, would be a one-line
`RingHom.ext` corollary (the `lift_comp_of` analogue). The lemma cannot be generalised *in place*
without deleting its reason to exist (naming `ringEval ∘ mk = polyEval`). So neither YES-add-as-is
nor YES-but-generalise-first applies. (If anything were upstreamable here it would be a general
`AdjoinRoot.lift_comp_mk` lemma — a trivial `RingHom.ext (lift_mk …)` — but that is a separate
mathlib-API question, not a verdict on *this* curve-specific declaration.)

## 6. Composition check (can ≤3 mathlib calls give it?)

**Yes — at most two trivial calls.** After unfolding the local definitions `ringEval` and `polyEval`
(which a mathlib user would introduce themselves regardless, since they don't exist in mathlib), the
goal is `(AdjoinRoot.lift i a h).comp (AdjoinRoot.mk f) = eval₂RingHom i a` (as ring homs), closed by
`RingHom.ext fun p => AdjoinRoot.lift_mk i a h p` — i.e. `RingHom.ext` + the `@[simp]` `lift_mk`.
That is **2** mathlib calls (well within ≤3), and it is verbatim the recipe mathlib uses for
`lift_comp_of`. The source proof is literally `RingHom.ext (ringEval_mk eqn)`, where `ringEval_mk`
is itself the single call `AdjoinRoot.lift_mk _ p`. In a downstream proof one could alternatively
just `simp only [ringEval, polyEval]` and let `lift_mk` (simp) discharge the pointwise goal after
an `ext`/`RingHom.comp_apply` unfold. Composition count: **≤2** mathlib calls.

## 7. Five-bucket verdict

**NO-composable-from-mathlib.**

- It is **not** in mathlib (Methods 1–2: the entire `Universal` evaluation API is project-local), so
  it cannot be NO-mathlib-has-it as a *named* lemma — and, unlike its `algebraMap_ring_eq_comp`
  sibling, there is **no single named mathlib lemma** that *is* this statement (mathlib ships
  `lift_comp_of` for `of`, but no `lift_comp_mk`). That alone rules out NO-mathlib-has-it.
- The only mathlib-relevant content — "`AdjoinRoot.lift` composed with `mk` equals `eval₂`" — is
  recovered in **≤2** trivial mathlib calls (`RingHom.ext` over the `@[simp] AdjoinRoot.lift_mk`),
  exactly the `lift_comp_of` idiom. So it is the bundled per-definition `comp`-rule that any
  `AdjoinRoot.lift`-based definition gets essentially for free.
- Therefore the right bucket is **NO-composable-from-mathlib**. The lemma is correct and is
  appropriately kept as project API (it cleanly names `ringEval ∘ mk = polyEval` in the `comp`
  spelling that the `algebraMap`-factorization rewrites in `ringEval_comp_eq_specialize` and
  `ZSMul.lean` actually need, and it is reused byte-for-byte in HasseWeil), but it carries no
  mathlib-worthy mathematical content of its own beyond `lift_mk`.

### Required evidence (for NO-composable-from-mathlib)
- **Composing lemmas:** `AdjoinRoot.lift_mk` (`Mathlib/RingTheory/AdjoinRoot.lean`, `@[simp]`) +
  `RingHom.ext`. (Mathlib's directly analogous bundled lemma `AdjoinRoot.lift_comp_of` is proved by
  this same `RingHom.ext`-over-pointwise pattern; the `mk` counterpart is simply not separately
  named upstream.)
- **Composition recipe (≤3 calls):** unfold `ringEval`, `polyEval` (project defs) ⟹ goal is the
  `comp` form of the `lift_mk` instance ⟹ `exact RingHom.ext fun p => AdjoinRoot.lift_mk _ p`
  (equivalently the source's `RingHom.ext (ringEval_mk eqn)`). **≤2 calls.**
- **Why it stays local:** both sides name project-only definitions (`ringEval`, `polyEval`) that have
  no place in mathlib; the general pointwise fact they specialise (`lift_mk`) is already in mathlib,
  and the bundled `comp` form is a one-line corollary.

---

## Cross-references
- **Unbundled companion / sibling report:** `.../mathlibable/ringEval_mk.md` (the pointwise rule,
  `WeierstrassCurve.Universal.ringEval_mk`, l.220; verdict NO-composable-from-mathlib, 1 call). This
  `comp`-form report is the `RingHom.ext` bundling of that lemma.
- **Sibling report (consumer):** `.../mathlibable/algebraMap_ring_eq_comp.md` — the lemma whose
  rewrite produces the `AdjoinRoot.mk` spelling that `ringEval_comp_mk` then collapses (verdict
  NO-mathlib-has-it, since *it* equals the named `AdjoinRoot.algebraMap_eq'`).
- **Duplicate (byte-identical statement + proof):** HasseWeil
  `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:226` — a `main`-side dedup target, not a
  mathlib concern.
- **Inventory entry:** `.../overview/inventory/LutzNagell_Universal.md:438`.
- **Underlying mathlib API:** `AdjoinRoot.lift_mk` (`@[simp]`), `AdjoinRoot.lift_comp_of`
  (`Mathlib/RingTheory/AdjoinRoot.lean`).
