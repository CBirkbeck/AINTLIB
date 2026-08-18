# /mathlibable report — `WeierstrassCurve.Universal.polyEval_comp_eq_specialize`

## Verdict: NO-composable-from-mathlib

The lemma is the universal property "evaluation hom restricted to the constant subring = the coefficient map", applied to the two-layer ring `Poly = ℤ[A₁..A₆][X][Y]`. Mathlib supplies every piece: `Polynomial.algebraMap_eq` (`algebraMap R R[X] = C`) and `Polynomial.eval₂_C` (`eval₂RingHom f x ∘ C = f`, per layer), with the structurally-identical single-layer lemma `Polynomial.aevalTower_comp_algebraMap` already upstream. The proof is `ext <;> simp [polyEval]` — ≤3 mathlib calls reproduce it. Rides along as YES only if the whole `specialize`/universal-curve package is upstreamed, and that packaging call is owned by `specialize.md` (already BORDERLINE-needs-human).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task); decl read from source.
- decl:                     `WeierstrassCurve.Universal.polyEval_comp_eq_specialize` ✓ resolved at
                            `projects/NagellLutz/LutzNagell/Universal.lean:226`
- qualified name VERIFIED:  the prompt's guess `WeierstrassCurve.Universal.polyEval_comp_eq_specialize`
  is **correct**. The lemma sits inside `namespace WeierstrassCurve` (L69) → `namespace Universal`
  (re-entered L196, after the outer `Universal` block L75–177 closed), closed L241/L243. The
  governing variables are `variable {R} [CommRing R] (W : WeierstrassCurve R)` (L186) and
  `variable (x y : R)` (L198).
- kind:                     `lemma` (in `noncomputable section`)
- duplicate:                **byte-identical copy** at
  `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:229` (same Junyan-Xu universal-curve fork,
  "Ported from the LutzNagell project"). Independent AINTLIB dedup concern (see end).

### The declaration

```lean
lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]
```

Resolving the elaborated holes:
- `polyEval W x y : Poly →+* R` is `eval₂RingHom (eval₂RingHom W.specialize x) y` (L203), where
  `Poly := (MvPolynomial Coeff ℤ)[X][Y]` (L94).
- `algebraMap _ _` is `algebraMap (MvPolynomial Coeff ℤ) Poly`, i.e. the inclusion of the coefficient
  ring `S := MvPolynomial Coeff ℤ` into the bivariate polynomial ring `S[X][Y]`. By
  `Polynomial.algebraMap_eq` this is `C.comp C` (the `CC` map; cf. `Bivariate.lean:148`
  `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC`).
- `W.specialize : MvPolynomial Coeff ℤ →+* R` is `(MvPolynomial.aeval (Coeff.rec a₁ a₂ a₃ a₄ a₆)).toRingHom`
  (L190).

So the fully-explicit statement is, with `S := MvPolynomial Coeff ℤ`:

```
(eval₂RingHom (eval₂RingHom W.specialize x) y).comp (algebraMap S S[X][Y]) = W.specialize
```

**Mathematics.** This is the *universal property of the iterated polynomial ring*: the point-evaluation
ring hom `polyEval W x y : ℤ[A₁..A₆][X][Y] → R` (which sends `Aᵢ ↦ aᵢ`, `X ↦ x`, `Y ↦ y`), when
restricted to the *constant* (coefficient) subring `ℤ[A₁..A₆]`, recovers the coefficient map
`W.specialize`. Equivalently: "evaluating at a point does nothing to the constants." There is no
elliptic-curve content — only `eval₂(C a) = f a` applied through the two polynomial layers.

**Role in the project (not dead code).** Used immediately by `ringEval_comp_eq_specialize` (L229–230):

```lean
lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]
```

which in turn feeds `curveRing_map_ringEval` (L237, "every Weierstrass curve is recovered by
base-changing the universal curve along `ringEval`") and the `Field.two_ne_zero` / cusp machinery. It
is a genuine glue lemma in the `specialize`/`polyEval`/`ringEval` universal-curve API, not dead code.

---

### Phase 1 — Literature search

- No named mathematical theorem corresponds to this. It is the universal property of a polynomial
  ring (the constants of `R[X]` map by `f`), iterated once. Silverman (*AEC* III.4, Exer. 3.7), Lang,
  Washington and the Ayad/Cassels EDS sources use universal-coefficient / specialization arguments
  for division polynomials implicitly; none isolates "the restriction of a point-evaluation hom to the
  coefficient subring equals the coefficient map" as a stated result — it is bookkeeping that every
  source takes for granted.
- WebSearch (`mathlib eval₂RingHom comp algebraMap polynomial universal property eval₂_C RingHom`)
  surfaced only the relevant mathlib doc pages — `Polynomial.Bivariate`, `Polynomial.AlgebraMap`,
  `Polynomial.Eval.Defs` — and the nearby (different) lemma `Polynomial.eval_C_X_comp_eval₂_map_C_X`.
  No external mathematical reference treats this as a named fact.
- The only place the *surrounding* universal-curve idea is gestured at is mathlib's own
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:36–38, 71`, which describes
  "the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`" used to define `ωₙ`,
  and leaves `ωₙ` an explicit **TODO**. That morphism is `R[X,Y]`-valued; `polyEval` (and hence this
  lemma) is its further evaluation at `(x,y)`. So even the closest mathlib hint is about a *sibling*
  construction, not this compatibility lemma.

Conclusion: zero literature support for this as a standalone named result.

### Phase 2 — Mathlib search (five methods)

Target: is "`(eval₂RingHom (eval₂RingHom f x) y).comp (algebraMap S S[X][Y]) = f`" (a layered
`eval₂RingHom ∘ algebraMap` cancellation) already in mathlib, or a more general form of it?

1. **Loogle / leansearch (index) + local source.** The per-layer primitive is
   `Polynomial.eval₂_C : (C a).eval₂ f x = f a` (`Eval/Defs.lean:71`, `@[simp]`) — equivalently the
   ring-hom form `eval₂RingHom f x ∘ C = f`. The coefficient inclusion is
   `Polynomial.algebraMap_eq : algebraMap R R[X] = C` (`AlgebraMap.lean:90`) and
   `Polynomial.algebraMap_apply` (L69). These two, applied through both `X` and `Y` layers, *are* the
   content.
2. **Structurally-identical upstream lemma (single layer).**
   `Polynomial.aevalTower_comp_algebraMap` (`AlgebraMap.lean:568`):
   ```lean
   theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
     aevalTower_comp_C _ _
   ```
   This is **exactly this lemma's shape for one polynomial layer**: an evaluation hom composed with
   `algebraMap R R[X]` collapses to the base map. The MvPolynomial analogue
   `MvPolynomial.aevalTower_comp_algebraMap` (`MvPolynomial/Eval.lean:769`) likewise. The project lemma
   is the **two-layer `eval₂RingHom` iterate** of this same pattern; mathlib has the pattern, just not
   pre-packaged for `R[X][Y]` with `eval₂RingHom`.
3. **Exact two-layer `eval₂RingHom_comp_algebraMap`?** `grep` over `Mathlib/Algebra/Polynomial/` for
   `eval₂RingHom.*comp.*C` / `eval₂RingHom.*algebraMap` returns only the unrelated bivariate identity
   `eval_C_X_comp_eval₂_map_C_X` (`Bivariate.lean:198`). So the *verbatim* two-layer statement is
   **not** present — but it is one `RingHom.ext` + two `eval₂_C` away.
4. **Bivariate file.** `Mathlib/Algebra/Polynomial/Bivariate.lean` provides the closely-related
   `eval₂RingHom_eval₂RingHom` (L189, the characterisation of `polyEval`'s body — owned by
   `polyEval.md`) and `coe_algebraMap_eq_CC` (L148). It does **not** state the `∘ algebraMap = f`
   cancellation; that follows from the per-layer `eval₂_C`.
5. **Universal Weierstrass curve in mathlib?** `grep`/`find` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/**` for `Universal.curve` / `def specialize` / `polyEval`
   / `inductive Coeff` / `Coeff.rec`: **none** (the only `Universal`/`Coeff`-looking hits are the prose
   TODO in `DivisionPolynomial/Basic.lean` and the unrelated private `expCoeff` in `Degree.lean`). The
   entire `Universal` namespace — `specialize`, `polyEval`, and this lemma with them — is a project
   addition; the module docstring says it provides "lemmas missing from the released mathlib."

Result: the **general** machinery is upstream (`eval₂_C`, `algebraMap_eq`, and the single-layer
`aevalTower_comp_algebraMap`); only the project-specific two-layer bundling with `W.specialize` is
local, and it is a trivial composition of the above.

### Phase 3 — Generality analysis

- This lemma is **strictly less general** than the mathlib primitives it rests on. It hard-codes the
  coefficient map to `W.specialize` (`= aeval (Coeff.rec a₁..a₆)`), the source to `Universal.Poly`, and
  the layer count to two, whereas `eval₂_C`, `algebraMap_eq` and `aevalTower_comp_algebraMap` hold for
  an arbitrary `f : R →+* S` and arbitrary `R[X]`. The maximally-general per-layer statement is already
  upstream; this is a downstream instantiation.
- The only thing mathlib does *not* literally have is the **two-layer `eval₂RingHom` packaging**
  `(eval₂RingHom (eval₂RingHom f x) y).comp (algebraMap S S[X][Y]) = f`. If one wanted to upstream a
  general lemma, that bivariate cancellation would be the right (small) target to sit in
  `Mathlib/Algebra/Polynomial/Bivariate.lean` next to `eval₂RingHom_eval₂RingHom` — analogous to the
  single-layer `aevalTower_comp_algebraMap`. But that is a *general* polynomial lemma, not a
  Weierstrass-curve one; this declaration as written (with `W.specialize`) is not itself the
  generalise-first target — it is the instance.
- So there is no "weaken-the-hypotheses" path that keeps this declaration and lands somewhere new: the
  general per-layer forms exist, and the would-be two-layer generalisation is a different (curve-free)
  lemma.

### Phase 4 — Composition check (can ≤3 mathlib calls give it?)

**Yes**, and the source proof already exhibits it: `ext <;> simp [polyEval]`.

Unwound, the derivation from mathlib primitives is:
1. `RingHom.ext` / `Polynomial.ringHom_ext'` to reduce to the action on `C (C a)` (1 structural call).
2. `Polynomial.algebraMap_eq` rewrites `algebraMap S S[X][Y]` to `C.comp C` (≤1 call; it is a `@[simp]`
   `rfl`-level fact, fired automatically).
3. `Polynomial.eval₂_C` applied to the **outer** `Y`-layer: `eval₂RingHom (eval₂RingHom f x) y (C p) =
   eval₂RingHom f x p` (`@[simp]`).
4. `Polynomial.eval₂_C` applied to the **inner** `X`-layer: `eval₂RingHom f x (C a) = f a` (`@[simp]`).

`simp` discharges 2–4 in one pass because all three are simp lemmas; the only "real" call is the
`ext`. That is well within ≤3 mathlib calls. This is the canonical **NO-composable-from-mathlib**
signature: a named lemma whose entire content is two applications of an existing `@[simp]` lemma after
an `ext`.

### Phase 4b — The packaging tension (why not simply NO)

This lemma is **not standalone**: it lives inside the `Coeff` / `Universal.curve` / `specialize` /
`polyEval` / `ringEval` ensemble — a coherent universal-curve API that mathlib genuinely lacks and
*explicitly TODOs* (the `ωₙ` / universal-morphism note in `DivisionPolynomial/Basic.lean`). Its
purpose is to bridge `polyEval` and `specialize` so that `ringEval_comp_eq_specialize` (and thence
`curveRing_map_ringEval`, "every curve is a base change of the universal curve along `ringEval`") goes
through. It has a real consumer and no inline re-derivation bypassing it.

But within that package the **named anchor** carrying the semantic intent is `specialize` (the
`ℤ[A₁..A₆] → R` coefficient map), already assessed **BORDERLINE-needs-human** in `specialize.md`. This
lemma is the *mechanical* member: "the universal property says `polyEval` restricted to constants is
`specialize`." The package-vs-inline maintainer decision is owned by `specialize.md` (its Q1). For
**this** declaration assessed singly (the skill's mandate), the composition verdict dominates:
- if the whole package is upstreamed → this lemma rides along as a package member (added as-is
  alongside `polyEval`/`ringEval`, since it is already the right two-layer instance);
- if mathlib prefers the inline `eval₂RingHom`/`aeval` idiom (the Angdinata DivisionPolynomial track
  may build `ωₙ`'s morphism directly) → this lemma is dropped, its one use site closed by `simp` with
  `eval₂_C` (exactly as it is proved now), possibly via a general bivariate
  `eval₂RingHom_comp_algebraMap` added next to `eval₂RingHom_eval₂RingHom`.

Either branch keeps this declaration *non-additive as an independent lemma*: it is glue, gated on the
`specialize` packaging call, never a freestanding mathlib contribution on its own merits.

---

## Five-bucket decision

| bucket | fit |
|---|---|
| YES-add-as-is | No — body is two `@[simp]` `eval₂_C` applications after `ext`; not a freestanding result with its own merit. |
| YES-but-generalise-first | No — the *per-layer* general forms already exist upstream (`eval₂_C`, `algebraMap_eq`, single-layer `aevalTower_comp_algebraMap`). The one not-yet-present generalisation (a two-layer `eval₂RingHom_comp_algebraMap` in `Bivariate.lean`) is a *different, curve-free* lemma; this `W.specialize`-bundled declaration is its instance, not the thing to generalise. |
| NO-mathlib-has-it | Close but not exact — mathlib has the per-layer cancellation and the single-layer comp lemma, **not** this two-layer `eval₂RingHom`-with-`W.specialize` statement verbatim. The honest call is composable, not "already present." |
| **NO-composable-from-mathlib** | **Yes** — `ext` then `simp [eval₂_C, algebraMap_eq]` reproduces it exactly (≤3 mathlib calls); this is literally the source proof `ext <;> simp [polyEval]`. |
| BORDERLINE-needs-human | Only as a *package rider* — but the packaging question is already escalated under `specialize.md`; duplicating the BORDERLINE here would double-count one decision. |

**Verdict: NO-composable-from-mathlib.**

The exact composition: after `RingHom.ext` (`ext`), the goal on `C (C a)` collapses by two applications
of `Polynomial.eval₂_C` (outer `Y`-layer, then inner `X`-layer), with `Polynomial.algebraMap_eq`
rewriting `algebraMap S S[X][Y]` to `C ∘ C` — all three are `@[simp]`, so a single `simp` closes it.
Mathlib's structurally-identical single-layer lemma is `Polynomial.aevalTower_comp_algebraMap`
(`Mathlib/Algebra/Polynomial/AlgebraMap.lean:568`).

### Caveat / cross-reference
This lemma is a member of the un-upstreamed universal-curve package whose **anchor** `specialize` is
**BORDERLINE-needs-human** (`specialize.md`). If the maintainer upstreams that whole scaffold (`Coeff`,
`Universal.curve`, `specialize`/`map_specialize`, `polyEval`/`ringEval` + their compatibility lemmas,
closing the `ωₙ` TODO), this lemma ships **as-is** as part of it. Re-run this assessment if/when that
packaging decision (Q1 of `specialize.md`) is made; until then, the single-declaration verdict is
NO-composable-from-mathlib. Sibling reports reach the same conclusion for the mechanical members:
`polyEval.md` (NO-composable), `algebraMap_ring_eq_comp.md` (NO-mathlib-has-it via
`AdjoinRoot.algebraMap_eq'`).

### Independent AINTLIB cleanup note
This lemma is duplicated **verbatim** between `projects/NagellLutz/LutzNagell/Universal.lean:226` and
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:229`. Regardless of the mathlib decision, file a
dedup ticket to refactor the shared `Universal` scaffold into `Common/`.

## Next step
None blocking for this lemma as a single decl (NO-composable). The live human decision is the
package-level one tracked in `specialize.md` (Q1: upstream the whole universal-curve scaffold vs.
inline the `eval₂RingHom`/`aeval` idiom). Separately, dedup the NagellLutz ↔ HasseWeil verbatim copy.

---

### Evidence anchors
- Project lemma: `projects/NagellLutz/LutzNagell/Universal.lean:226`; use site L229–230
  (`ringEval_comp_eq_specialize`), thence L237 (`curveRing_map_ringEval`).
- `polyEval` def: L203 (`eval₂RingHom (eval₂RingHom W.specialize x) y`); `Poly` def: L94.
- `specialize` def: L190.
- Duplicate: `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:229`.
- mathlib per-layer: `Polynomial.eval₂_C`, `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean:71`.
- mathlib `algebraMap = C`: `Polynomial.algebraMap_eq`, `…/Mathlib/Algebra/Polynomial/AlgebraMap.lean:90`
  (`algebraMap_apply` L69); bivariate `coe_algebraMap_eq_CC`, `…/Bivariate.lean:148`.
- mathlib single-layer comp lemma (structural twin): `Polynomial.aevalTower_comp_algebraMap`,
  `…/AlgebraMap.lean:568`; MvPolynomial analogue `…/MvPolynomial/Eval.lean:769`.
- mathlib `polyEval`-body characterisation: `Polynomial.eval₂RingHom_eval₂RingHom`, `…/Bivariate.lean:189`.
- no universal-curve scaffolding in mathlib: `grep` over `Mathlib/AlgebraicGeometry/EllipticCurve/**`
  empty; only the prose TODO `DivisionPolynomial/Basic.lean:36–38, 71`.
