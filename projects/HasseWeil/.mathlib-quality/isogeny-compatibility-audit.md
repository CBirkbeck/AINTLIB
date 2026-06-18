# Isogeny compatibility audit

## Background

The `Isogeny` structure in this project (HasseWeil/Basic.lean:63) carries TWO
independent fields:

* `pullback : W₂.FunctionField →ₐ[F] W₁.FunctionField` — the pullback on
  rational functions.
* `toAddMonoidHom : W₁.Point →+ W₂.Point` — the rational-point map.

In algebraic geometry both come from a single morphism of varieties, so they
satisfy the **compatibility relation**

    f(toAddMonoidHom P) = (pullback f)(P)    for f ∈ K(W₂), P ∈ W₁.Point.

The structure encodes no such law, so a value can type-check while the two
fields represent inequivalent maps. Any theorem that ties data on the
pullback side (`degree`, `sepDegree`, `IsSeparable`, `FiniteDimensional`) to
data on the point side (`kernel`, `Nat.card kernel`, fiber cardinality) is
*structurally false* unless either (a) the `Isogeny` value used has a
pullback genuinely matching its toAddMonoidHom, or (b) the theorem carries
an explicit witness pinning the relevant cross-side equality.

`isogSmulSub α r s` (HasseWeil/Endomorphism.lean:105) is the canonical bad
case: pullback is `AlgHom.id` (degree = 1) but toAddMonoidHom is
`r • α - s • id` (a real point map). Worker B already moved the bound to
consume a non-negativity hypothesis on the QF in `ℤ`, sidestepping any
direct degree assertion about this isogeny (commits `de247d3`, `bfa2afc`).

This audit catalogs every `Isogeny` constructor in the codebase and triages
every theorem in HasseWeil/ that crosses the pullback/point boundary.

## Catalog of Isogeny constructors

### Genuine pullback (compatibility holds)

| Name | File:line | Pullback construction | toAddMonoidHom | Notes |
|------|-----------|------------------------|----------------|-------|
| `Isogeny.id` | HasseWeil/Basic.lean:150 | `AlgHom.id F W.FunctionField` | `AddMonoidHom.id _` | Both sides represent the identity. Degree = 1 matches. Compatible. |
| `mulByInt W n` | HasseWeil/Basic.lean:233 | `if n = 0 then AlgHom.id else mulByInt_pullbackAlgHom W n hn` (genuine, division-polynomial-based for n ≠ 0) | `zsmulAddGroupHom n` | Compatible **except at n = 0**: zero map on points but identity on functions. The `n = 0` placeholder is a known mismatch — pullback gives degree 1, point map is constant zero. Compatible for all `n ≠ 0`. |
| `frobeniusIsog W` | HasseWeil/Frobenius.lean:53 | `FiniteField.frobeniusAlgHom K W.toAffine.FunctionField` (genuine `f ↦ f^q`) | `AddMonoidHom.id _` | Compatible: over `F_q`, π acts as identity on rational points (since `a^q = a`). Degree = q matches. |
| `isogOneSub_negFrobenius W hq` | HasseWeil/AdditionPullback/Frobenius.lean:2702 | `addPullbackAlgHom_negFrobenius W hq` (genuine addition-formula pullback) | `AddMonoidHom.id _ - frobeniusIsog.toAddMonoidHom` | Compatible — this is the *intended* `1 − π` Isogeny, replacing the `oneSubFrobeniusIsog`/`isogOneSub` placeholder. |

### Placeholder pullback (compatibility-violating)

| Name | File:line | Pullback shape | toAddMonoidHom shape | Why violates |
|------|-----------|----------------|----------------------|--------------|
| `isogOneSub α` | HasseWeil/Endomorphism.lean:71 | `AlgHom.id F E.FunctionField` | `(AddMonoidHom.id _) - α.toAddMonoidHom` | Pullback is identity (degree = 1, separable) regardless of α. Point map is genuine. For α ≠ 0 the point map is non-trivial — pulling back any non-constant `f ∈ K(E)` should give something other than `f`, but the placeholder returns `f`. |
| `isogSmulSub α r s` | HasseWeil/Endomorphism.lean:105 | `AlgHom.id F E.FunctionField` | `r • α.toAddMonoidHom - s • (AddMonoidHom.id _)` | Same disease as `isogOneSub` but worse: at `(r,s) = (0,0)` the pullback is `id` (degree 1) but the point map is the zero map (kernel = whole group). Worker B's discriminant fix sidesteps this by consuming non-negativity in `ℤ`. |
| `oneSubFrobeniusIsog W` | HasseWeil/Frobenius.lean:153 (`= isogOneSub (frobeniusIsog W)`) | `AlgHom.id` (inherited from `isogOneSub`) | `id - id = 0` (since `frobeniusIsog.toAddMonoidHom = id` on F_q-points) | The TWO fields agree *coincidentally* (both 0-on-K(E)-action on the function field side, and 0 on F_q-points side: every fiber is the whole group). But mathematically `1 − π` should have **degree q + 1 − t = pointCount** as a separable isogeny over F_q, not 1. The point-side identity (kernel = whole group) is correct (V.1.1). The pullback side claims trivial. So `degree = pointCount` is false here, but `sepDegree = pointCount` is also false (sepDegree = 1 by placeholder pullback). |

### Composed (inherits from constituents)

| Name | File:line | Composed from | Status inherited |
|------|-----------|----------------|-------------------|
| `Isogeny.comp ψ φ` | HasseWeil/Basic.lean:99 | both | Pullback = `φ.pullback ∘ ψ.pullback`; point map = `ψ ∘ φ`. Compatible iff both inputs are compatible. |
| `Isogeny.zsmul m φ` | HasseWeil/Basic.lean:1166 | `mulByInt W m` and `φ` (via `Isogeny.comp`) | Compatibility inherited; safe when `m ≠ 0` and `φ` compatible. |
| `negFrobeniusIsog W` | HasseWeil/AdditionPullback/Frobenius.lean:1062 | `mulByInt W.toAffine (-1)` ∘ `frobeniusIsog W` | Both constituents compatible (mulByInt n with n=-1 ≠ 0; Frobenius). Compatible. |
| `verschiebungIsog_of_witness W h_subset` | HasseWeil/Verschiebung/IsDual.lean:59 | `verschiebungPullback_of_witness W h_subset` (genuine factoring through Frobenius range, taking the AlgHom.factor of `[q].pullback` through `π.pullback`); point map is `(mulByInt W q).toAddMonoidHom` | Witness-parametric. Pullback compatible as the IsDualOf certificate `verschiebung_comp_frobenius_eq_mulByInt_q` proves both Isogeny components compose to `mulByInt W q` — a structural compatibility check on the composition. The base `verschiebungIsog_of_witness` itself is compatible: pullback is the genuine V*, point map is [q]'s point map (which is the genuine action of V on F_q-points since π acts as identity there, so V acts as [q] on F_q-points). |

### Constructed inline (anonymous Isogeny.mk)

| Where | File:line | Pullback | toAddMonoidHom | Notes |
|-------|-----------|----------|----------------|-------|
| `Isogeny.mk` inside `verschiebung_comp_frobenius_eq_mulByInt_q` | HasseWeil/Verschiebung/IsDual.lean:85–90 | composed pullback (frobenius.pullback ∘ verschiebung.pullback) | composed hom (verschiebung.hom ∘ frobenius.hom) | Internal scratch: shows `Isogeny.comp` output equals `mulByInt W q`. Compatibility-correct because both sides are constructed the same way as `Isogeny.comp`. |
| Anonymous Isogeny in `EC/IsogenyFactor.lean:72` | EC/IsogenyFactor.lean:67-72 | `lamPb` (provided as input) | `lamHom` (provided as input) | The factor lemma takes both fields as inputs without a compatibility hypothesis. Safe at the *theorem* level only because the conclusion only mentions `Isogeny.comp` of the manufactured isogeny with `φ`, and consumers must supply both pieces consistently. |
| `Isogeny.mk` in `Hasse/HoleE.lean:48` and `AdditionPullback/SilvermanIV14.lean:2743` | various | (uses extant α, β isogenies as parameters) | parametric | Witness-parametric — caller responsible for passing compatible pullback and toAddMonoidHom. |

## Suspect theorems — implicit compatibility cross-binding

These theorems bind data on both sides of the pullback/toAddMonoidHom split
without an explicit witness pinning the cross-side relation. Each is
classified by mathematical-truth-status under the placeholder pullback for
the isogenies it touches.

### S1. `oneSubFrobeniusIsog_isSeparable` (Hasse/PointFix.lean:180)

```
(oneSubFrobeniusIsog W).IsSeparable
```

* What it asserts: the function-field extension `K(E) / (oneSubFrobeniusIsog
  W).pullback K(E)` is separable.
* What's true: under the placeholder, the pullback is `AlgHom.id`, so the
  extension is `K(E) / K(E)` — trivially separable. Provable.
* Mathematical truth status: **mathematically true under shipped pullback**
  by accident (placeholder pullback gives trivial extension which is
  separable). Mathematically `1 − π` IS separable (Silverman III.5.5), so
  the theorem name agrees with truth, but the proof is using the
  placeholder, not capturing the real content. Once the real pullback
  arrives, this theorem must be re-proved (and `oneSubFrobeniusIsog_isSeparable`
  at HasseWeil/AdditionPullback/Differential.lean already supplies the
  witness-parametric replacement for the *real* `isogOneSub_negFrobenius`).

### S2. `oneSubFrobeniusIsog_finiteDimensional` (Hasse/Unconditional.lean:52)

```
@FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
  _ _ (oneSubFrobeniusIsog W).toAlgebra.toModule
```

* Same status as S1: trivially provable from the placeholder pullback
  (self-extension). Mathematically true (Silverman III.4.6 — every isogeny
  has finite-dimensional pullback) but the placeholder proof is vacuous
  about the real content.

### S3. `pointCount_eq` (Frobenius.lean:300)

```
(pointCount W.toAffine : ℤ) =
  Fintype.card K + 1 - isogTrace (frobeniusIsog W) (oneSubFrobeniusIsog W)
```

* Documented `sorry` in the source. The proof would need:
  `pointCount = #ker(1 − π) = deg(1 − π) = (oneSubFrobeniusIsog W).degree`,
  and the last identity is equivalent to `(oneSubFrobeniusIsog W).degree =
  q + 1 − t` (V.1.3) — false under the placeholder (degree = 1).
* Mathematical truth status: **mathematically false under shipped pullback**.
  Witness-parametric replacement `pointCount_eq_of_witness`
  (Frobenius.lean:317) takes `(β.degree : ℤ) = pointCount` as a hypothesis;
  it's the safe drop-in.

### S4. Theorems chaining `card_kernel_eq_degree_of_separable_witness` to `oneSubFrobeniusIsog`

The function `Isogeny.card_kernel_eq_degree_of_separable_witness`
(EC/IsogenyKernel.lean:419) is correctly factored: it explicitly takes
`hsep`, `hfin`, and a fiber witness, and concludes `Nat.card φ.kernel =
φ.degree`. **The theorem itself is sound** — it does the cross-binding via
the *hypotheses*, not by appealing to internal compatibility.

But its callers must ensure `hsep`, `hfin`, and the fiber witness *all
refer to the same isogeny* (which Lean enforces type-theoretically) AND
that the *isogeny is genuine* — otherwise `φ.kernel` (point side) and
`φ.degree` (pullback side) disagree.

**Callers using `oneSubFrobeniusIsog` directly** (placeholder pullback):

* `hole_e_closer_via_workers` (Hasse/HoleE.lean) chain ultimately consumes
  `(oneSubFrobeniusIsog W).sepDegree = pointCount W.toAffine` as a
  hypothesis.
  - Under the placeholder: sepDegree = 1, pointCount = #E(F_q). The
    hypothesis is the false statement `1 = pointCount` — **unsatisfiable in
    general**, so the call site never fires. The theorem statement is
    sound (witness-parametric), but the shipped instances using
    `oneSubFrobeniusIsog` cannot be discharged unless pointCount = 1.
  - Mathematical truth status: **mathematically false under shipped pullback**,
    but the surrounding code knows it: e.g., Hasse/Unconditional.lean:97–98
    and Hasse/Unconditional.lean:298–299 explicitly comment that the
    fact is structurally false at (r,s) = (0,0).
  - Safe fix: switch downstream to `isogOneSub_negFrobenius W hq` (genuine).

### S5. `degree_quadratic_nonneg` (DegreeQuadraticForm.lean:151)

```
0 ≤ (α.degree : ℤ) * r ^ 2 - (isogTrace α one_sub_α) * r * s + s ^ 2
```

* The proof reads `← degree_quadratic α one_sub_α r s β hβ_hom` then
  `Int.natCast_nonneg`. It threads through `degree_quadratic` (a `sorry`),
  but the conclusion only depends on the algebraic non-negativity (every
  ℕ-cast is non-negative).
* Hypotheses include `hβ_hom : β.toAddMonoidHom = r • α.toAddMonoidHom - s
  • (AddMonoidHom.id _)` — a *point-side* identity. The conclusion uses
  `α.degree` and `β.degree` from the *pullback side*.
* Cross-binding: implicit. The theorem assumes the caller has a `β` whose
  *degree* satisfies the QF identity — which is what `degree_quadratic`
  would prove if it weren't `sorry`. The hypothesis `hβ_hom` is the wrong
  hypothesis to use here: it pins the point side, not the pullback side
  needed for the conclusion.
* Mathematical truth status: theorem statement is true (from
  `Int.natCast_nonneg`), but the proof script uses `degree_quadratic`
  whose truth depends on β's pullback being genuine.
* Safe fix: callers (e.g., `traceOfFrobenius_sq_le` HasseBound.lean:61)
  use this and pass a placeholder `β = isogSmulSub frob r s`. The theorem
  statement in HasseBound.lean would then *type-check* but its content
  becomes false at `(r,s) = (0,0)`. **However**, the *conclusion* (≤ 0 on
  the QF) is true at (0,0): `0 ≤ 0`. So the bound is correct *if and only
  if* the QF conclusion is what's used downstream — which it is, via
  `trace_sq_le_four_mul_deg`. The proof currently hits a sorry through
  `degree_quadratic`; the witness-parametric replacement
  `degree_quadratic_nonneg_of_witness` (DegreeQuadraticForm.lean:166) is
  the safe drop-in.

### S6. `traceOfFrobenius_sq_le` (HasseBound.lean:61)

```
(traceOfFrobenius W) ^ 2 ≤ 4 * (Fintype.card K : ℤ)
```

* Builds `β := isogSmulSub frob r s` (placeholder pullback) and calls
  `degree_quadratic_nonneg frob one_sub_frob r s β hβ_hom`.
* Cross-binding: feeds the placeholder `β` (degree = 1) into
  `degree_quadratic_nonneg`, which (via S5/`degree_quadratic`) would
  unsoundly assert `1 = q·r² − tr·rs + s²`.
* Mathematical truth status: **the conclusion is true** (Hasse's bound),
  **but the proof currently routes through `degree_quadratic` (a sorry that
  would be false-on-placeholder)** — so the proof is conditional on a sorry
  whose statement is false under the placeholder. Worker B already
  refactored the discriminant argument to consume only QF non-negativity
  in ℤ via `traceOfFrobenius_sq_le_of_qf_nonneg`
  (Hasse/BoundOfWitnesses.lean:251) and
  `hasse_bound_of_qf_nonneg_witnesses`. Replace this old form with the
  non-negativity form.

### S7. `pointCount_eq_sub_trace` (Frobenius.lean:332)

```
(pointCount W.toAffine : ℤ) = Fintype.card K + 1 - traceOfFrobenius W
```

* Trivial wrapper around S3 (`pointCount_eq`). Same status —
  **mathematically false under shipped placeholder for `oneSubFrobeniusIsog`**.
* Already replaced in practice by `pointCount_eq_of_hom_kernel_witness`
  (Hasse/PointFix.lean:192) which takes a witness `β` parametrically.

### S8. `Isogeny.zsmul_degree` (Basic.lean:1181) — used with placeholder?

```
(Isogeny.zsmul m φ).degree = (m^2).toNat * φ.degree    (for m ≠ 0)
```

* Defined via `Isogeny.zsmul m φ = (mulByInt W₁ m).comp φ` (or similar
  composition through `mulByInt` on point side and `mulByInt_pullbackAlgHom`
  on pullback side).
* Cross-binding: the theorem itself stays on the pullback side. **Sound (no
  compatibility needed)** — `mulByInt W m` for m ≠ 0 is genuine, so
  composition with a genuine `φ` is genuine. Risk: composing
  `Isogeny.zsmul m` with a placeholder `φ` (e.g. `isogOneSub α`) would
  inherit the placeholder's pullback degeneracy. No usage of that pattern
  found in the codebase.

### S9. `degree_quadratic_mulByInt` (Endomorphism.lean:227)

```
((isogSmulSub_mulByInt (W := W) m r s).degree : ℤ) =
  ((mulByInt W.toAffine m).degree : ℤ) * r ^ 2
  - isogTrace ... * r * s + s ^ 2
```

* `isogSmulSub_mulByInt m r s = mulByInt W (r * m - s)` — defined as a
  pure mulByInt isogeny, so pullback and point side are both
  consistent (genuine). Non-degenerate when `r * m - s ≠ 0`.
* Cross-binding: pullback-side `degree` and pullback-side
  `mulByInt_degree`. **Sound (no compatibility needed)** — genuine
  isogeny throughout.

### S10. `verschiebung_comp_frobenius_eq_mulByInt_q` (Verschiebung/IsDual.lean:70)

```
(verschiebungIsog_of_witness W h_subset).comp (frobeniusIsog W) =
  mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)
```

* Equality of full Isogeny structures — pulls in BOTH the pullback and the
  toAddMonoidHom. The proof shows pullback equality via Session 4 plus
  toAddMonoidHom equality structurally.
* Cross-binding: explicit at the *Isogeny* level. **Sound (compatibility
  witnessed)** — proof checks both fields.

### S11. `verschiebungIsog_of_witness_isDualOf_frobenius` (Verschiebung/IsDual.lean:158)

```
IsDualOf W.toAffine (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W)
```

* Same as S10 but as the `IsDualOf` predicate. **Sound (compatibility
  witnessed)**.

### S12. `card_oneSubFrobeniusIsog_kernel` (Hasse/PointFix.lean:74)

```
Nat.card (oneSubFrobeniusIsog W).kernel = pointCount W.toAffine
```

* Pure point-side statement (kernel-as-AddSubgroup, cardinality), proved
  from `oneSubFrobeniusIsog_kernel_eq_top` (point-side observation that
  `id − π` kills every F_q-point).
* Cross-binding: none. **Sound (no compatibility needed)** — single-side.
  Note: this *is* mathematically correct for `oneSubFrobeniusIsog` because
  the point-map is genuine (`id − π_point = 0` on F_q-points), even though
  the pullback is a placeholder.

### S13. Composed bound theorems consuming `(oneSubFrobeniusIsog W).sepDegree = pointCount`

* `hasse_bound_via_signed_QF` (Hasse/HoleE.lean:174)
* `hasse_bound_target_via_qth_root_witness` (Verschiebung/Cascade.lean:179)
* `hole_d_of_sepDegree_eq_pointCount` (Hasse/PointFix.lean:226)
* `hole_d_closer` (Hasse/Unconditional.lean:185)

All these take `(oneSubFrobeniusIsog W).sepDegree = pointCount W.toAffine`
as a hypothesis. Under the placeholder: sepDegree = 1, pointCount = real.
The hypothesis is therefore **unsatisfiable in general**.

* Mathematical truth status: theorem statements sound (consume hypothesis
  parametrically), but **no caller can discharge the hypothesis as long as
  `oneSubFrobeniusIsog` retains its placeholder pullback**.
* Status: **suspect (compatibility implicit)** — the statement is
  parametric on the (false-under-placeholder) hypothesis, so consumers can
  prove it conditionally but won't reach the bound.
* Safe fix: switch `β_pc = oneSubFrobeniusIsog W` to `β_pc =
  isogOneSub_negFrobenius W hq` (genuine pullback). The corresponding
  theorems with `isogOneSub_negFrobenius` already exist in
  `HasseWeil/Verschiebung/Cascade.lean:235–273` (the
  `hasse_bound_witness_parametric_assembled` family).

### S14. `Isogeny.kernel_eq_top_of_hom_eq_id_sub_frobenius` (Hasse/PointFix.lean:88)

```
β.toAddMonoidHom = id - π.toAddMonoidHom → β.kernel = ⊤
```

* Pure point-side. **Sound (no compatibility needed)**.

### S15. `omegaPullbackCoeff_oneSubFrobeniusIsog` (Hasse/PointFix.lean:152)

```
omegaPullbackCoeff W (oneSubFrobeniusIsog W) = 1
```

* Pure pullback-side computation. Direct from
  `omegaPullbackCoeff_of_pullback_eq_id` (since `oneSubFrobeniusIsog` has
  pullback = `AlgHom.id`).
* Mathematical truth status: matches the truth value for the *real* `1 − π`
  (Silverman III.5.5: `n = -1`, `m = 1` → ω-coeff = m = 1). So the
  theorem ships the correct value by accident. **Mathematically true under
  shipped pullback** (and also under the genuine pullback).

### S16. `not_isSeparable_frobenius_of_witness` (BridgeFrobenius.lean:127)

```
(h_sep_iff : (frobeniusIsog W).IsSeparable ↔ ω-coeff ≠ 0) →
  ¬ (frobeniusIsog W).IsSeparable
```

* Pure pullback-side. **Sound (no compatibility needed)** — Frobenius is
  genuine.

### S17. `degree_eq_pointCount_of_witness` (Hasse/PointFix.lean:108)

```
(h_hom : β.toAddMonoidHom = id - π.toAddMonoidHom) →
  (h_ker_deg : Nat.card β.kernel = β.degree) →
  (β.degree : ℤ) = pointCount W.toAffine
```

* Cross-binding: takes `h_hom` (point side: hom equality with `id − π`)
  and `h_ker_deg` (cross-side: kernel cardinality matches degree —
  exactly the compatibility claim for separable isogenies). The
  conclusion uses `β.degree` (pullback side) and `pointCount` (point
  side).
* The cross-binding is **explicit via h_ker_deg**: the caller is required
  to supply the kernel-degree match. **Sound (compatibility witnessed)**.

### S18. `pointCount_eq_of_hom_kernel_witness` (Hasse/PointFix.lean:192)

* Composed witness form of `pointCount_eq_of_witness` and
  `degree_eq_pointCount_of_witness`. **Sound (compatibility witnessed)** —
  takes both `h_hom` and `h_ker_deg`.

## False under placeholder (priority fix list)

These are theorem names that, when applied to the placeholder isogenies
(`isogOneSub`, `isogSmulSub`, `oneSubFrobeniusIsog`), state mathematical
falsehoods. They are NOT currently proved unconditionally — they're either
sorries, witness-parametric on hypotheses that cannot be discharged under
the placeholder, or only used inside a chain that's already aware of the
issue.

### F1. `pointCount_eq` (Frobenius.lean:300) — SORRY

```
pointCount = q + 1 - isogTrace π (isogOneSub π)   -- with placeholder
           = q + 1 - (1 + q - 1)                   -- since (isogOneSub π).degree = 1
           = 1
```

* False whenever `pointCount ≠ 1`. The `sorry` is structurally
  unprovable under the placeholder. **Already documented inline at
  Frobenius.lean:271–298** as the blocking factor.
* Replacement: `pointCount_eq_of_witness` (parametric on a witness β with
  `β.degree = pointCount`, supplied by the genuine `1 − π`).

### F2. `degree_quadratic` (DegreeQuadraticForm.lean:139) — SORRY

```
(β.degree : ℤ) = α.degree · r² - tr · r · s + s²
```

with `β` a placeholder `isogSmulSub α r s` (degree = 1) at (r,s) = (0,0)
gives `1 = 0` — false.

* The `sorry` is structurally unprovable for placeholder β. The
  surrounding code knows it: `Hasse/Unconditional.lean:104-107` and
  `BoundOfWitnesses.lean:241-246` explicitly say the equality form is false
  for the placeholder.
* Replacement: `traceOfFrobenius_sq_le_of_qf_nonneg` consumes only
  non-negativity in ℤ, which is provable (and trivially true at (0,0)).

### F3. `traceOfFrobenius_sq_le` (HasseBound.lean:61)

* Currently routes through `degree_quadratic_nonneg` →
  `degree_quadratic` (the false-under-placeholder sorry). The conclusion
  is mathematically true, but the proof depends on a sorry that is
  structurally false. **Replacement already exists**:
  `hasse_bound_of_qf_nonneg_witnesses` chain. Should retire this proof.

### F4. Hypotheses requiring `(oneSubFrobeniusIsog W).sepDegree = pointCount`

(See S13.) Any consumer of the form `... → (oneSubFrobeniusIsog
W).sepDegree = pointCount W.toAffine → ...` cannot have its hypothesis
discharged under the placeholder. Theorems whose only use is to consume
this:

* `hasse_bound_via_signed_QF` (Hasse/HoleE.lean:174)
* `hasse_bound_sq_via_signed_QF` (Hasse/HoleE.lean:195)
* `hasse_bound_target_via_qth_root_witness` (Verschiebung/Cascade.lean:179)
* `hasse_bound_sq_target_via_qth_root_witness` (Verschiebung/Cascade.lean:276)
* `hole_d_closer` (Hasse/Unconditional.lean:185)
* `hole_d_of_sepDegree_eq_pointCount` (Hasse/PointFix.lean:226)
* `hole_d_of_hom_and_sepDegree` (Hasse/PointFix.lean:249) — generalized,
  parametric on β

These are all parametric (sound at the theorem level) but un-discharge-able
on the placeholder. The whole `hasse_bound_target` (Hasse/Unconditional.lean:71)
hits this wall — explicitly documented at Hasse/Unconditional.lean:265–275.
Migration target: `hasse_bound_target_via_negFrobenius`
(Hasse/Unconditional.lean:316), built on the genuine
`isogOneSub_negFrobenius`.

### F5. `oneSubFrobeniusIsog_sepDegree_eq_pointCount_of_degree` (Hasse/Unconditional.lean:200)

```
(oneSubFrobeniusIsog W).degree = pointCount → sepDegree = pointCount
```

* The hypothesis `degree = pointCount` is false under placeholder
  (LHS = 1). The theorem itself is parametric, but
  cannot fire under the shipped `oneSubFrobeniusIsog`. Migration target:
  `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses`
  (Hasse/HoleE.lean:570) using genuine pullback.

### F6. Identity-on-points-but-not-on-functions split in `mulByInt W 0`

```
(mulByInt W 0).pullback = AlgHom.id      -- placeholder
(mulByInt W 0).toAddMonoidHom = zsmulAddGroupHom 0 = 0    -- genuine
```

* Compatibility violation similar to `isogSmulSub`. Currently no theorem
  hits this — `mulByInt_degree` (Basic.lean) explicitly carries `n ≠ 0` as
  a hypothesis. So no false statement is shipped.
* Status: **mathematically incoherent at n = 0**, but the API forecloses
  on it. Worth annotating in the source if a future caller forgets the
  guard. (Currently HasseWeil/Basic.lean:233 documents this.)

## Sound — explicitly witnessed (reference)

For the avoidance of doubt, the following theorems carry compatibility
hypotheses cleanly and are robust regardless of placeholder use:

* `Isogeny.card_kernel_eq_degree_of_separable_witness`
  (EC/IsogenyKernel.lean:419) — takes `hsep`, `hfin`, fiber witness.
* `Isogeny.fiber_card_eq_sepDegree_of_witness`
  (EC/IsogenyKernel.lean:369) — takes a single fiber-card witness.
* `pointCount_eq_of_witness` (Frobenius.lean:317) — takes degree witness.
* `pointCount_eq_of_hom_kernel_witness` (Hasse/PointFix.lean:192) — takes
  hom + kernel-degree witnesses.
* `degree_quadratic_nonneg_of_witness` (DegreeQuadraticForm.lean:166) —
  takes degree-equality witness.
* `degree_quadratic_closed` (DegreeQuadraticForm.lean:409) — takes a full
  six-witness bundle including the degree-bridge for the QF.
* `isogSmulSub_degree_quadratic_closed` (DegreeQuadraticForm.lean:451) —
  same but specialized to `β = isogSmulSub α r s`.
* `hole_e_closer_via_frobenius_dual_witness` (Hasse/HoleE.lean — section
  for "frobenius-dual witness" form) — takes `IsDualOf` certificate plus
  ancillary degree-bridge witnesses.
* `hasse_bound_of_qf_nonneg_witnesses` (Hasse/BoundOfWitnesses.lean:262)
  and the entire `_qf_nonneg` family — take only non-negativity in ℤ.
* `verschiebung_comp_frobenius_eq_mulByInt_q` (Verschiebung/IsDual.lean:70)
  and `verschiebungIsog_of_witness_isDualOf_frobenius`
  (Verschiebung/IsDual.lean:158) — Isogeny-level equalities, both fields
  checked.
* `hasse_bound_witness_parametric_assembled`
  (Verschiebung/Cascade.lean:235) and the `_q_two/three/five/seven` family
  — take the genuine `isogOneSub_negFrobenius W hq`.
* `hasse_bound_target_via_negFrobenius` (Hasse/Unconditional.lean:316) —
  built on `isogOneSub_negFrobenius`.

These are the safe consumer surfaces.

## Recommendations

1. **Retire the `pointCount_eq`, `degree_quadratic`, `traceOfFrobenius_sq_le`,
   `hasse_bound`, `hasse_bound_sq` chain in `HasseBound.lean` and
   `Frobenius.lean:300` in favor of the qf_nonneg/witness-parametric
   chain.** The currently-shipped `traceOfFrobenius_sq_le` proof routes
   through `degree_quadratic` (a sorry that is structurally false on the
   placeholder); this is the live source of unsoundness if any sorries get
   accidentally accepted. The `_qf_nonneg`-form chain
   (`hasse_bound_of_qf_nonneg_witnesses` and friends in
   `Hasse/BoundOfWitnesses.lean`) is sound. Migrate `hasse_bound`,
   `hasse_bound_sq`, and `hasse_bound_target` to the negFrobenius-driven
   target (`hasse_bound_target_via_negFrobenius`).

2. **Mark `isogOneSub`, `isogSmulSub`, and `oneSubFrobeniusIsog` as
   deprecated / scheduled for removal once `isogOneSub_negFrobenius` is
   ubiquitous downstream.** Their docstrings already say "placeholder"
   (Endomorphism.lean:56–69 and 96–104), but the project still has many
   consumers (~15 theorems explicitly named after them in
   `Hasse/Unconditional.lean`, `Hasse/PointFix.lean`, `Hasse/HoleE.lean`,
   `Verschiebung/Cascade.lean`, `Hasse/CascadeValidation.lean`).
   A grep of
   `oneSubFrobeniusIsog\|isogOneSub\b\|isogSmulSub\b` (excluding
   `_negFrobenius` and `_mulByInt` variants) gives the deprecation work
   list.

3. **The placeholders' problematic theorems are well-isolated.** Apart
   from the `traceOfFrobenius_sq_le` sorry-chain (a real concern, since the
   sorry would be structurally false), every other suspect theorem either
   (a) takes its cross-binding as a hypothesis that cannot be discharged
   on the placeholder, so it never fires, or (b) is mathematically true
   under the trivial extension by accident (the separability /
   finite-dimensional theorems for `oneSubFrobeniusIsog`). Most damage
   would come from a future contributor wiring `traceOfFrobenius_sq_le`'s
   sorry to a different proof attempt — flagging this with a comment at
   `HasseBound.lean:61` (or removing it) closes that risk.

4. **The `mulByInt W 0` placeholder (zero point map but identity pullback)
   is a structurally similar mismatch but currently unused** — every
   degree theorem takes `n ≠ 0` as a guard. Left as-is is fine; consider
   moving `mulByInt` definition to a `dite` or partial form returning a
   subtype `{n : ℤ // n ≠ 0}` if cleanup is desired.

5. **`Isogeny.id` and `Isogeny.comp` are clean** — their pullback and
   point-map agree. Ditto `frobeniusIsog`, `negFrobeniusIsog`,
   `verschiebungIsog_of_witness`, `isogOneSub_negFrobenius`,
   `mulByInt W n` (n ≠ 0). All the genuine constructors are
   compatibility-respecting.
