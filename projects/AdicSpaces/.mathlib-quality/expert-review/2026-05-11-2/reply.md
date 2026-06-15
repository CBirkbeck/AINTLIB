# Reviewer reply — ChatGPT Pro, 2026-05-11 (second session)

## Assessment

The main conclusion is: **do not try to close Wedhorn Prop. 8.15 by proving that an arbitrary completed rational restriction map is an `IsLocalization.Away` map. In that generality, that target is false.**

The phrase "localization" is doing two different jobs here:

1. **Algebraic localization** in Mathlib's `IsLocalization.Away` sense: every element is cleared by a finite power of one element.
2. **Completed/rational/topological localization** in Huber–Wedhorn's sense: adjoin bounded fractions, then complete.

The presheaf value of a rational subset is generally the second object, not the first. A completed rational localization contains infinite convergent expressions that cannot be cleared by multiplying by a finite power of the denominator. So the condition

```
∀ z ∈ O(D), ∃ n a, z * u^n = σ(a)
```

is not true for general rational restriction maps.

Candidate **P** and **B** are not the right critical-path Mathlib targets. Pettis/Open Mapping does not address the finite-denominator algebraic localization condition, and the nonarchimedean Banach route is too specialised to valued-field affinoids. Candidate **H** is the mathematically native Huber/Wedhorn formulation, but it is large infrastructure. Candidate **S**, in a corrected form, is the best focused Mathlib contribution — but not as the theorem stated in the brief.

The correct Mathlib-style theorem is not

```
completion of R[1/x] ≅ (completion of R)[1/x]
```

in full generality. That statement is false. The correct object is the **completed localization**

```
lim_n (R / I^n)[1/x]
```

or equivalently the `I·R[1/x]`-adic completion of `R[1/x]`. This is the formal-scheme/rational-localization object, not ordinary algebraic localization of `R̂`.

Mathlib's public docs already expose noetherian adic-completion infrastructure such as `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` and `AdicCompletion.flat_of_isNoetherian`, which fits a focused adic-completion contribution better than a new open-mapping theory. The docs also present `IsLocalization` explicitly as an algebraic predicate on `algebraMap`, so it should not be used for completed rational localization unless the finite-denominator property is actually true.

## Mathematical idea

A simple example shows why the current `IsLocalization.Away` target is too strong.

Take a nonarchimedean affinoid ring such as

```
A = Q_p⟨X⟩
```

and consider the completed rational localization where `X` is inverted in the affinoid sense:

```
A⟨T⟩ / (XT - 1).
```

This ring contains convergent infinite negative-power series such as

```
∑_{n ≥ 0} p^n X^{-n}.
```

No finite power of `X` clears the denominator tail into `A`; multiplying by `X^N` only removes finitely many negative powers. Thus the completed rational localization is not algebraically `A[1/X]` in the `IsLocalization.Away` sense.

The same phenomenon appears in ordinary adic completion. For example, with

```
R = Z, I = (p), x = p,
```

the `I·R[1/p]`-adic completion of `R[1/p]` is zero, because `I` becomes the unit ideal after inverting `p`. But

```
R̂_I[1/p] = Z_p[1/p] = Q_p.
```

So the naive "completion commutes with localization as `R̂[1/x]`" statement is false. What is true is the completed-localization identity

```
(R[1/x])^∧_{I R[1/x]} ≅ lim_n (R/I^n)[1/x].
```

For noetherian rings, the surrounding exactness/flatness/completion facts are standard; Stacks' noetherian completion section states exactness of completion on finite modules, flatness of `R → R̂`, faithful flatness when `I` lies in the Jacobson radical, and noetherianity of the completion.

So the right mathematical correction is:

* Use `IsLocalization.Away` only for genuinely algebraic away localizations where finite denominator clearing is true.
* Use **completed localization / rational localization** for presheaf values.
* For Corollary 8.32, require **flatness** of restriction maps, not `IsLocalization.Away`.

## Lean-facing next steps

First, audit the exact consumer of the current sorry.

If the theorem currently called something like

```
restrictionMap_isLocalization
```

is used for arbitrary rational restrictions, replace that interface. It is too strong.

The Corollary 8.32 abstract theorem should be refactored from:

```
∀ i, IsLocalization.Away (κ_D0 s_i) (presheafValue D_i)
```

to something like:

```
∀ i, Module.Flat (presheafValue D₀) (presheafValue D_i)
```

plus the already intended spectrum/Spa-cover surjectivity hypothesis. Then flatness is supplied by Wedhorn Prop. 8.30 / Lemma 8.31 through the Tate-algebra quotient identifications, not by ordinary localization.

For Mathlib, the useful focused contribution is a new file or section around:

```
Mathlib/RingTheory/AdicCompletion/Localization
```

with a theorem in the following spirit:

```
-- schematic, not exact Lean
AdicCompletion.completedLocalization :
  AdicCompletion (I.map (algebraMap R (Localization.Away x)))
      (Localization.Away x)
    ≃+*
  inverseLimit_n (Localization.Away (image of x in R ⧸ I^n))
```

or a finite-level version first:

```
-- schematic
(Localization.Away x) ⧸ (I.map ...)^n
  ≃+*
Localization.Away (image x) (R ⧸ I^n)
```

Then build the completion-level equivalence from the inverse-limit/completion API.

A separate corollary may say that this completed localization agrees with ordinary localization of the completion under extra hypotheses, for example when `x` is already a unit in the completed ring for the relevant reason. But that should be a corollary with explicit assumptions, not the main theorem.

Do **not** spend critical-path effort on:

```
Pettis open mapping for Polish groups
nonarchimedean Banach open mapping
ordinary IsLocalization.Away for general rational presheaf values
```

Those are either not directly applicable or too narrow for Wedhorn's Huber-ring setting.

If the project wants a Huber-native theorem instead of the Mathlib adic-completion theorem, target the universal property of completed rational localization:

```
O(R(T/s)) is the universal complete topological A-algebra
where s is invertible and each t/s is power-bounded.
```

That is mathematically correct, but it is a larger project-local infrastructure package.

## Risks or missing facts

The biggest risk is that the current critical-path sorry is trying to prove a false algebraic statement. If the target is truly condition (ii),

```
∀ z ∈ O(D), ∃ n a, z * u^n = σ(a),
```

for arbitrary completed rational restrictions, it should be abandoned or restricted to a genuine ordinary-away subcase.

The second risk is misquoting Candidate S. Completion-localization commutation is true in the **completed localization** sense, but false as a blanket statement

```
(R[1/x])^∧ ≅ R̂[1/x].
```

The third risk is using `IsLocalization.flat` as a shortcut for flatness of rational restrictions. Rational restriction flatness should come from Wedhorn Lemma 8.31 / Prop. 8.30: identify basic rational localizations with Tate-algebra quotients and transfer flatness.

The fourth risk is final theorem drift. The final Tate acyclicity theorem should not gain extra hypotheses just to make an over-strong `IsLocalization.Away` statement true. The right fix is to weaken the intermediate theorem to the flatness/topological-rational-localization statement Wedhorn actually uses.

## Manager message to worker

The current "Prop. 8.15 as `IsLocalization.Away`" target is likely misframed.

For completed rational localizations, `IsLocalization.Away` is generally false: completed rational sections contain infinite convergent denominator tails that no finite power clears. So do not try to close the critical sorry by proving ordinary algebraic localization of presheaf values.

Refactor Cor. 8.32 to consume **flatness of each restriction map**, not `IsLocalization.Away`. Discharge flatness via Wedhorn Prop. 8.30 / Lemma 8.31 and the Tate-algebra quotient identifications.

If we want a Mathlib contribution, build the corrected adic-completion localization theorem:

```
completion of R[1/x] with respect to I·R[1/x]
  ≅ lim_n (R/I^n)[1/x]
```

or its finite-level quotient lemmas. Put this near `AdicCompletion`, using existing `AdicCompletion` and `IsLocalization` APIs. Do not state the false general theorem `(R[1/x])^∧ ≅ R̂[1/x]`, and do not expect this theorem to imply `IsLocalization.Away` for general rational presheaf values.

Critical-path action: replace the `restrictionMap_isLocalization` dependency with `restrictionMap_flat` / Prop. 8.30. Then use the existing product-level Cor. 8.32 route: componentwise flatness plus spectrum/Spa cover surjectivity gives faithful flatness of the product restriction.

## References cited

- Mathlib AdicCompletion docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.html
- Stacks Project Tag 0BNH (Section 10.97, Completion for Noetherian rings): https://stacks.math.columbia.edu/tag/0BNH
