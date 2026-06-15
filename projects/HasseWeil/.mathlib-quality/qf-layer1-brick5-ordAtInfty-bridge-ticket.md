# QF Layer-1 Brick 5 — `ordAtInfty(α*x) < 0` from positive formal order of `α*t`

**Location**: `HasseWeil/FormalIsogenySeries.lean`.

**Brick (CLOSED modulo two residuals)**:
```lean
theorem ordAtInfty_pullback_x_gen_gen_neg_of_orderTop_pos
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0
```
Proof is `R5b ∘ R5a` (below); **no fresh `sorry`** in the brick. The two
residuals carry the sole `sorryAx`; axioms otherwise standard
(`propext, Classical.choice, Quot.sound`).

## Why the brick is the substantive Layer-1 bridge

The hypothesis lives in the **`localExpand` / `LaurentSeries.orderTop`** world
(formal `t`-adic expansion at `O`, `HasseWeil/LocalExpansion.lean`); the
conclusion lives in the **norm-based `ordAtInfty`** world
(`HasseWeil/Curves/Infinity.lean`, `HasseWeil/OrdAtInftyBridge.lean`). These
are two *independently constructed* discrete valuations on `K(E)`. An
exhaustive grep confirms **no shipped lemma connects them**: in
`AdditionPullback/SilvermanIV14.lean` the `ordAtInfty` lemmas and the
`orderTop`/`localExpand` lemmas appear only in *separate* statements, never
together; `GapQfKernel.lean` uses `ordAtInfty` independently.

## Residual R5a — chain-rule / substitution at `O`

```lean
theorem orderTop_localExpand_pullback_x_gen_neg_of_orderTop_localParam_pos
    (α : Isogeny W.toAffine W.toAffine)
    (h_orderTop : (0 : WithTop ℤ) < (localExpand W (α.pullback (localParam W))).orderTop) :
    (localExpand W (α.pullback (x_gen W))).orderTop < (0 : WithTop ℤ)
```

**Math**: at `O`, `x = t⁻²·u` with `u` a unit (`ord_O u = 0`). Shipped:
`localExpand_x_gen : localExpand W (x_gen W) = formalX W`,
`formalX = single(-2,1)·u⁻¹` (`LocalExpansion.formalX`),
`formalX_orderTop = -2`, `localExpand_localParam = single(1,1)`. Hence
`localExpand(α*x) = (localExpand(α*t))⁻²·v` with `orderTop v = 0`, giving
`orderTop(localExpand(α*x)) = -2·orderTop(localExpand(α*t)) < 0`.

**Gap**: this needs the **`localExpand ∘ α.pullback` substitution** (chain
rule) for an *abstract* `α`. Every shipped `localExpand_*_pullback_*` lemma
(`SilvermanIV14.lean`, e.g.
`orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam`) uses the
**concrete** Frobenius pullback `π* = (·)^q`, where `localExpand` commutes
through explicitly. No general substitution principle for abstract
`α.pullback` is shipped. (Note: the *algebraic* identity
`α*t = -α*x / α*y` in `K(E)` plus `localExpand` ring-hom gives only ONE
relation between `orderTop(localExpand(α*x))` and `orderTop(localExpand(α*y))`;
pinning `α*x < 0` needs the second (Weierstrass `y²=x³+…`) relation, i.e.
the full substitution.)

## Residual R5b — valuation comparison `orderTop∘localExpand → ordAtInfty` (`<0`)

```lean
theorem ordAtInfty_neg_of_orderTop_localExpand_neg
    {f : KE} (h : (localExpand W f).orderTop < (0 : WithTop ℤ)) :
    (W_smooth W).ordAtInfty f < 0
```

**Math**: both `f ↦ ordAtInfty f` (norm/`intDegree`-based) and
`f ↦ orderTop(localExpand f)` (`localExpand_injective` makes it a valuation)
are discrete valuations on `K(E)` at the place `O`, agreeing on the
generators (`ordAtInfty x_gen = -2 = orderTop formalX`; `y_gen ↦ -3`). They
coincide by **uniqueness of the place-at-`O` valuation** on the elliptic
curve. The `< 0` direction is all the brick needs.

**Gap**: this is exactly the "follow-up" identity flagged at
`Curves/Infinity.lean:114-123`. The full non-archimedean structure of
`ordAtInfty` (`ordAtInfty_add_ge_min`, `_mul`, `_inv`) is now shipped
(Infinity.lean) — the comment there is stale on that point — but the
*identification* with the formal-expansion valuation is not. Cleanest full
form to ship: `ordAtInfty f = orderTop(localExpand f)` for all `f`, which
gives R5b immediately.

## Discharge routes

* **R5b** (recommended first): prove `ordAtInfty f = orderTop(localExpand f)`.
  Both sides are valuations (multiplicative + non-archimedean, both shipped
  for `ordAtInfty`; for `orderTop∘localExpand` via `localExpand` ring-hom +
  `HahnSeries.orderTop_mul`/`min_orderTop_le_orderTop_add`). Reduce to a
  generating set `{x_gen, y_gen}` of `K(E)/F` where both agree
  (`= -2`, `= -3`). The reduction-to-generators step is the place-uniqueness
  content.
* **R5a**: ship the abstract `localExpand ∘ α.pullback` substitution
  (`localExpand(α*f) = MvPowerSeries.subst (localExpand(α*t)) (localExpand f)`
  shape), then specialise to `f = x_gen` via `localExpand_x_gen = formalX`.

## Consumers

Generalises the concrete pole witness `addPullback_x_ne_const`
(`AdditionPullback.lean:201`, currently itself a `sorry` for the
addition-pullback) to abstract `α` stated via the brick-4-shaped hypothesis
`0 < orderTop(localExpand(α*t))`.
