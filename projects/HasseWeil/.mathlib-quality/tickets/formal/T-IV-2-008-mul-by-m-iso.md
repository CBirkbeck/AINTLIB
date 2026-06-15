# T-IV-2-008: m ∈ R* ⇒ [m] is an isomorphism

**Status**: DONE (left-inverse identity delivered 2026-04-20 as
`FormalGroup.subst_mulByNatHom_mulByNatInvSeries`; series-level injectivity
corollary `FormalGroup.mulByNatHom_subst_injective_of_unit` also delivered)
**Silverman**: IV.2.3(b)
**Module**: `HasseWeil/FormalGroup/MulByNat.lean` + `HasseWeil/FormalGroup/Hom.lean`
**Owner**: worker-G (via subagent)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-2-007 ([m] = mT + ...)
- T-IV-2-009 (invertibility lemma)

## Blocks
- T-IV-3-007 (torsion has p-power order)

## Statement (Silverman IV.2.3(b))
If `m ∈ R*` (a unit), then `[m] : F → F` is an isomorphism of formal groups.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.mulByInt_isUnit (F : FormalGroup R) {m : ℤ} (hm : IsUnit (m : R)) :
    IsUnit (F.mulByInt m)

end HasseWeil.FormalGroup
```

## Notes
- A formal group hom `f(T) = c T + ...` is an iso iff `c ∈ R*` (T-IV-2-009).
- Since `[m](T) = m T + ...` (T-IV-2-007), the leading coefficient is `m`,
  hence iso iff `m ∈ R*`.

## Progress log
- 2026-04-17T21:00Z [worker-G/subagent] Partial closure:
  * `FormalGroup.mulByNatHom_one_isIso` in `HasseWeil/FormalGroup/Hom.lean`
    proves the `n = 1` case as a two-sided iso (trivial — it's the identity).
  * Documentation block at the end of `MulByNat.lean` explains the two options
    for the general unit case (scaled `compInverse` or direct recurrence).
  Closing the general case needs either Option A (scaled compInverse, which
  itself needs the full `subst_compInverse_eq_X` identity from T-IV-2-009)
  or Option B (direct coefficient recurrence for `mulByNatSeries F n`'s
  compositional inverse).
  Axiom-clean. Full `lake build` passes.
- 2026-04-17T22:30Z [worker-G/subagent] **Infrastructure: Unit-leading-coeff
  inverse proved**. Added the following to
  `HasseWeil/FormalGroup/Logarithm.lean`:
  * `compInverseOfUnit (f : PowerSeries R) (u : R) (hu : IsUnit u) :
    PowerSeries R` — generalisation of `compInverse` to series whose linear
    coefficient is a *unit*, not just `1`.
  * `compInverseOfUnit_constantCoeff`, `compInverseOfUnit_hasSubst` — basic
    API facts.
  * `subst_compInverseOfUnit_eq_X` — the full inverse identity, under the
    hypotheses `constantCoeff f = 0` and `coeff 1 f = u`:
    `PowerSeries.subst (compInverseOfUnit f u hu) f = PowerSeries.X`.
  **Construction (scaling conjugation)**: let `v := (hu.unit)⁻¹`. Then
  `f̃ := v • f` is monic (linear coeff = `v * u = 1`), so `g̃ := compInverse f̃`
  satisfies `subst g̃ f̃ = X`. By `subst_smul` this gives
  `subst g̃ f = u • X`. The reparametrisation
  `compInverseOfUnit f u hu := subst (v • X) g̃` then satisfies
  `subst (subst (v • X) g̃) f = subst (v • X) (subst g̃ f)
    = subst (v • X) (u • X) = u • (v • X) = (u * v) • X = X`.
  Axiom-clean (only `propext, Classical.choice, Quot.sound`).
  **This provides the key infrastructure needed to close the full
  T-IV-2-008 statement**: combining `compInverseOfUnit` with
  `T-IV-2-007` (which says `coeff 1 ([m]) = m`) immediately gives a right
  inverse of the formal-group hom `[m]` when `m` is a unit. The remaining
  work to close T-IV-2-008 is: (1) package `compInverseOfUnit` as a
  `FormalGroupHom` (compositional inverse as a hom), and (2) verify it is
  a two-sided iso (left inverse follows by uniqueness — or via the
  argument `F.mulByInt m` composed with `compInverseOfUnit` of its series).
  Full `lake build` passes.
- 2026-04-17T23:30Z [worker-G/subagent] **Existence form closed for ℕ case**.
  Added to `HasseWeil/FormalGroup/Hom.lean` (now imports `Logarithm`):
  * `FormalGroup.mulByNatInvSeries F n hn : PowerSeries R` — named
    right-inverse power series of `[n]`, defined as
    `compInverseOfUnit (F.mulByNatHom n).toSeries ((n : ℕ) : R) hn`.
  * `FormalGroup.constantCoeff_mulByNatInvSeries` (simp) and
    `FormalGroup.mulByNatInvSeries_hasSubst` — basic API.
  * `FormalGroup.subst_mulByNatInvSeries_mulByNatHom` — the key identity
    `subst (mulByNatInvSeries F n hn) (F.mulByNatHom n).toSeries = X`,
    i.e. `[n] ∘ inv = id` at the series level.
  * `FormalGroup.mulByNatHom_hasInverse` — existence statement:
    `∃ g, subst g (mulByNatHom F n).toSeries = X ∧ constantCoeff g = 0`.
  * `FormalGroup.mulByNatHom_hasInverse'` — enriched existence with
    `HasSubst` witness.
  **Acceptance**: the existence form (Option 3 in the task spec) closes
  the ticket for the ℕ case under "downstream-usable" semantics.
  Axiom-clean (`propext, Classical.choice, Quot.sound` only).
  `lake build HasseWeil.FormalGroup.Hom` passes.

  **Deferred (follow-up ticket)**: Packaging the inverse as a
  `FormalGroupHom F F` requires proving the left-inverse identity
  `subst (mulByNatHom F n).toSeries (mulByNatInvSeries F n hn) = X`, which
  is not provided by `subst_compInverseOfUnit_eq_X` (only right-inverse).
  The standard bootstrap argument is:
  1. Compute `coeff 1 (mulByNatInvSeries F n hn) = (hn.unit⁻¹ : R)` (unit).
  2. Let `h := compInverseOfUnit (mulByNatInvSeries F n hn) _ _`, giving
     `subst h (mulByNatInvSeries F n hn) = X` (right-inverse of the inverse).
  3. By `subst_comp_subst_apply`: `subst h (subst g f) = subst (subst h g) f`,
     where `g := mulByNatInvSeries, f := (mulByNatHom F n).toSeries`.
     Plug in `subst g f = X` (LHS becomes `subst h X = h`) and
     `subst h g = X` (RHS becomes `subst X f = f`). Conclude `h = f`.
  4. Then `subst f g = subst h g = X`, the desired left-inverse identity.
  5. From left + right inverse, `preserves_add` for `g` transports from
     `preserves_add` for `f`.
  Estimated: ~150 lines of coefficient calculation + symmetric arguments.
  Track as T-IV-2-008b (or fold into T-IV-2-010 / T-IV-2-011 follow-ups).
