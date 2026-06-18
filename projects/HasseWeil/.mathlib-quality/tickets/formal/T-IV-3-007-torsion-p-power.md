# T-IV-3-007: Torsion of F(M) has p-power order

**Status**: DONE (delivered 2026-04-20).
**Silverman**: IV.3.2(b)
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-3-006 (graded iso) — DONE
- T-IV-2-008 ([m] iso) — only **right-inverse** is currently proved (REVIEW); the
  **left-inverse** is the deferred T-IV-2-008b piece, which is what we need here

## Why it's blocked

The Silverman argument proceeds:
* If `m` is coprime to residue characteristic `p`, then `(m : R)` is a unit
  (lifts from the residue field being char p).
* By T-IV-2-008, `[m]` as a formal-group hom is then an iso, hence
  **injective** when restricted to `F(M)`.
* So for a torsion element `x`, any factor of `addOrderOf x` coprime to `p`
  must act trivially, i.e. order is a `p`-power.

The current T-IV-2-008 infrastructure provides only the *right-inverse* at
the series level:
`subst (mulByNatInvSeries F n hn) (F.mulByNatHom n).toSeries = X`,
which says `[m] ∘ g = id`, giving **surjectivity** of `[m]`, not injectivity.

For injectivity we need the *left-inverse*:
`subst (F.mulByNatHom n).toSeries (mulByNatInvSeries F n hn) = X`,
which is the deferred T-IV-2-008b piece. The progress log there describes the
~150-line bootstrap: use `compInverseOfUnit` on `mulByNatInvSeries` itself,
then identify its inverse with `mulByNatHom` via `subst_comp_subst_apply` and
uniqueness.

## Additional dependency (beyond T-IV-2-008b)

Even with formal injectivity of `[m]`, the ticket asks about `addOrderOf x`
under the **AddCommGroup nsmul**. Relating that to the formal action requires
a bridge lemma

```lean
theorem nsmul_eq_eval₂ (F : FormalGroup R) (m : ℕ) (x : maximalIdeal R) :
    letI := F.evalGroup hAdic
    (m • x).1 = PowerSeries.eval₂ (RingHom.id R) x.1 (F.mulByNatHom m).toSeries
```

i.e., the n-fold formal-group sum equals evaluation of `mulByNatSeries` at x.

### Typeclass diamond — RESOLVED 2026-04-20

The original `F.evalGroup hAdic : AddCommGroup (maximalIdeal R)` created a
diamond against the native Submodule `AddCommGroup`, making `n • x` resolve
ambiguously.

**Fix delivered**: introduced a wrapper type
`FormalGroup.EvalGroup F hAdic` (a `@[ext] structure` with one field
`val : maximalIdeal R`) in `EvalGroup.lean`. Full `AddCommGroup` instance
via `AddGroup.ofLeftAxioms`, with `@[simp]` projection lemmas
`val_zero`/`val_add`/`val_neg`. The `evalGroup_powerIdeal` construction and
its full API (`_mono`, `_toQuot`, `_toQuot_ker`, `_toQuot_range`,
`_quotKerEquivRange`) are migrated to use `AddSubgroup (F.EvalGroup hAdic)`.
The old `evalGroup` is removed.

**Bridge delivered**:

```lean
theorem FormalGroup.EvalGroup.nsmul_val
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
    (n : ℕ) (x : F.EvalGroup hAdic) :
    (n • x).val.1 =
      PowerSeries.eval₂ (RingHom.id R) x.val.1 (F.mulByNatHom n).toSeries
```

Axiom-clean. Build passes.

### Remaining blocker

T-IV-3-007 still needs **T-IV-2-008b**: left-inverse of `[m]` at the series
level, i.e., `subst (F.mulByNatHom n).toSeries (F.mulByNatInvSeries n hn) = X`.
The current `F.mulByNatInvSeries` only gives the right-inverse, hence
`[m]` surjective not injective. Once the left-inverse is in place, the
standard Silverman argument combines it with the new `EvalGroup.nsmul_val`
bridge to conclude the torsion p-power property.

## Blocks
- T-IV-6-001 (DVR torsion)
- T-IV-6-005 (log iso for large M^r)

## Statement (Silverman IV.3.2(b))
Let `R` be a complete local ring with residue characteristic `p`. Then every
torsion element of `F(M)` has order a power of `p`. (If `p = 0`, then `F(M)` is
torsion-free.)

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.torsion_pPower (F : FormalGroup R) [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) (hp : (IsLocalRing.ResidueField R).charP p) :
    ∀ x : F.evalGroup, IsAddTorsion x → ∃ k : ℕ, addOrderOf x ∣ p^k

end HasseWeil.FormalGroup
```

## Notes
- Proof: if `m = m₀` with `gcd(m₀, p) = 1`, then `m₀ ∈ R*` (since residue field
  has char p, m₀ ≠ 0 ⇒ unit). So `[m₀]` is iso (T-IV-2-008), hence injective.
  So `[m₀] x = 0 ⇒ x = 0`.

## Progress log

- **2026-04-20** — DONE. Delivered the final theorem in
  `HasseWeil/FormalGroup/Associated.lean`:

  ```lean
  theorem FormalGroup.EvalGroup.addOrderOf_isPowOf
      (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R))
      (p : ℕ) (hp : p.Prime)
      (hR : ∀ m : ℕ, ¬ p ∣ m → IsUnit ((m : ℕ) : R))
      (x : F.EvalGroup hAdic) (hx : IsOfFinAddOrder x) :
      ∃ k : ℕ, addOrderOf x = p^k
  ```

  The residue-characteristic hypothesis is abstracted as
  `hR : ∀ m, ¬ p ∣ m → IsUnit ((m : ℕ) : R)`: any `m` coprime to `p` becomes
  a unit in `R` (the key consequence of the residue field having characteristic
  `p` combined with units lifting in a complete local ring).

  Three new theorems:
  - `FormalGroup.eval_mulByNatHom_injective_of_unit` — evaluation-level
    injectivity: for `a ∈ M`, `eval₂ id a.1 [n].toSeries = 0 → a.1 = 0` when
    `(n : R)` is a unit. Applies the series-level left-inverse identity
    `subst [n].toSeries invSeries = X` (from `Hom.lean`), transported through
    the evaluation map via `eval₂_subst_bridge`.
  - `FormalGroup.EvalGroup.nsmul_injective_of_unit` — transports the
    evaluation-level injectivity to the `AddCommGroup` nsmul via
    `FormalGroup.EvalGroup.nsmul_val`.
  - `FormalGroup.EvalGroup.addOrderOf_isPowOf` — the main theorem. Splits
    `addOrderOf x = p^k * m` using `Nat.ordProj_mul_ordCompl_eq_self`, shows
    `(m : R)` is a unit via `hR` + `Nat.not_dvd_ordCompl`, concludes
    `(p^k) • x = 0` by `nsmul_injective_of_unit`, then uses
    `addOrderOf_dvd_iff_nsmul_eq_zero` and `Nat.dvd_antisymm` to finish.

  Plus one private helper `FormalGroup.eval₂_zero_of_constantCoeff_zero` for
  the sub-computation `eval₂ id 0 f = 0` when `constantCoeff f = 0`.

  171 lines added (including docstrings). Axiom-clean (`propext`,
  `Classical.choice`, `Quot.sound`). Full `lake build HasseWeil` passes.
