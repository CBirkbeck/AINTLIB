# T-V-1-3-RAMIDX-EQ-ORDATPOINT: Sinf carrier ramification index = curve ordAtPoint at kernel primes

**Status**: OPEN (single isolated valuation **value-identity** sub-leaf — RE-EXTRACTED as a named, reusable lemma; consumed inequality now sorry-free, 2026-05-26 deep-pass #3)
**Silverman**: V.1.1 proof (book p. 138, ramification computation)
**Module**: `HasseWeil/Hasse/L6Witnesses.lean`
**Stream**: F (V.1.3 substrate, Bridge B(iii))
**Difficulty**: hard (substantial new infrastructure — valuation identification across two Dedekind domains, uniform across `ord_P` / `ordAtInfty`, with value-group normalisation)
**Estimated lines**: ~200-400 (full `v_{P_T} = exp(-ord_T)` identity: valuation-subring uniqueness via `LocalSubring` maximality + value-group normalisation + `ordAtInfty` DVR/ValuationSubring packaging)
**Spawned by**: `/develop` deep-pass on `bridge_Biii_ord_eq_neg_two_v2` (2026-05-26)

## UPDATE (2026-05-26 deep-pass #3): residual RE-EXTRACTED as reusable value identity; consumed inequality sorry-free

The consumed inequality `Sinf_intValuation_le_exp_neg_at_kernel` (`ord_T(a) ≥ m →
v_{P_T}.intValuation a ≤ exp(-m)`) is **no longer the `sorry`-bearing declaration**: it is
now *derived* (purely formally, no `sorry`) from a freshly-extracted named leaf — the
per-element **value identity** in `ℤᵐ⁰`:

```lean
-- THE SOLE SORRY (sorryAx source for the whole chain):
theorem Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel (W hq data T)
    (d : ℤ) (a : data.carrier) (ha0 : a ≠ 0)
    (had : ordAtPoint T.val (algebraMap data.carrier (LinfAt …) a) = (d : WithTop ℤ)) :
    (Sinf_kernelPrime_heightOne W hq data T).intValuation a = WithZero.exp (-d)
```

The derivation of `Sinf_intValuation_le_exp_neg_at_kernel` from this leaf:
* `a = 0` → `intValuation 0 = 0 ≤ exp(-m)` (`Valuation.map_zero`, `WithZero.zero_le`);
* `a ≠ 0` → `algebraMap a ≠ 0` (`IsFractionRing.injective`), so `ord_T(algebraMap a) = (d : WithTop ℤ)`
  (`ordAtPoint_eq_top_iff`, `WithTop.ne_top_iff_exists`); the leaf gives `intValuation a = exp(-d)`,
  and `(m : WithTop ℤ) ≤ (d : WithTop ℤ)` forces `m ≤ d`, hence `exp(-d) ≤ exp(-m)`
  (`WithZero.exp_le_exp`). **Done, axiom-clean modulo the leaf.**

**Why re-extract to the value identity.** (i) It is strictly more reusable than the
inequality — the *equality* `v_{P_T} = exp(-ord_T)` is exactly what `bridge_Bii_bijective`
and `bridge_Biv_inertia_eq_one` also need (two-sided, value-precise). (ii) It names the
gap maximally sharply: the ONLY thing unproven is "carrier `P_T`-adic value = `exp(-ord_T)`
at a nonzero carrier element". (iii) The consumed inequality (hence the whole V.1.3 chain
through `bridge_Biii_ord_eq_neg_two_v2`) is now a clean `sorry`-free derivation.

`#print axioms` (verified): `Sinf_kernelPrime_pow_le_ord` axiom-clean
`[propext, Classical.choice, Quot.sound]`; the leaf
`Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel` carries `sorryAx`; and
`Sinf_intValuation_le_exp_neg_at_kernel`, `Sinf_kernelPrime_pow_mem_of_le_ord`,
`Sinf_ramificationIdx_eq_two_at_kernel`, `bridge_Biii_ord_eq_neg_two_v2` carry `sorryAx`
**only** via this one leaf (no other axioms). `lake build HasseWeil.Hasse.L6Witnesses`
clean (2941 jobs).

### Concrete discharge route identified (deep-pass #3 analysis)

The genuine content is the valuation agreement `v_{P_T} = exp(-ord_T)` on `LinfAt f`. The
cleanest route found avoids the hard "integral closure = maximal order" direction by using
**valuation-subring maximality**:

1. Let `O_{P_T} := {x ∈ LinfAt f | v_{P_T} x ≤ 1}` (the carrier's `P_T`-adic valuation
   subring) and `O_T := {x | ord_T x ≥ 0}` (the curve's valuation subring at `T`).
2. **Easy inclusion + domination** `O_{P_T} ≤ O_T` in the `LocalSubring` domination order
   (`Mathlib/RingTheory/LocalRing/LocalSubring.lean:69`, `le_def`): for `x = a/s`
   (`a ∈ carrier`, `s ∈ carrier \ P_T`) one has `ord_T s = 0` (since `s ∉ P_T` and
   `ord_T ≥ 0` on the carrier — `Sinf_ord_nonneg_at_kernel_point_unconditional`, shipped),
   so `ord_T x = ord_T a ≥ 0` (subring inclusion) and a unit of `O_{P_T}` has `ord_T = 0`
   (the local-hom condition). Both follow from the *definition* of `P_T` + the shipped
   nonneg fact — **easy**.
3. **Maximality** `ValuationSubring.isMax_toLocalSubring`
   (`Mathlib/RingTheory/Valuation/LocalSubring.lean:78`): `O_{P_T}` is `IsMax`, so
   `O_{P_T} ≤ O_T` forces `O_T ≤ O_{P_T}`, hence `O_{P_T} = O_T` (`IsMax.eq_of_le`) — the
   two valuation subrings coincide. **(The reverse "maximal order" inclusion is FREE here.)**
4. **Value-group normalisation** (the remaining genuine work): equal valuation subrings give
   `v_{P_T}.IsEquiv (curve valuation at T)`, but the *value identity* in `ℤᵐ⁰` needs a common
   uniformizer realising `exp(-1)` carrier-side (`intValuation_singleton` /
   `intValuation_exists_uniformizer`, `AdicValuation.lean:253,280`) and `ord = 1` curve-side
   (`Uniformizer`, `Curves/Valuation.lean:247`), then multiplicativity + surjectivity.
5. **`ordAtInfty` branch packaging** (the `T.val = .zero` case): `ordAtInfty`
   (`Curves/Infinity.lean:81`) is `-intDegree ∘ normAsRatFunc`, *not* a DVR/`HeightOneSpectrum`
   /`ValuationSubring` — step 1's `O_T` and steps 2–4 must be re-established for it (its
   valuation subring needs to be exhibited as a `ValuationSubring`, e.g. via the place at
   infinity / `Curves/Infinity.lean` DVR ticket referenced there). This is the main extra
   infrastructure beyond the finite-point case.

Steps 2–3 are tractable (~40-80 LOC); steps 4–5 are the substantial remainder. This is the
same `bridge_Bii`-level closed-point ↔ prime content; not an import unblock.

## UPDATE (2026-05-26 deep-pass #2): membership lemma DERIVED, residual = ONE valuation inequality

The reverse **membership** lemma `Sinf_kernelPrime_pow_mem_of_le_ord` is **no longer a
`sorry`**: it is now *derived* by packaging `P_T` as an
`IsDedekindDomain.HeightOneSpectrum data.carrier` and applying
`IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem`
(`a ∈ v.asIdeal^n ↔ v.intValuation a ≤ exp(-n)`, `AdicValuation.lean:248`).

Two new axiom-clean infrastructure declarations support the packaging
(`L6Witnesses.lean`):

```lean
-- AXIOM-CLEAN [propext, Classical.choice, Quot.sound]:
theorem Sinf_kernelPrime_ne_bot (W hq data T) :
    bridge_Bi_kernelToPrime_v2 W hq data T ≠ ⊥
-- proof: witness xc = algebraMap (Polynomial K) carrier X ∈ P_T (ord_T(f⁻¹)=2>0),
--        nonzero since its image f⁻¹ ≠ 0 and algebraMap carrier (LinfAt f) injective.

noncomputable def Sinf_kernelPrime_heightOne (W hq data T) :
    IsDedekindDomain.HeightOneSpectrum data.carrier :=
  { asIdeal := bridge_Bi_kernelToPrime_v2 W hq data T
    isPrime := bridge_Bi_isPrime_v2 …, ne_bot := Sinf_kernelPrime_ne_bot … }
```

**The sole remaining `sorry`** is now the precise one-direction valuation inequality
(genuine closed-point ↔ prime content), with `P_T` *already packaged*:

```lean
-- THE ONLY SORRY (sorryAx source for the whole chain):
theorem Sinf_intValuation_le_exp_neg_at_kernel (W hq data T) (m : ℤ) (a : data.carrier)
    (ha : (m : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap data.carrier (LinfAt …) a)) :
    (Sinf_kernelPrime_heightOne W hq data T).intValuation a ≤ WithZero.exp (-m)
```

`#print axioms` (verified): `Sinf_kernelPrime_ne_bot`, `Sinf_kernelPrime_heightOne`,
and the forward half `Sinf_kernelPrime_pow_le_ord` are axiom-clean
(`[propext, Classical.choice, Quot.sound]`). `Sinf_intValuation_le_exp_neg_at_kernel`,
`Sinf_kernelPrime_pow_mem_of_le_ord`, `Sinf_ramificationIdx_eq_two_at_kernel`, and
`bridge_Biii_ord_eq_neg_two_v2` carry `sorryAx` **only** via this one leaf.
`lake build HasseWeil.Hasse.L6Witnesses` clean (2941 jobs).

This is the genuine residual: `Sinf_intValuation_le_exp_neg_at_kernel` is the reverse
half of `v_{P_T}(a) = exp(-ord_T(a))` — the carrier's intrinsic `P_T`-adic
`intValuation` (integral closure of `Polynomial K` in `LinfAt f`) agrees with the
curve's geometric `ordAtPoint T` (`W.CoordinateRing` localized at `maximalIdealAt T`),
two valuations on the shared fraction field `LinfAt f = FunctionField`. The forward
half (`a ∈ P_T^n → ord_T(a) ≥ n`, i.e. the `≤ exp(-n) → ord_T ≥ n` direction) IS
SHIPPED as `Sinf_kernelPrime_pow_le_ord`. Closing this single inequality (via
`IsFractionRing`/DVR valuation-uniqueness on `LinfAt f`) discharges B(iii) and is the
same content underlying `bridge_Bii_bijective` / `bridge_Biv_inertia_eq_one`.

## UPDATE (2026-05-26 deep-pass): keystone REDUCED, easy half SHIPPED

The keystone `Sinf_ramificationIdx_eq_two_at_kernel` is **no longer a `sorry`**: it
is now proved (axiom-clean modulo this leaf) by `Ideal.ramificationIdx_spec` with
`n = 2`, reducing to two ideal-membership facts about `xc := algebraMap (Polynomial K)
carrier X` (whose image in `LinfAt f` is `f⁻¹`):

* `xc ∈ P_T ^ 2`  — needs the **reverse** valuation direction (this leaf);
* `xc ∉ P_T ^ 3`  — discharged by the **forward** direction, now SHIPPED.

Two helper lemmas now sit in `L6Witnesses.lean`:

```lean
-- SHIPPED, axiom-clean ([propext, Classical.choice, Quot.sound]):
theorem Sinf_kernelPrime_pow_le_ord (W hq data T) (n : ℕ) (a : data.carrier)
    (ha : a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T) ^ n) :
    (n : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap data.carrier (LinfAt …) a)
-- proof: `Submodule.pow_induction_on_left'` + `Sinf_ord_nonneg_at_kernel_point_unconditional`
--        + `ordAtPoint_add_le` / `ordAtPoint_mul`.

-- THE REMAINING SORRY (this leaf):
theorem Sinf_kernelPrime_pow_mem_of_le_ord (W hq data T) (n : ℕ) (a : data.carrier)
    (ha : (n : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap data.carrier (LinfAt …) a)) :
    a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T) ^ n
```

`#print axioms` confirms: `Sinf_kernelPrime_pow_le_ord` is axiom-clean;
`Sinf_ramificationIdx_eq_two_at_kernel`, `bridge_Biii_ord_eq_neg_two_v2`, and
`Sinf_kernelPrime_pow_mem_of_le_ord` carry `sorryAx` **only** via this one leaf.

The new target leaf statement (replacing the old keystone-as-sorry framing):

```lean
theorem Sinf_kernelPrime_pow_mem_of_le_ord
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (n : ℕ) (a : data.carrier)
    (ha : (n : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap data.carrier (LinfAt …) a)) :
    a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T) ^ n
```

## Why it is the irreducible residual

`bridge_Biii_ord_eq_neg_two_v2` is **fully discharged** modulo this one leaf:
`Sinf.ordAt P = -(ramificationIdx (algebraMap (Polynomial K) carrier) (X) P : ℤ)`
**by definition** (`RamificationAtInfinity.lean:476`), so the `= -2` goal reduces
(axiom-clean, via `change` + `rw`) to the `ℕ`-level `ramificationIdx … = 2`, now
itself reduced (above) to `Sinf_kernelPrime_pow_mem_of_le_ord`.

The mathematical chain for the leaf is:

| step | content | mathlib / project lemma |
|------|---------|-------------------------|
| 1 | `ramificationIdx (algebraMap) (X) P_T = 2` via `xc ∈ P_T^2 ∧ xc ∉ P_T^3` | `Ideal.ramificationIdx_spec` (`Basic.lean:86`); `Ideal.map_span`, `Ideal.span_singleton_le_iff_mem` — **DONE** |
| 1' | (alt) `= count P_T (normalizedFactors (xIdeal.map))` | `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count` (`Basic.lean:211`), `…_eq_multiplicity:221` |
| 2 | `xc ∈ P_T^n ⟺ v_{P_T}(xc) ≤ exp(-n)` (carrier intValuation) | `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem` (`AdicValuation.lean:248`), `intValuation_le_pow_iff_dvd:237` |
| 3 | image of `X` under `algebraMap (Polynomial K) carrier` = `f⁻¹` (in `LinfAt f`) | `LinfAt.algebraMap_polynomial_apply` (`RamificationAtInfinity.lean:186`), `polyToFieldOfInv_X:70`; **DONE** (keystone `h_ord_xc`) |
| 4 | **(open)** carrier `P_T`-adic `intValuation a` ≤ `exp(-m)` when `ord_T(a) ≥ m` (reverse `≤` of `v_{P_T} = exp(-ord_T)`) | **= `Sinf_intValuation_le_exp_neg_at_kernel`, the leaf** (membership `Sinf_kernelPrime_pow_mem_of_le_ord` now DERIVED via `intValuation_le_pow_iff_mem` + `Sinf_kernelPrime_heightOne`) |
| 5 | `ord_T(f⁻¹) = 2` | `Conditional.inv_gamma_pullback_x_pos_at_kernel` (`L6Witnesses.lean:218`, shipped axiom-clean) — **DONE** |

**Step 4 (reverse direction only) is the genuine gap.** The forward direction
(`v_{P_T}(a) ≥ exp(-ord_T(a))`, i.e. `Sinf_kernelPrime_pow_le_ord`: `a ∈ P_T^n →
ord_T(a) ≥ n`) is now SHIPPED axiom-clean directly from `P_T`'s definition by
`pow_induction`. The reverse direction asserts `P_T^n` is *exactly*
`{a | ord_T(a) ≥ n}` — that `ord_T` restricted to the carrier *is* the carrier's
intrinsic `P_T`-adic valuation (up to uniformizer normalization). The curve
valuation `ordAtPoint T` (= `ord_P` /
`ordAtInfty`) is built from `W.CoordinateRing` localized at `maximalIdealAt T`
(`Curves/Valuation.lean:63`, `Curves/OrdAtPoint.lean:57`). The Sinf carrier is a
**different** `IsDedekindDomain` — the integral closure of `Polynomial K` in
`LinfAt f` (`RamificationAtInfinity.lean:357`). Both share the fraction field
`LinfAt f = W.toAffine.FunctionField`, but no lemma identifies the carrier's
intrinsic `P_T`-adic valuation with the curve's `ordAtPoint T`. The
order-based prime `bridge_Bi_kernelToPrime_v2` is defined *via the curve
valuation* (`{a : ord_T(algebraMap a) > 0}`), not as a `HeightOneSpectrum` of
the carrier, so even establishing `P_T ≠ ⊥` / height-one and the
`HeightOneSpectrum` packaging is part of the work.

This identification IS the geometric closed-point ↔ prime correspondence, the
same content underlying the still-open `bridge_Bii_bijective`
(`OpenLemmas.lean:414`, `sorry`). It is substantial new infrastructure, not an
import unblock.

## Depends on / consumes-into

- **Consumed by**: `bridge_Biii_ord_eq_neg_two_v2` (L6Witnesses, shipped modulo this leaf),
  the downstream analogue of upstream `HasseWeil.bridge_Biii_ord_eq_neg_two`
  (`OpenLemmas.lean:448`, `sorry`). Provides the ramification side of V.1.3.
- **Sibling**: `bridge_Biv_inertia_eq_one` (inertia side) and `bridge_Bii_bijective`
  (the bijection), both still `sorry` in OpenLemmas — all three need the same
  carrier↔curve identification.

## Discharge route (recommended)

**Packaging is now DONE** (deep-pass #2): `P_T` is a `HeightOneSpectrum`
(`Sinf_kernelPrime_heightOne`), and `Sinf_kernelPrime_pow_mem_of_le_ord` is derived
via `intValuation_le_pow_iff_mem`. The ONLY remaining target is the inequality

```lean
Sinf_intValuation_le_exp_neg_at_kernel :
  (m : WithTop ℤ) ≤ ordAtPoint T.val (algebraMap … a) →
    (Sinf_kernelPrime_heightOne …).intValuation a ≤ WithZero.exp (-m)
```

i.e. the **reverse** half of `v_{P_T}(a) = exp(-ord_T(a))` on the carrier. Two viable
routes for *this* inequality:

1. **Full valuation identity (recommended).** Prove the `Valuation`-level identity
   `v_{P_T} = exp(-ord_T)` on `LinfAt f` (a `Sinf.intValuation_carrier_eq_ordAtPoint_at_kernel`
   helper on the shared fraction field), then `Sinf_intValuation_le_exp_neg_at_kernel`
   is immediate. Prove the identity by `IsFractionRing`/DVR valuation-uniqueness
   against the curve's `pointValuation T` / `localRingAt T` (`Curves/Valuation.lean:41`):
   both are `HeightOneSpectrum`/DVR valuations on `LinfAt f` whose valuation rings
   share the maximal ideal traced from `P_T = {ord_T > 0}`. Useful mathlib:
   `Valuation.isEquiv_iff_val_le_one`, `IsDiscreteValuationRing` / `IsLocalization.AtPrime`
   API; the project already uses `Valuation.IsEquiv` + `isEquiv_iff_val_le_one` for an
   analogous transport in `HasseWeil/EC/TranslationOrd.lean` (e.g.
   `isTranslateMaxIdealCompatible_iff_isEquiv`, lines ~4750–5117).

2. **Directly.** Exhibit a uniformizer `π ∈ P_T` with `ord_T(π) = 1` and use the DVR
   structure of `carrier_{P_T}` to factor any `a` with `ord_T(a) ≥ m` as `π^m · unit`,
   then read off `v_{P_T}(a) ≤ exp(-m)`.

The forward direction is already done (`Sinf_kernelPrime_pow_le_ord`); steps 1, 1', 2,
3, 5 in the table are shipped/mechanical, and the `HeightOneSpectrum` packaging (was
"part of the work") is now also done.

## Acceptance criteria

- `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel` proved (no `sorry`) — the single
  residual value identity. (`Sinf_intValuation_le_exp_neg_at_kernel` and
  `Sinf_kernelPrime_pow_mem_of_le_ord` are DERIVED from it; no separate work.)
- `#print axioms HasseWeil.Sinf_ramificationIdx_eq_two_at_kernel` and
  `HasseWeil.bridge_Biii_ord_eq_neg_two_v2` →
  `[propext, Classical.choice, Quot.sound]` only.
- `lake build HasseWeil.Hasse.L6Witnesses` clean.
- (Stretch) generalise the value identity to a `Valuation`-level `v_{P_T} = exp(-ord_T)`
  on all of `LinfAt f` (not only carrier elements) and a
  `Sinf.ramificationIdx_eq_neg_ordAtPoint`, then retarget `bridge_Biv_inertia_eq_one` /
  `bridge_Bii_bijective`.

## Progress log

- 2026-05-26 (`/develop` deep-pass): keystone `Sinf_ramificationIdx_eq_two_at_kernel`
  REDUCED from a bare `sorry` to `Ideal.ramificationIdx_spec` (n=2) over the two
  membership facts. Forward half `Sinf_kernelPrime_pow_le_ord` SHIPPED axiom-clean.
  Residual isolated as `Sinf_kernelPrime_pow_mem_of_le_ord` (reverse direction).
  `lake build HasseWeil.Hasse.L6Witnesses` clean (2941 jobs); only `sorryAx` source
  is this leaf.
- 2026-05-26 (`/develop` deep-pass #2): reverse **membership** lemma
  `Sinf_kernelPrime_pow_mem_of_le_ord` DERIVED (no bare `sorry`) by packaging `P_T`
  as `Sinf_kernelPrime_heightOne : IsDedekindDomain.HeightOneSpectrum data.carrier`
  (new, axiom-clean; `ne_bot` via new axiom-clean `Sinf_kernelPrime_ne_bot`) and
  applying `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem`
  (`AdicValuation.lean:248`). The sole `sorry` is now the precise one-direction
  valuation inequality `Sinf_intValuation_le_exp_neg_at_kernel`
  (`ord_T(a) ≥ m → v_{P_T}.intValuation a ≤ exp(-m)`), the reverse half of
  `v_{P_T} = exp(-ord_T)`. `#print axioms`: `Sinf_kernelPrime_ne_bot`,
  `Sinf_kernelPrime_heightOne`, `Sinf_kernelPrime_pow_le_ord` axiom-clean; the
  membership lemma, keystone, and `bridge_Biii_ord_eq_neg_two_v2` carry `sorryAx`
  only via this one leaf. `lake build HasseWeil.Hasse.L6Witnesses` clean (2941 jobs).
  Mathlib lemmas used: `intValuation_le_pow_iff_mem`; `HeightOneSpectrum` structure
  (`Ideal/Lemmas.lean:458`); `WithZero.exp`. Project: `bridge_Bi_isPrime_v2`,
  `inv_gamma_pullback_x_pos_at_kernel`, `LinfAt.algebraMap_polynomial_apply`,
  `polyToFieldOfInv_X`, `ordAtPoint_zero_function`.
- 2026-05-26 (`/develop` deep-pass #3): residual RE-EXTRACTED as the named, reusable
  **value-identity** leaf `Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`
  (`a ≠ 0 → ord_T(algebraMap a) = d → v_{P_T}.intValuation a = exp(-d)`). The consumed
  inequality `Sinf_intValuation_le_exp_neg_at_kernel` is now `sorry`-free (derived
  formally: `a = 0` trivial via `Valuation.map_zero`/`WithZero.zero_le`; `a ≠ 0` via
  `IsFractionRing.injective` + `ordAtPoint_eq_top_iff` + `WithTop.ne_top_iff_exists` +
  `WithZero.exp_le_exp`). `#print axioms`: leaf carries `sorryAx`;
  `Sinf_intValuation_le_exp_neg_at_kernel`, `Sinf_kernelPrime_pow_mem_of_le_ord`,
  `Sinf_ramificationIdx_eq_two_at_kernel`, `bridge_Biii_ord_eq_neg_two_v2` carry `sorryAx`
  ONLY via the leaf (otherwise standard `[propext, Classical.choice, Quot.sound]`);
  `Sinf_kernelPrime_pow_le_ord` axiom-clean. `lake build HasseWeil.Hasse.L6Witnesses` clean
  (2941 jobs). Concrete discharge route (valuation-subring maximality via
  `ValuationSubring.isMax_toLocalSubring` / `LocalSubring` domination + value-group
  normalisation, with separate `ordAtInfty` `ValuationSubring` packaging for `T.val = .zero`)
  recorded above; analysis confirmed the easy valuation-subring *inclusion* + maximality
  collapses the hard "maximal order" direction, leaving value-group normalisation + the
  `ordAtInfty` packaging as the substantial remainder. This is `bridge_Bii`-level content,
  not closable as an import unblock within deep-pass scope.
