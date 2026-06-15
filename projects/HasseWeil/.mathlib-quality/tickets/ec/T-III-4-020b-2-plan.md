# T-III-4-020b-2: `mulByInt_x W n = Affine.Point.xOf (n • genericPoint W)`

**Parent**: T-III-4-020b (Silverman III.4.2 core — `[m] ∘ [n] = [m·n]`)
**Status**: ✅ **CLOSED** (Jacobian-based main theorem landed 2026-04-20)
**Estimated scope**: 400-600 lines across multi-session effort
**Silverman ref**: Exercise III.3.7 (division polynomial explicit formula)
**Owner**: worker-A

## Goal

For `n ≠ 0`, prove in `HasseWeil/EC/GenericPointZsmul.lean`:
```lean
theorem zsmul_genericPoint_eq (n : ℤ) (hn : n ≠ 0) :
    n • genericPoint W =
      Affine.Point.some (mulByInt_x W n) (mulByInt_y W n)
        (generic_nonsingular_at W n hn)
```

This is the connection between the division-polynomial definition of
`mulByInt_x W n = Φ_n / ΨSq_n`, `mulByInt_y W n = ω_n / ψ_n³` and the
group-law `n`-th multiple of the generic point.

Once this lands, T-III-4-020b (Silverman III.4.2) follows routinely via
`mulByInt_pullback_unique` + the two-coordinate composition identities.

## Silverman's proof (Exercise III.3.7, pp. 105-106)

The reference we follow is **Silverman Exercise III.3.7**, which provides
"an elementary, highly computational proof that [m] has degree m²".

### Silverman's setup

Division polynomials `ψ_m ∈ ℤ[a₁, ..., a₆, x, y]`:
- `ψ₁ := 1`
- `ψ₂ := 2y + a₁x + a₃`
- `ψ₃ := 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`
- `ψ₄ := ψ₂ · (2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x² + (b₂b₈ - b₄b₆)x + (b₄b₈ - b₆²))`

Recurrences (for `m ≥ 2`):
- `ψ_{2m+1} = ψ_{m+2} · ψ_m³ - ψ_{m-1} · ψ_{m+1}³`
- `ψ_{2m} · ψ₂ = ψ_m² · (ψ_{m+2} · ψ_{m-1}² - ψ_{m-2} · ψ_{m+1}²)` (for `m ≥ 3`)

Associated polynomials:
- `φ_m := x·ψ_m² - ψ_{m+1}·ψ_{m-1}`
- `4y·ω_m := ψ_{m-1}²·ψ_{m+2} + ψ_{m-2}·ψ_{m+1}²`

### Silverman's parts (a)-(g), summarised

* **(a)** `ψ_m, φ_m, y⁻¹ω_m` are polynomials in `ℤ[a₁,...,a₆, x, (2y+a₁x+a₃)²]` for odd m.
* **(b)** `φ_m(x) = x^{m²} + ...`, `ψ_m(x)² = m²·x^{m²-1} + ...`.
* **(c)** If `Δ ≠ 0`, then `φ_m(x)` and `ψ_m(x)²` are relatively prime in `K[x]`.
* **(d) [KEY]** For any point `P = (x₀, y₀) ∈ E` with `Δ ≠ 0`:
  ```
  [m]P = (φ_m(P)/ψ_m(P)², ω_m(P)/ψ_m(P)³)
  ```
* **(e)** `deg[m] = m²` (follows from (d) + (b) + (c)).
* **(f)** `div(ψ_n) = Σ_{T ∈ E[n]} (T) - n²(O)` (ψ_n vanishes on n-torsion).
* **(g)** Composition identity:
  ```
  ψ_{n+m}·ψ_{n-m}·ψ_r² = ψ_{n+r}·ψ_{n-r}·ψ_m² - ψ_{m+r}·ψ_{m-r}·ψ_n²   for n > m > r
  ```

### Silverman's proof of (d) (implicit outline)

Silverman sketches the induction: for `P = (x,y)`, check `[1]P = P`
(base case, matches `φ₁/ψ₁² = x`, `ω₁/ψ₁³ = y`), then use the addition formula
on `E` plus the recurrences for `ψ_m, φ_m, ω_m` to show
`[m]P + P = [m+1]P` gives coordinates `(φ_{m+1}/ψ_{m+1}², ω_{m+1}/ψ_{m+1}³)`.

The algebraic identities that make this work are (g) above plus the
standard `addX(x₁, x₂, slope) = ...` formula from the group law, applied
at the generic point.

## Why the universal-lift approach was abandoned (Phase A obstruction)

The original strategy was to prove `zsmul_point_eq_smulX_smulY` for the
universal curve once and specialize via a ring hom
`specField : Universal.Field →+* K(E)`.

**The obstruction**: For a generic `W`, the lift `ringEval : Universal.Ring → KE`
is NOT injective (it sends formal universal variables `a₁, a₂, a₃, a₄, a₆`
to concrete `W.a₁, ..., W.a₆` which may be zero, so non-zero-divisors of
`Universal.Ring` can go to zero). This prevents `IsLocalization.lift` from
extending `ringEval` to a field hom.

Moreover, `ψ_n ∈ K(E)` is nonzero but has zeros (at the n-torsion locus, by
Silverman 3.7(f)), so even treating `ψ_n` as a unit in `K(E)` doesn't salvage
the lift: the unit condition in `IsLocalization.lift` requires the image to
be a unit, not just nonzero.

**Verdict**: The "lift universal identity to W_KE via a ring hom" pattern
cannot close this ticket. We must port the induction directly.

## Chosen strategy: port mathlib's `Affine.zsmul_point_eq_smulX_smulY`

File: `HasseWeil/Auxiliary/DivisionPolynomial.lean`, lines 248-458. The
proof has ~210 lines of helper lemmas + main induction. We port it to the
W_KE setting (using `mulByInt_x W n, mulByInt_y W n` in place of
`smulX n, smulY n`, and `genericPoint W` in place of `Affine.point`).

The ported lemmas follow Silverman Ex 3.7 essentially verbatim, just with
the F-field `K(E)` and our specific `W` in place of `Universal.Field` and
`pointedCurve`. The algebraic content is identical; only the concrete
ring is different.

## Decomposition (dependency DAG)

```
  Phase 0 (DONE):
    0a: Affine.Point.map  [~30 lines, HasseWeil/EC/AffinePointMap.lean]
    0b: map_add           [~100 lines]
    0c: map_zsmul         [~20 lines]

  Phase 1 (NEW PLAN — direct induction, no lift):
    Task #1  [DONE]: n=1 base case (genericPoint_eq_mulByInt_one)
    Task #4:  mulByInt_x_eq (rational form: x_gen - ψ(n+1)ψ(n-1)/ψ(n)²)
    Task #5:  mulByInt_x_sub_mulByInt_x  (uses Silverman Ex 3.7(g))
    Task #6:  mulByInt_x_ne_mulByInt_x   (distinctness)
    Task #7:  mulByInt_y_sub_negY        (= ψ(2n)/ψ(n)⁴)
    Task #8:  slopeOne + addX/addY_one_one (doubling case: n=2)
    Task #9:  mulByInt_x_add (addition formula for n+m)
    Task #10: mulByInt_y_add_sub_negY
    Task #11: zsmul_genericPoint_eq (main induction)

  Auxiliary (DONE in session):
    Task #1 (mulByInt_y_neg): negation case y-coordinate — needed for neg
    Task #2 (zsmul_genericPoint_neg): reduce n<0 to n>0

  Phase 2 (after Phase 1):
    Task #12: mulByInt_pullback_x_gen via Point-map functoriality
    Task #13: mulByInt_pullback_y_gen version
    Task #14: mulByInt_comp_eq_mul (using unique + Phase 2 witnesses)
```

### Critical path (by lemma ordering)

```
  Task#4 (smulX_eq) → Task#5 (smulX_sub) → Task#6 (ne) → Task#9 (smulX_add)
                                         ↘          ↘
  Task#7 (smulY_sub_negY) → Task#8 (doubling)     ↘
                                                    Task#11 (main)
  Task#10 (smulY_add)  ───────────────────────────↗
```

### Parallelizable work

- Task #4 (smulX_eq) can be done independently.
- Task #7 (smulY_sub_negY) can be done independently of Task #4-6.
- After Task #5+#7: Task #8 (doubling), Task #9 (smulX_add), Task #10 (smulY_add) in parallel.

## Session 1 deliverables (April 20, 2026)

Landed (axiom-clean):
1. ✅ **ψ_ff_neg**: `ψ_ff W (-n) = -ψ_ff W n` (simp lemma).
2. ✅ **mulByInt_y_neg**: `mulByInt_y W (-n) = negY(mulByInt_x, mulByInt_y)`.
3. ✅ **zsmul_genericPoint_neg_of_pos**: witness-form reduction `n • → (-n) •`.
4. ✅ **mulByInt_y_sub_negY**: `mulByInt_y - negY = ψ(2n)/ψ(n)⁴` (Task #7).
5. ✅ **mulByInt_y_one_sub_negY** + **mulByInt_y_one_ne_negY** (doubling prep).

Support infrastructure landed:
- `algebraMap_mk_CC`: bridges universal `CC x` to K(E) coefficient via scalar tower.
- `ω_ff_neg`: ω_ff negation formula (using `W.ω_neg` universal polynomial).
- `ψc_ff_eq`: ψc ↔ 2·ω + a₁·Φ·ψ + a₃·ψ³ in K(E) (using `W.ω_spec`).
- `ψ_ff_mul_ψc_eq`: ψ·ψc = ψ(2n) in K(E) (using `W.ψc_spec`).
- Also made `ψ_ff_sq_eq_ΨSq_ff` and `φ_ff_eq_Φ_ff` public in MulByIntPullback.lean.

Multi-session follow-ups:
- Task #4 (mulByInt_x_eq) — rational identity via `W.Φ` definition.
- Task #5 (mulByInt_x_sub_mulByInt_x) — Silverman Ex 3.7(g) composition identity.
- Task #6 (mulByInt_x_ne_mulByInt_x) — distinctness from Task #5.
- Task #8 (slopeOne + addX/addY_one_one) — doubling closure.
- Task #9 (mulByInt_x_add) — addition formula for n+m.
- Task #10 (mulByInt_y_add_sub_negY) — y-coord addition.
- Task #11 (main induction) — ~80 lines once helpers land.

Incremental scope: ~180 lines landed this session. ~300 lines remaining.

## Risks and mitigations

- **ψ_ff W n nonvanishing**: mathlib's generic `ψ_ne_zero` should apply in K(E)
  via the fact that `W_KE` inherits elliptic structure from `W` (`IsElliptic`
  is preserved under base change). If not, Task #4 needs a preliminary
  `ψ_ff_ne_zero` lemma.
- **Specialization of EDS**: mathlib's `EllipticDivisibilitySequence` provides
  `IsEllDivSequence.smul` which shows EDS structure is preserved under ring
  scaling. We can leverage this to transfer identities for the numeric ψ_n
  coefficients.
- **Mathlib API gaps**: if some Silverman 3.7(g) identity has no direct
  mathlib analog, we may need to prove it as polynomial identity in
  `F[X][Y]` and then push to `K(E)`. This is a polynomial manipulation
  expected to fit within 50 lines per identity.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, Ex III.3.7 (pp. 105-106).
* mathlib: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
  — the `Φ`, `ΨSq`, `preΨ`, `ψ`, `ω` definitions.
* local: `HasseWeil/Auxiliary/DivisionPolynomial.lean` — universal proof to mirror.
* local: `HasseWeil/EC/AffinePointMap.lean` — Phase 0 functorial API (DONE).

## Progress log

- 2026-04-20 [worker-A] Phase 0 (a, b, c) landed. Phase A obstruction documented.
- 2026-04-20 [worker-A] Base case n=1 landed in `GenericPointZsmul.lean`.
- 2026-04-20 [worker-A] Silverman-guided comprehensive plan written.
  Scope reduced to direct-induction approach (no universal lift).
  Sub-tickets #4-#11 created covering ~400 lines of multi-session work.
- 2026-04-20 [worker-A] **Session 1 deliverables landed** (~180 lines, axiom-clean):
  - `ψ_ff_neg`, `mulByInt_y_neg`, `zsmul_genericPoint_neg_of_pos`
  - `mulByInt_y_sub_negY` + `_one_sub_negY` + `_one_ne_negY` (Task #7 done)
  - Supporting infrastructure: `algebraMap_mk_CC`, `ω_ff_neg`, `ψc_ff_eq`,
    `ψ_ff_mul_ψc_eq` in GenericPointZsmul.lean
  - Side-effect: exposed `ψ_ff_sq_eq_ΨSq_ff`, `φ_ff_eq_Φ_ff` (removed `private`)
  - Added import `HasseWeil.EC.MulByIntComp` for `mulByInt_x_neg`
  - Task #1, #2, #7 DONE. Task #4-6, #8-11 REMAIN.
- 2026-04-20 [worker-A] **Session 2 deliverables** (~90 more lines, axiom-clean):
  - `Φ_ff_eq`: bivariate expansion `Φ_ff = x_gen · ψ_ff² - ψ_ff(n+1)·ψ_ff(n-1)`
  - `mulByInt_x_eq` (Task #4): `mulByInt_x W n = x_gen - ψ(n+1)ψ(n-1)/ψ(n)²`
  - `ψ_ff_one` (simp): `ψ_ff W 1 = 1`
  - `isEllSequence_ψ_ff`: Silverman Ex 3.7(g) transferred to K(E)
  - `mulByInt_x_sub_mulByInt_x` (Task #5): composition identity
  - `mulByInt_x_ne_mulByInt_x` (Task #6): distinctness
  - **Task #8 partial**: `slopeOne` defined (as `abbrev`) + `slopeOne_eq`.
    Remaining: `addX_mulByInt_one_mulByInt_one`, `addY_mulByInt_one_mulByInt_one`
    (doubling closure — requires polynomial manipulations with `Ψ₃`, `preΨ₄`).
  - **Task #11 partial**: `zsmul_genericPoint_two_of_witness` — the n=2 case
    as a witness-parametric theorem. Given `h_addX_two, h_addY_two, h_ns_two`,
    derives `(2 : ℤ) • genericPoint W = .some (mulByInt_x W 2) (mulByInt_y W 2) _`.
    This unblocks Task #8 incrementally: future work supplies the `h_addX/Y_two`
    witnesses, and the n=2 case of the main theorem closes.
  - Task #4, #5, #6 DONE. Task #8, #11 partial. Task #9-10 REMAIN.

## Session 3 breakthrough: Jacobian approach closes T-III-4-020b-2

**The Jacobian equivalence provides a direct proof of `zsmul_genericPoint_eq`**
that BYPASSES the entire Task #8-10 addX/addY closure chain:

```
n • genericPoint W  [in Affine]
 = toAffineAddEquiv (n • Point.fromAffine genericPoint)  [map_zsmul of AddEquiv]
 = toAffineLift (n • Point.fromAffine genericPoint)      [toAffineAddEquiv_apply]
 = toAffine (W_KE W) ⟦smulEval (W_KE W) (x_gen) (y_gen) n⟧
                                                         [by zsmul_eq_smulEval]
 = .some (smulEval../0/smulEval../2², smulEval../1/smulEval../2³) _
                                                         [toAffine_of_Z_ne_zero]
 = .some (Φ_ff W n / ψ_ff W n², ω_ff W n / ψ_ff W n³) _  [smulEval_generic_X/Y/Z]
 = .some (mulByInt_x W n, mulByInt_y W n) _              [definitions]
```

Mathematical content: mathlib's `zsmul_eq_smulEval` (line 678 of Auxiliary)
already encapsulates the ENTIRE induction Silverman would require. Our
contribution is wiring it to the generic point of W_KE via the
`toAffineAddEquiv` naturality. ~60 lines total.

**Tasks closed (via Jacobian approach)**:
- Task #8 (addX/addY doubling): subsumed (not needed)
- Task #9 (mulByInt_x_add): subsumed (not needed)
- Task #10 (mulByInt_y_add): subsumed (not needed)
- Task #11 (main theorem `zsmul_genericPoint_eq`): ✅ DONE

## Session 3 deliverables

Additional lemmas landed (~150 more lines, axiom-clean):

- `ψ_ff_two_eq`: `ψ_ff 2 = 2·y_gen + a₁·x_gen + a₃`
- `generic_weierstrass`: expanded Weierstrass equation at generic point
- `algebraMap_Poly_KE_eval₂`: scalar tower polynomial evaluation
- `ψ_ff_three_eq`: `ψ_ff 3 = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`
- **`addX_mulByInt_one_mulByInt_one`** (Task #8 x-half closed!): doubling
  x-identity closed via `field_simp + linear_combination` using `generic_weierstrass`
  with coefficient `-(a₁² + 4a₂) - 12x_gen` (= `-b₂ - 12x`).

**Remaining for Task #8**: `addY_mulByInt_one_mulByInt_one` — the y-coord
doubling identity. Requires expanding `ω_ff W 2` via `2·ω = ψc - a₁·φ·ψ - a₃·ψ³`
+ similar linear_combination approach. Estimated ~30-50 lines. The x-coord
approach is the template.

## Session 2 closing state

GenericPointZsmul.lean: 88 → 409 lines (+321). 25 declarations total.
All axiom-clean (no `sorryAx`).

Key remaining mathematical work (for future session(s)):
1. **Task #8 completion**: port `C_Ψ₃_eq` + `generic_equation` chain to give
   `addX_mulByInt_one_mulByInt_one` as a ring identity. ~70 lines.
2. **Task #9**: port `smulX_add` (general addition formula).
3. **Task #10**: port `smulY_add_sub_negY`.
4. **Task #11 completion**: do the full `Int.negInduction` on `n.natAbs`
   using the witness-parametric pieces. Follow mathlib's proof at
   `Auxiliary/DivisionPolynomial.lean:423`.
