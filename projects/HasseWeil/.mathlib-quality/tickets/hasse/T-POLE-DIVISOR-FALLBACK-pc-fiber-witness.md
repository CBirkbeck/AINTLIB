# T-POLE-DIVISOR-FALLBACK: pole-divisor proof of #ker(1−π) = deg(1−π)

**Status**: OPEN — Plan-C fallback (use only if T-II-2-009 stalls)
**Silverman**: III.4.10(c) specialised to `γ = 1 − π`, via direct pole-divisor computation
**Module**: `HasseWeil/Hasse/PoleDivisorFallback.lean` (new file, only if activated)
**Owner**: (held in reserve)
**Estimated lines**: 200-300
**Difficulty**: medium-hard (divisor/valuation bookkeeping)
**Stream**: V

## When to activate

This ticket is dormant unless T-II-2-009 stalls. The reviewer's primary
recommendation is the generic-fibre + translation-bootstrap chain (via
T-II-2-009). The pole-divisor route is bound-specific (only works for
`γ = 1 − π`, not general separable isogenies) but avoids the fibre theorem
entirely.

Activate this ticket only if:
- T-II-2-009 stalls (3+ distinct named-tactic failures on the same
  sub-piece, per PROTOCOL.md).
- AND the narrower "separable isogenies are unramified everywhere" route
  (T-II-2-009 Plan-B alternative) also stalls.

## Statement (target)

```lean
theorem degree_oneSubFrobenius_eq_card_kernel
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).degree =
      Fintype.card (isogOneSub_negFrobenius W hq).kernel
```

This directly delivers `pc_fiber_witness` for `1 − π`.

## Proof sketch (per first reviewer response, 2026-05-08)

Let `γ = 1 − π`. Five concrete lemmas:

1. **Pole at O**: `ord_O(γ.pullback x_gen) = -2`.
   Already shipped via Worker A's `ord_addPullback_x_negFrobenius` chain.
2. **Translation invariance**: `τ_T*(γ.pullback x_gen) = γ.pullback x_gen` for
   all `T ∈ ker γ`.
   Corollary of the kernel-translation action (already shipped) plus the
   addition formula compatibility.
3. **Pole at every kernel point**: `ord_T(γ.pullback x_gen) = -2` for all
   `T ∈ ker γ`. Consequence of (1) + (2) (translation moves the pole at O
   to a pole at T).
4. **No poles off the kernel**: for `P ∉ ker γ`, `0 ≤ ord_P(γ.pullback x_gen)`.
   Since `x` has only a pole at O, `γ.pullback x_gen` can only have poles
   where `γ(P) = O`, i.e., `P ∈ ker γ`.
5. **Pole divisor degree**: `deg(poleDivisor(γ.pullback x_gen)) = 2 · #ker γ`.
   Follows from (3) + (4) by summing pole orders.

Then the standard tower argument:
- `[K(E) : K(γ.pullback x_gen)] = deg(γ.pullback x_gen as map E → P¹) = 2 · #ker γ` (from (5)).
- `[K(E) : K(γ.pullback x_gen)] = [K(E) : γ*K(E)] · [γ*K(E) : K(γ.pullback x_gen)] = deg γ · 2`
  (using `[K(E) : K(x)] = 2` shipped and the tower).
- Equate: `2 · #ker γ = 2 · deg γ`, hence `#ker γ = deg γ`.

## Lemma decomposition (per reviewer)

```lean
lemma pole_order_gamma_x_at_zero :
    ordAt (0 : E.Point) (gamma.pullback x_gen) = -2

lemma gamma_pullback_x_kernel_translation_invariant
    (T : ker gamma) :
    τ_T^* (gamma.pullback x_gen) = gamma.pullback x_gen

lemma pole_order_gamma_x_at_kernel
    (T : ker gamma) :
    ordAt T (gamma.pullback x_gen) = -2

lemma no_poles_gamma_x_off_kernel
    (P : E.Point) (hP : P ∉ ker gamma) :
    0 ≤ ordAt P (gamma.pullback x_gen)

lemma pole_divisor_degree_gamma_x :
    degreePoleDivisor (gamma.pullback x_gen) = 2 * Fintype.card (ker gamma)

lemma degree_gamma_eq_card_kernel :
    gamma.degree = Fintype.card (ker gamma)
```

## Notes

- This is **not** quotient-variety infrastructure. It is divisor/valuation
  bookkeeping plus the compatibility of the genuine pullback with the
  point map.
- The hardest local input — `ord_O(γ*x) = -2` — is already shipped.
- Bound-specific: only delivers `#ker γ = deg γ` for `γ = 1 − π`. Does not
  generalise to arbitrary separable isogenies, so it does NOT discharge
  T-III-4-015 in the general setting; it only discharges
  `pc_fiber_witness` for the specific isogeny the bound consumes.

## Progress log

- 2026-05-13: Worker A's abstract ramification-at-infinity scaffolding shipped on
  branch worker-tensor-isom (commits da201be → 80cca29). New APIs in
  HasseWeil/Curves/RamificationAtInfinity.lean for Worker B to consume:

  * `structure Sinf {L} [Field L] [Algebra k L] (f : L)` — package of
    integral-closure data with all required instances as fields. Axiom-clean.
  * `Sinf.ofIntegralClosure f` — canonical constructor from
    `integralClosure (Polynomial k) (LinfAt f)` under the natural
    finite-separability + transcendence hypotheses.
  * `finrank_eq_sum_ramificationIdx_mul_inertiaDeg` — abstract identity
    `Σ e(P)·f(P) = [LinfAt f : k(f)]` via Mathlib's `sum_ramification_inertia`.
  * `Sinf.ordAt`, `Sinf.kappa`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`,
    `Sinf.inertiaDeg_eq_finrank_kappa` — bridges 2 and 3.
  * `quotientXAlgEquiv` + `finrank_residue_eq_finrank_k` — convert
    `Polynomial k ⧸ xIdeal ≃ k` finrank, so inertia degree → [κ(P):k].
  * `finrank_eq_weighted_poleDegree_of_nonconstant data` — closing
    abstract corollary in `inertiaDeg` form.

  Worker B's specialisation to γ\*x_gen on E:
    1. Construct `data := Sinf.ofIntegralClosure (γ\*x_gen)` (needs the
       three hypotheses: Fact(Transcendental k (γ\*x_gen)⁻¹),
       Module.Finite, Algebra.IsSeparable on K(E)/k(γ\*x_gen)).
    2. Apply `finrank_eq_weighted_poleDegree_of_nonconstant` to obtain
       the abstract identity.
    3. Identify the primesOverFinset xIdeal data.carrier with ker γ via
       the existing smoothPoint_fiber_eq_primesOver-style infrastructure
       in NormValuation.lean.
    4. Apply pole_order_gamma_x_at_kernel + no_poles_gamma_x_off_kernel
       (Lemmas 1-4 already itemised above) to compute the sum.

