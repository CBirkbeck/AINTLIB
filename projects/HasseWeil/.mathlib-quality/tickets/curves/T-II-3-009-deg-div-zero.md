# T-II-3-009: deg(div(f)) = 0

**Status**: CHECKED-OUT
**Silverman**: II.3.1(b)
**Module**: `HasseWeil/Curves/ProjectiveDivisor.lean` (extends T-II-3-001b)
**Owner**: worker-K
**Checked out at**: 2026-04-20T18:00Z
**Estimated lines**: 50 → **revised 200–300** (see 2026-04-20 progress note)
**Difficulty**: medium → **hard** (see 2026-04-20 progress note)
**Stream**: A

## Depends on
- T-II-3-005 (div(f))
- T-II-2-006 (deg-1 iso) OR T-II-2-008 (sum formula)

## Blocks
- T-II-3-010 (exact sequence)

## Statement (Silverman II.3.1(b))
For any nonzero `f ∈ K̄(C)*`,

```
deg(div(f)) = 0.
```

## Acceptance criteria (revised 2026-04-20)

**The original statement `(divisorOf C f).degree = 0` is mathematically
incorrect for this project's framework** (see progress note 2026-04-20).
The corrected statement uses the projective divisor from T-II-3-001b and
requires `[IsAlgClosed F]`:

```lean
namespace HasseWeil.Curves

/-- The degree of a principal projective divisor on a smooth plane curve
over an algebraically closed field is zero.
Reference: Silverman II.3.1(b). -/
theorem SmoothPlaneCurve.projectiveDivisorOf_degree_zero [IsAlgClosed F]
    (C : SmoothPlaneCurve F) {f : C.FunctionField} (hf : f ≠ 0) :
    (C.projectiveDivisorOf f).degree = 0

end HasseWeil.Curves
```

## Notes
- Silverman's slick proof uses a map `f : C → ℙ¹` and the formula
  `deg ∘ f* = (deg f) · deg`. This requires T-II-2-006 (deg-1 iso),
  T-II-3-011 (pullback), T-II-3-012 (pullback properties) — none DONE.
- The **norm-based route** is more direct with our existing infrastructure
  (ordAtInfty via `RatFunc.intDegree` of the algebra norm):
  1. For `g ∈ F(x) = RatFunc F` with F alg closed:
     `intDegree(g) = Σ_{a ∈ F} v_a(g)` (purely algebraic, via
     `Polynomial.roots.card = natDegree`).
  2. For `f ∈ F(C)*` and `a ∈ F`:
     `v_a(N(f)) = Σ_{P : P.x = a} ord_P(f)` — requires that primes of
     `F[C]` above `(x−a)` correspond to smooth F-rational points with
     `P.x = a` (holds for F alg closed + `IsIntegrallyClosed F[C]`).
  3. Combine: `Σ_P ord_P(f) = Σ_a v_a(N(f)) = intDegree(N(f)) =
     -ordAtInfty(f)` ⇒ projective degree = 0.

## Why the original statement is wrong

Over non-algebraically-closed F, the affine-only divisor degree of a
principal divisor need not be 0:

- **∞ missing**: `C: y² = x³ − x` over ℚ, `f = x`: `ord_{(0,0)}(x) = 2`,
  all other affine orders 0. Affine degree = 2. The balancing `−2` lives
  at infinity.
- **Non-F-rational closed points missing**: `C: y² = x³ − 2` over ℚ,
  `f = x − 2`: no ℚ-rational `P` has `P.x = 2` (since `y² = 6` has no
  ℚ root), so affine degree = 0. But `ordAtInfty(x−2) = −2`, balanced by
  two non-F-rational closed points that aren't tracked in
  `C.SmoothPoint` (which is F-rational by construction).

## Progress log

- **2026-04-20T18:00Z** [worker-K] checkout. Audit of scope: ticket's
  original statement `(divisorOf C f).degree = 0` is mathematically false.
  Correct form uses `projectiveDivisorOf` (from T-II-3-001b, just
  delivered) and assumes `[IsAlgClosed F]`. Plan is norm-based (avoids
  the `f → morphism → ℙ¹` framework which is not built). Estimated
  200–300 lines split across three helper lemmas.

- **2026-04-20T18:30Z** [worker-K] Delivered **Helper A** (F(x) product
  formula, axiom-clean) in `HasseWeil/Curves/ProjectiveDivisor.lean`:
  - `HasseWeil.Curves.Polynomial.sum_rootMultiplicity_eq_natDegree`
    `[IsAlgClosed F] [DecidableEq F] (p : Polynomial F)`:
    `∑ a ∈ p.roots.toFinset, p.rootMultiplicity a = p.natDegree`.
    Proof via `IsAlgClosed.card_roots_eq_natDegree` +
    `Multiset.toFinset_sum_count_eq` + `Polynomial.count_roots`.
  - `HasseWeil.Curves.RatFunc.intDegree_eq_sum_sub_of_isAlgClosed`
    `[IsAlgClosed F] [DecidableEq F] (g : RatFunc F)`:
    `(intDegree g : ℤ) = (Σ a ∈ num.roots.toFinset, mult a num)
                       − (Σ a ∈ denom.roots.toFinset, mult a denom)`.

  Still to do (Helper B + main combination):
  - **Helper B**: for `f ∈ F(C)*` and `a ∈ F`:
    `rootMultiplicity a (num (N f)) − rootMultiplicity a (denom (N f))
     = Σ_{P : P.x = a, smooth} ord_P(f)` (for F alg closed).
  - **Main**: combine Helpers A + B to get
    `Σ_{P affine smooth} ord_P(f) = intDegree(N(f)) = −ordAtInfty(f)`,
    hence `(projectiveDivisorOf f).degree = 0`.

- **2026-04-20T19:00Z** [worker-K] **Helper B investigation — deferred**.
  Attempted to formalize Helper B via `Ideal.relNorm` machinery in mathlib
  (`Mathlib.RingTheory.Ideal.Norm.RelNorm`). Path surveyed:
  1. Add `[IsIntegrallyClosed C.CoordinateRing]` hypothesis → get
     `IsDedekindDomain C.CoordinateRing` (exists in
     `HasseWeil/Curves/IntegralClosure.lean`, conditional on same).
  2. For `u ∈ F[C]` nonzero, `I := span {u}` factors as `Π_P P^{m_P}` in
     the Dedekind domain `F[C]` with `m_P = multiplicity P I = ord_P(u)`.
  3. `Ideal.relNorm F[X] I = span {Algebra.intNorm F[X] F[C] u} = (N(u))`
     (from `Ideal.relNorm_singleton`).
  4. By `map_mul (Ideal.relNorm F[X])`:
     `(N(u)) = relNorm I = Π_P (relNorm P)^{m_P}`.
  5. For maximal P of F[C] lying over `p = (X − a)` of F[X] under
     `[IsAlgClosed F]`, `F[C]/P` is a finite F-algebra field, hence
     isomorphic to F (alg closed). So `inertiaDeg p P = 1` and by
     `Ideal.relNorm_eq_pow_of_isMaximal` (which requires
     `[PerfectField (FractionRing F[X])]`, satisfied under
     `[IsAlgClosed F]`): `relNorm P = p^1 = p = (X − a)`.
  6. Comparing factorizations in F[X] (PID/UFD):
     `N(u) = c · Π_P (X − a_P)^{m_P}` where `a_P = P.x`, and grouping
     gives `rootMultiplicity a (N(u)) = Σ_{P: a_P = a} m_P =
     Σ_{P: P.x = a} ord_P(u)`.

  **Why not delivered**: the chain above is mathematically correct but
  formalizing each step needs:
  - Bridge `C.SmoothPoint` (F-rational, affine) ↔ maximal ideals of F[C]
    lying over `(X − a)` under `[IsAlgClosed F]`. This is a missing
    correspondence: `SmoothPoint` is a concrete structure with `x, y : F`
    while maximal ideals are abstract. The bridge requires either a
    `SmoothPointToMaximalIdeal` equivalence or direct rewriting of ord_P
    via Ideal.spanNorm in terms of the `P` constructor.
  - Per-P bridge from `ord_P u` (project's `pointValuation`-based integer
    valuation) to `multiplicity P (span {u})` in F[C] (mathlib's Dedekind
    factorization).
  - `inertiaDeg (X−a) P = 1` under `[IsAlgClosed F]` (needs a statement
    that `F[C]/P ≃ F`; likely needs a non-trivial argument about
    finitely-generated F-algebras).
  - `IsIntegrallyClosed C.CoordinateRing` (currently conditional —
    unconditional under `[IsElliptic]` tracked as separate work).

  Estimated **150–200 lines** of additional scaffolding required to
  close Helper B. Realistic as its own follow-up session; not achievable
  cleanly in this one without violating the `no-sorry` rule. Ticket
  remains CHECKED-OUT; Helper A (F(x) product formula) stands alone as
  reusable.

- **2026-04-20T19:45Z** [worker-K] Delivered **Helper B bridge lemmas** in
  new file `HasseWeil/Curves/NormValuation.lean` (~110 lines, axiom-clean):

  - `SmoothPlaneCurve.quotientMaximalIdealAtEquiv` — the F-algebra iso
    `F[C] ⧸ maximalIdealAt P ≃ₐ[F] F`, obtained from mathlib's
    `quotientXYIdealEquiv`.
  - `SmoothPlaneCurve.finrank_quotientMaximalIdealAt` —
    `Module.finrank F (F[C] ⧸ maximalIdealAt P) = 1`. This is the
    "residue degree = 1" fact under the smoothness of `P` (independently
    of `[IsAlgClosed F]`).
  - `SmoothPlaneCurve.xClass_mem_maximalIdealAt` — the structural fact
    `XClass C.toAffine P.x ∈ maximalIdealAt P`.
  - `SmoothPlaneCurve.algebraMap_X_sub_C_mem_maximalIdealAt` —
    `algebraMap F[X] F[C] (X − P.x) ∈ maximalIdealAt P`.
  - `SmoothPlaneCurve.maximalIdealAt_liesOver` — **the LiesOver bridge**:
    `(maximalIdealAt P).LiesOver (Ideal.span {X − P.x})`. Proof via
    `Polynomial.quotientSpanXSubCAlgEquiv` for the maximality of
    `span {X − P.x}` in `F[X]`, then `IsMaximal.eq_of_le`.

  These five lemmas are the first concrete block of Helper B's scaffold.
  Remaining for full Helper B:
  - Under `[IsAlgClosed F]`, every maximal ideal of `F[C]` lying over
    `(X − a)` is `maximalIdealAt P` for some smooth `P` with `P.x = a`
    (surjective direction of the SmoothPoint ↔ max-ideal correspondence).
  - `ord_P u` ↔ `multiplicity (maximalIdealAt P) (span {u})` bridge
    (connects our `ord_P : WithTop ℤ` to mathlib's Dedekind factorization
    multiplicities).
  - Put together via `Ideal.relNorm` monoid-hom + UFM factorization.

  `finrank_quotientMaximalIdealAt = 1` combined with
  `maximalIdealAt_liesOver` is exactly the statement that the
  inertia-degree of `maximalIdealAt P` over `(X − P.x)` is 1
  (definitionally, via `inertiaDeg_algebraMap`), modulo an
  `IsAlgClosed` - free proof — good news, we don't need
  `[IsAlgClosed F]` for this piece.

- **2026-04-21T10:30Z** [worker-K] Attempted `inertiaDeg_maximalIdealAt P = 1`
  via `Algebra.finrank_eq_of_equiv_equiv` with
  `Polynomial.quotientSpanXSubCAlgEquiv P.x` as the base-ring iso, going
  from `Module.finrank F (F[C]/M) = 1` (proved) to
  `Module.finrank (F[X]/(X-P.x)) (F[C]/M) = 1`. The compatibility
  condition (diagram commutativity) reduced to:
  `algebraMap F (F[C]/M) (p.eval P.x) = algebraMap (F[X]/(X-P.x)) (F[C]/M)
   (Quotient.mk _ p)` for any `p ∈ F[X]`. Mathematically this holds
  because the difference `algebraMap F[X] F[C] (p - C(p.eval P.x))` lies
  in `maximalIdealAt P` (divisible by `X - P.x`), but formalizing it hit
  definitional-unfolding issues with the `Ideal.Quotient` algebra map
  coercion chain. Reverted; the bridge lemmas stand. A cleaner path may
  go via `Module.finrank_mul_finrank` tower formula with
  `F ≤ F[X]/(X-P.x) ≤ F[C]/M` once appropriate `IsScalarTower` instance
  is established.

- **2026-04-21T10:45Z** [worker-K] Tried tower approach via
  `Module.finrank_mul_finrank`. Ran into module-structure diamond: the
  `F[X]/(X-P.x)`-module instance on `F[C]/M` via `Ideal.Quotient.algebraQuotientOfLEComap`
  gives `Algebra.toModule`, but `Module.Free.of_divisionRing` produces a
  different module structure (via the `Field → DivisionRing → Semiring`
  synthesis path). Two module instances on the same pair of types don't
  unify definitionally. Reverted the inertiaDeg attempt again; kept the
  useful by-product `finrank_quotientSpanXSubC` (rank of
  `F[X]⧸(X−a)` over `F` is 1).

- **2026-04-21T11:00Z** [worker-K] Delivered
  `algebraMap_quotient_maximalIdealAt_surjective` (axiom-clean, ~45
  lines): the structure map `F[X]⧸(X−P.x) → F[C]⧸maximalIdealAt P` is
  surjective. Proof via the LiesOver bridge + `Ideal.quotientMap_mk` +
  `IsScalarTower F (Polynomial F) C.CoordinateRing`.

- **2026-04-21T11:20Z** [worker-K] **Closed inertiaDeg = 1** (axiom-clean):
  `inertiaDeg_maximalIdealAt P : inertiaDeg (X − P.x) (maximalIdealAt P) = 1`.

  Proof structure:
  - `Ideal.inertiaDeg_algebraMap` reduces to `finrank (F[X]⧸(X−P.x))
    (F[C]⧸M) = 1`.
  - Upper bound via `finrank_le_one`: v = 1, every w = c • 1 by
    `algebraMap_quotient_maximalIdealAt_surjective`.
  - Lower bound via `Module.finrank_pos` (base is a field).

  Works over arbitrary F — no `[IsAlgClosed F]` required.

- **2026-04-21T15:00Z** [worker-K] **Fiber bijection CLOSED** (axiom-clean):
  - `maximalIdealAt_liesOver_of_eq_x` — for P with P.x = a,
    `(maximalIdealAt P).LiesOver (Ideal.span {X − C a})`.
  - `smoothPoint_fiber_eq_primesOver` — under IsAlgClosed + IsElliptic,
    `maximalIdealAt '' {P | P.x = a} = {M | M.IsMaximal ∧ M.LiesOver (X−a)}`.
    This is the key bijection used in the final sum rearrangement:
    `Σ_{P : P.x = a} ord_P(u) = Σ_{M over (X−a)} multiplicity_M(u)`.

  **18 Helper B bridge lemmas total, all axiom-clean.** `NormValuation.lean`
  now ~550 lines.

- **2026-04-21T14:45Z** [worker-K] **Full SmoothPoint ↔ MaxSpec bijection
  + range lemma CLOSED** (axiom-clean). Added:
  - `maximalIdealAt_injective` — no hypotheses.
  - `smoothPointEquivMaxIdeal` (`Equiv`) — under IsAlgClosed + IsElliptic.
  - `smoothPointEquivMaxIdeal_apply` (`@[simp]`).
  - `maximalIdealAt_range` — the range equals the full MaxSpec.

  **16 Helper B bridge lemmas total, all axiom-clean.** `NormValuation.lean`
  now ~500 lines.

- **2026-04-21T14:15Z** [worker-K] **SmoothPoint surjection CLOSED**
  (axiom-clean). Two new theorems delivered in `NormValuation.lean`:

  - `equation_of_coordinates`: the coordinates `(a, b)` extracted from any
    maximal ideal `M` via `exists_coordinates_of_isMaximal` satisfy the
    Weierstrass equation `W(a, b) = 0` in F. Proof: apply
    `AdjoinRoot.mk_self` + project via `Quotient.mk M` + ring-hom-commute
    using `ha, hb` substitutions + reduce to a polynomial identity in
    `F[X][Y]` closed by `Polynomial.C_add/C_mul` + `ring1`.

  - `exists_smoothPoint_of_isMaximal`: under `[IsAlgClosed F]` +
    `[C.toAffine.IsElliptic]`, every maximal ideal of F[C] is
    `maximalIdealAt P` for some `P : C.SmoothPoint`. Proof chain:
    `exists_coordinates_of_isMaximal` → `equation_of_coordinates` →
    `equation_iff_nonsingular` (IsElliptic) → construct smooth point →
    show `maximalIdealAt P ⊆ M` via `XClass a, YClass (C b) ∈ M` (using
    `ha, hb` and `algebraMap` cancellation) → `IsMaximal.eq_of_le` for
    equality.

  **13 Helper B bridge lemmas now delivered, all axiom-clean.** The
  SmoothPoint surjection was the main remaining obstruction.

- **2026-04-21T13:30Z** [worker-K] Attempted the **Equation step** via
  `Polynomial.ringHom_ext'` + `eval₂_eval₂RingHom_apply` +
  `map_mapRingHom_evalEval`. The approach is mathematically correct — see
  the detailed strategy comment — but the `Polynomial.ringHom_ext'`
  invocation required matching the precise expected form (F-constants,
  embedded F[X] indeterminate via `Polynomial.C Polynomial.X`, then outer
  Y) and hit an unfilled `sorry` due to the way
  `Polynomial.eval₂_C/eval₂_X/algebraMap_apply` interact with the
  `Ideal.Quotient.mk M ∘ algebraMap (Polynomial (Polynomial F))`
  composition.

  Alternative approach likely cleaner: work directly with `equation_iff`
  (instead of `evalEval`), use the algebraic identity
  `mk W.polynomial = 0 ⇒ (mk Y)² + a₁ (mk X)(mk Y) + a₃ (mk Y) =
  (mk X)³ + a₂(mk X)² + a₄(mk X) + a₆` in F[C], project via
  `Quotient.mk M`, substitute `ha, hb`, and pull out `algebraMap F` via
  `map_add/map_mul` before applying injectivity. Avoids the
  polynomial-ring-hom-ext detour.

  Reverted to clean state. Follow-up session should take the
  `equation_iff` route.

- **2026-04-21T12:00Z** [worker-K] **Zariski's lemma path** (axiom-clean):
  Three new lemmas pushing toward SmoothPoint ↔ max-ideal surjection:

  - `coordinateRing_finiteType : Algebra.FiniteType F C.CoordinateRing`
    via `Algebra.FiniteType.trans` (F → F[X] → F[C]).
  - `module_finite_quotient_of_maximal` — under `[M.IsMaximal]`,
    `Module.Finite F (F[C]⧸M)` via
    `finite_of_finite_type_of_isJacobsonRing` (Zariski / Stacks 0CY7).
  - `algebraMap_bijective_quotient_of_maximal` — under `[IsAlgClosed F]`,
    `algebraMap F (F[C]⧸M)` is bijective, via
    `IsAlgClosed.algebraMap_bijective_of_isIntegral` on the finite module.
  - `exists_coordinates_of_isMaximal` — for any maximal M, there exist
    `a, b ∈ F` with `algebraMap a = Quotient.mk M (mk (C X))` and
    `algebraMap b = Quotient.mk M (mk Y)`. (Surjectivity applied to the
    classes of X and Y.)

  **Eleven Helper B bridge lemmas now available, all axiom-clean.**

  Remaining for full Helper B (under `[IsAlgClosed F]` + `[IsElliptic C]`):
  - `exists_smoothPoint_of_isMaximal` — extend
    `exists_coordinates_of_isMaximal` by showing:
    (i) `W(a, b) = 0` in F (using `mk W = 0` in F[C], the ring hom
        `F[X][Y] → F[C] → F[C]/M` sends W to 0, transport through the
        bijective algebraMap F ≃ F[C]/M gives `W.polynomial.evalEval a b = 0`
        in F);
    (ii) `equation_iff_nonsingular` under `[IsElliptic]` promotes (i) to
         smoothness;
    (iii) `maximalIdealAt ⟨a, b, h⟩ ⊆ M` from `XClass a, YClass b ∈ M`
          (by construction of a, b), then `IsMaximal.eq_of_le` closes equality.
  - `ord_P u` ↔ `multiplicity (maximalIdealAt P) (span {u})` bridge via
    `IsDedekindDomain.HeightOneSpectrum.intValuation` or `UniqueFactorizationMonoid.normalizedFactors.count`.
  - Combine: `N(u) = relNorm (u) = Π (relNorm (maximalIdealAt P))^{m_P}`
    via `map_mul Ideal.relNorm` + inertiaDeg = 1 to compute
    `relNorm (maximalIdealAt P) = span {X − P.x}`, then compare
    factorizations in PID F[X].

  The main obstruction to closing (i) is threading
  `algebraMap F (F[C]/M)` through `Polynomial.evalEval` — mathlib has
  `eval₂_eval₂RingHom_apply` (via `mapRingHom`) but the coercion chain
  is fiddly.
