# T-HASSE-CLOSE-C: Dual isogeny existence → HOLE E (Route A)

**Status**: OPEN
**Silverman**: III.6.1 (dual isogeny existence + uniqueness), cascading through
  III.4.15 (kernel theory), III.4.16 (factorization), III.4.17 (quotient curve)
**Module**: `HasseWeil/DualIsogeny.lean` (line 134 sorry) + supporting
  infrastructure in `HasseWeil/EC/IsogenyFactor.lean`,
  `HasseWeil/EC/IsogenyKernel.lean`, plus new `HasseWeil/EC/QuotientCurve.lean`
**Owner**: [TO BE ASSIGNED]
**Estimated lines**: 1500–2000 (depends on route chosen — see Strategy)
**Difficulty**: hard (CRITICAL keystone — the classical route to HOLE E)
**Stream**: C (III.4 kernel theory + III.6 dual)

## Goal

Close **T-III-6-001** (dual isogeny existence + uniqueness), which triggers
the ✅cc (content-complete, cascade) family:
- T-III-6-003 (`φ̂ ∘ φ = [deg φ]`)
- T-III-6-005 (`(φ+ψ)^ = φ̂ + ψ̂`)
- T-III-6-006 (`[m]^ = [m]`)
- T-III-6-007 (`deg φ̂ = deg φ`)
- T-III-6-008 (`(φ̂)^ = φ`)

These in turn enable **T-III-6-009** (degree is a positive-definite quadratic
form), which discharges **HOLE E** in `Hasse/Unconditional.lean`.

This is the **classical route** (parallel to Route B = T-HASSE-CLOSE-B via
BRIDGE-001). Whichever ticket lands first closes HOLE E.

## Depends on
- T-III-4-015 (separable ⇒ #ker = deg — PARTIAL, witness form by worker-A)
- T-III-4-016 (factorization — PARTIAL, witness form by worker-A)
- T-III-4-017 (quotient curve — OPEN ★)
- T-II-2-016 (factor as sep ∘ Frob^e — OPEN ★)

## Blocks
- **HOLE E** in `Hasse/Unconditional.lean` via Route A
- All of III.6 except III.6.2 (which uses Pic⁰ route)
- The classical proof architecture of Silverman III.6

## Statement

```lean
namespace HasseWeil

/-- Existence and uniqueness of the dual isogeny.
    Reference: Silverman III.6.1(a). -/
theorem exists_dual (α : Isogeny E E) :
    ∃! β : Isogeny E E, IsDualOf E β α

end HasseWeil
```

The current `HasseWeil/DualIsogeny.lean:134` has this as a `sorry`.

## Strategy

**Two high-level approaches**, pick one:

### Approach A — via III.4.15/16/17 (Silverman's construction)

This is the most faithful to the Silverman text. It needs:

1. **T-III-4-015 upgrade** (`sep ⇒ #ker = deg` unconditional): currently PARTIAL
   in witness form. For separable α, this says the kernel has cardinality deg(α).
2. **T-III-4-016 upgrade** (factorization theorem): if φ : E₁ → E₂, ψ : E₁ → E₃
   are isogenies with `ker φ ⊆ ker ψ`, then there exists unique λ : E₂ → E₃ with
   `ψ = λ ∘ φ`. Currently PARTIAL (witness form).
3. **T-III-4-017 fresh** (quotient curve): for a finite subgroup G ⊆ E[m], the
   quotient E/G exists as an elliptic curve and projects to E₂ such that
   `ker (E → E/G) = G`. ~500–800 lines; needs GIT-like construction via
   coinvariant ring or function-field-fixed-subfield approach.
4. **Dual construction**:
   - Case separable: `ker φ ⊆ ker [deg φ]`, so by III.4.16 there's unique
     `ψ : E₂ → E` with `ψ ∘ φ = [deg φ]`. Set `φ̂ := ψ`.
   - Case inseparable: decompose `φ = φ_sep ∘ Frob^e` (T-II-2-016), use
     separable case for `φ_sep`, and Verschiebung for `Frob^e`.

**Estimated scope**: ~1500–2000 lines total for all four pieces.

### Approach B — via Pic⁰ (T-III-3-004)

If Pic⁰(E) ≅ E (Silverman III.3.4) is available, the dual is defined via
pullback/pushforward on divisor classes. Currently **T-III-3-004 is OPEN ★**,
so this route is also a 1000+ line infrastructure build.

### Approach C — "finite group-theoretic" shortcut for characteristic 0

In char(F) = 0, every isogeny is separable, simplifying the dual to a
quotient-curve-only argument. For the Hasse bound over F_q (char p > 0), this
does NOT apply — Frobenius is purely inseparable. So this approach cannot
replace the full dual machinery; it only simplifies a subcase.

**Recommended: Approach A** — it's the classical proof and advances
general-purpose Silverman API (user directive 2026-04-18: "no shortcuts, full
Silverman API").

## Existing infrastructure

Already shipped (usable as inputs):

- `HasseWeil/DualIsogeny.lean`:
  - `IsDualOf` predicate
  - `exists_dual_of_construction` — witness-parametric
  - `exists_dual_of_constructor` — cascade triggering from a per-α constructor
  - `exists_dual_iff_constructor` — bi-directional
  - `isogDual_comp_self_of_witness`, `self_comp_isogDual_of_witness`,
    `degree_dual_of_witness`
  - `dual_add_of_trace_witnesses`, `dual_add_of_sum_witnesses` (T-III-6-005)
- `HasseWeil/EC/IsogenyFactor.lean`:
  - `factor_through_isogeny_witness` (T-III-4-016 witness form)
  - `factor_unique_of_surjective`
  - `factor_through_isogeny_existsUnique_witness`
- `HasseWeil/EC/IsogenyKernel.lean`:
  - `Isogeny.fiber_witness_of_ker_card_eq_sepDegree` (reduces T-III-4-015-style
    ker=sepDeg identity to ker card witness)
- `HasseWeil/DegreeQuadraticForm.lean`:
  - `degree_quadratic_closed`, `isogSmulSub_degree_quadratic_closed`
    (T-III-6-009 witness forms)

## Acceptance criteria

```lean
#print axioms HasseWeil.exists_dual
-- reports only [propext, Classical.choice, Quot.sound]
```

Once landed, the following ✅cc tickets close automatically (since their
content-complete witness forms already exist):
- T-III-6-003, T-III-6-005, T-III-6-006, T-III-6-007, T-III-6-008
- T-III-6-009 follows via `degree_quadratic_closed` instantiated with the dual
- HOLE E auto-discharges in `Hasse/Unconditional.lean`

## Files to create/modify

- `HasseWeil/EC/QuotientCurve.lean` (NEW, ~500-800 lines) — Silverman III.4.17
- `HasseWeil/EC/IsogenyFactor.lean` — upgrade witness form to unconditional
- `HasseWeil/EC/IsogenyKernel.lean` — sep + finite-kernel → #ker = deg
- `HasseWeil/DualIsogeny.lean` — close `exists_dual` via quotient-curve
  construction + inseparable decomposition
- `HasseWeil/DegreeQuadraticForm.lean` — remove the sorry at line 145 via the
  cascade
- `HasseWeil/Hasse/Unconditional.lean` — discharge HOLE E case

## Risks / gotchas

- **III.4.17 quotient curve** is the biggest sub-piece — genuinely hard, no
  mathlib infrastructure. Needs either:
  - Function-field fixed-subfield route: `F(E/G) = F(E)^G` and show this is a
    field of transcendence degree 1 admitting an elliptic-curve equation
  - GIT-like invariant-theory route: `(F[E])^G` as a finite subalgebra,
    identified with an elliptic curve coordinate ring
- **Inseparable case** requires T-II-2-016 (factor φ = φ_sep ∘ Frob^e), which
  is OPEN. May need to construct this infrastructure first.
- `IsDualOf` might need to be generalized from `E → E` to `E₁ → E₂` if the
  general Silverman III.6.1 statement is required. Check existing scope.
- 1500–2000 lines is a significant infrastructure build — genuinely multi-
  session work. Consider splitting into sub-tickets:
  - T-HASSE-CLOSE-C-1: quotient-curve construction (III.4.17)
  - T-HASSE-CLOSE-C-2: factorization unconditional (III.4.16)
  - T-HASSE-CLOSE-C-3: dual construction via C-1 + C-2

## Comparison with Route B

| | Route A (this ticket) | Route B (T-HASSE-CLOSE-B) |
|---|---|---|
| Path | III.4.15/16/17 → dual → III.6.9 | BRIDGE-001/003 → III.5.6 → III.6.9 |
| Lines | ~1500–2000 | ~500–800 |
| Infrastructure reuse | Builds III.4 general API | Builds formal-group bridge |
| Mathematics | Kernel theory, quotient curves | Formal groups, power series |
| Stream | C | D / E |

Both routes are legitimate Silverman content. Whichever lands first closes
HOLE E. Running both in parallel is safest — if one gets stuck, the other
independently completes the proof.

## Progress log

- **2026-04-27** (Pivot): Status changed from PARTIAL → **BLOCKED-ON-VERSCHIEBUNG**.
  Investigation discovered that **universal `exists_dual` is structurally
  unprovable** in the current `Isogeny` representation. The independent
  `pullback`/`toAddMonoidHom` fields admit non-unique duals at the record
  level: from `IsDualOf β α` for both β₁ and β₂, `δ := β₁.hom - β₂.hom`
  satisfies `δ ∘ α = 0` AND `α ∘ δ = 0` — the factored map
  `δ̄ : E.Point/im α → ker α` can be nonzero (concrete witness: α = [2]
  over a curve with nontrivial 2-torsion gives `coker[2]` and `ker[2]`
  with the same cardinality). Documented permanently in
  `HasseWeil/DualIsogeny/RouteA.lean` docstring.

  **Pivot strategy**: drop the universal goal; deliver only the
  Frobenius-specific Verschiebung needed by the Hasse-Weil cascade. For
  α = π, both Route A blockers vanish: `π.toAddMonoidHom = AddMonoidHom.id`
  (surjectivity is `Function.surjective_id`) and the universal pullback
  commute is shipped via `frobeniusIsog_pullback_universal_commute`
  (`HasseWeil/Frobenius.lean`).

  **Tier 1 shipped this session**: `hole_e_closer_via_frobenius_dual_witness`
  in `HasseWeil/Hasse/HoleE.lean` — axiom-clean, takes
  `verschiebung : Isogeny W.toAffine W.toAffine` plus
  `IsDualOf verschiebung (frobeniusIsog W)` directly (no detour through
  universal `isogDual`). When the new sub-ticket
  **T-HASSE-CLOSE-C-VERSCHIEBUNG-FROBENIUS** delivers `verschiebungIsog W`
  + `verschiebungIsog_isDualOf_frobenius W`, this closer is the canonical
  HOLE E entry point and the cascade closes axiom-clean.

  **New sub-ticket**:
  `T-HASSE-CLOSE-C-VERSCHIEBUNG-FROBENIUS.md` (Path B — division
  polynomials, ~600-800 LOC). This is the actual closure work; parent
  ticket reduces to "ship the wire-up + Verschiebung sub-ticket".

  **End of session: Sub-ticket sessions 2, 4, 5, 6 all shipped axiom-clean
  witness-parametric (~575 LOC total)** in five new files:
  - `HasseWeil/Frobenius.lean` (additions): `frobeniusIsog_pullback_*`
    image lemmas + `mulByInt_pullback_pow_witness_iff_*` bridge
  - `HasseWeil/Verschiebung/FieldTower.lean`: field-tower setup with
    `[K(E) : Im(π*)] = q`, `[K(E) : Im([q]*)] = q²`, and the
    inclusion-as-witness theorem
  - `HasseWeil/Verschiebung/Construction.lean`: V* pullback via
    `frobeniusIsog_rangeEquiv.symm ∘ mulByInt_q_pullback_restricted`
  - `HasseWeil/Verschiebung/IsDual.lean`: full Isogeny + IsDualOf
    (uses `frobeniusIsog_pullback_universal_commute` for the
    `π ∘ V = [q]` direction)
  - `HasseWeil/Verschiebung/Cascade.lean`: full witness-parametric
    HOLE E closer via the Verschiebung witness

  **Single residual mathematical input** (Session 3): the inclusion
  `Im([q]*) ⊆ Im(π*) = K(E)^q`. Three approaches identified, none
  closed in this session:

  (i) Direct generator computation — fails because `Φ_q ∉ F_q[X^q]`
      generically (verified for q=3 char 3); q-th root must mix in y_gen.
  (ii) Field-tower degree count — doesn't pin down inclusion without
       additional structure (inseparable lattice).
  (iii) Frobenius factorization (T-II-2-016) at the function-field level
        via mathlib's `IsPurelyInseparable` machinery — ~200 LOC focused
        work, the cleanest path. Recommended for next session.

- **2026-04-24** (Session): `HasseWeil/DualIsogeny/RouteA.lean` scaffold
  complete and axiom-clean (11 theorems, `[propext, Classical.choice,
  Quot.sound]` only). Covers all of Steps 1–5 of the classical
  III.4.15/16/17 → III.6.1 pipeline as witness-parametric theorems.
  Commits landed this session:
  - **Scaffold + Lagrange + self-comp + scalar-commute closure** (f395765,
    f087a2c): the three sorries in the initial scaffold were closed via
    `AddSubgroup.addOrderOf_dvd_natCard` (Lagrange), Isogeny struct
    extensionality (scalar commute at Isogeny level), and
    `factor_unique_of_surjective` (second-composition closure).
  - **C-2 witness reduction** (18c9754): the `h_n_comm` witness in
    `self_comp_factor_of_factor` etc. weakened from full Isogeny-level
    commute to **pullback-level commute only**. The hom-level commute
    (`α.toAddMonoidHom ∘ [n].toAddMonoidHom = [n].toAddMonoidHom ∘
    α.toAddMonoidHom`) is shipped unconditionally via `map_zsmul` as
    `mulByInt_toAddMonoidHom_comm`. Also added
    `exists_dual_of_route_A_raw_witness` which takes the factor data
    `(lamPb, h_pb, lamHom, h_hom)` directly via
    `factor_through_isogeny_witness` instead of a pre-assembled `lam`.
  - **Lagrange chain for separable α** (90fca10): added
    `kernel_subset_kernel_mulByInt_deg` (specialization at `n = α.degree`)
    and `kernel_subset_kernel_mulByInt_deg_of_separable_witness` (one-shot
    chain from `IsSeparable + finiteDimensional + fiber witness` to
    `α.kernel ≤ (mulByInt E α.degree).kernel`).

  **Current upstream witnesses required by Route A** (to discharge
  `exists_dual` unconditionally via `exists_dual_of_route_A_raw_witness`):
  1. `lamPb : E.FunctionField →ₐ[F] E.FunctionField` with factoring
     identity — from **T-III-4-015** (Galois fixed-field
     `K(E)^{ker α} = α*K(E)`) + **T-III-4-016** (factorization
     unconditional; sub-ticket C-2). These are CLOSED in witness form;
     the unconditional discharge is the remaining work.
  2. `lamHom : E.Point →+ E.Point` with factoring identity — from
     **T-II-2-001** smooth-curve duality.
  3. `Function.Surjective α.toAddMonoidHom` — from **T-II-2-002**.
     ⚠ Structural concern: `α.toAddMonoidHom` is on F-rational points,
     not F̄-rational points. Over F_q with separable α of degree > 1,
     this is **false** on F_q-points. Route A's uniqueness argument as
     written requires this surjectivity; a refinement would either
     re-target Isogeny's hom field to F̄-points or find an alternative
     uniqueness argument (e.g., using both left+right composition).
  4. `α.pullback.comp (mulByInt E α.degree).pullback =
       (mulByInt E α.degree).pullback.comp α.pullback` — the **pullback
     part** of T-III-4-020 (scalar commutativity). The hom part is
     automatic (shipped as `mulByInt_toAddMonoidHom_comm`).

  **Session outcome**: Route A scaffold now in its final shape; all
  content that can be shipped without additional infrastructure is
  axiom-clean. Further progress on `exists_dual` (Route A) blocked on
  the four upstream witnesses above, which require genuine infrastructure
  builds (Galois fixed-field, smooth-curve duality, pullback naturality,
  and the F-vs-F̄-points structural question).
