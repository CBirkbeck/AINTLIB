# Decomposition — Eichler-integral proof of period-map injectivity (k ≥ 2)

**Mode:** `/develop --decompose` (adversarial). **No tickets created.**
**Goal (R):** `periodMap'_injective` for `k ≥ 2` — `ι(f) = 0 ⟹ f = 0` for `f ∈ S_k(Γ₁N)` — proved via
the Eichler integral + the Δⁿ weight-0 trick, **replacing** the superseded boundary-identity route
`interior_edges_cancel_sum` (Shimura 8.2.22).
**Source of the proof:** reviewer reply `expert-review/2026-06-24/reply.md` §1–§2 (verbatim quotes
below); cross-refs Shimura §8.2, Diamond–Shurman §5.x, arXiv:1701.00611 (Bol / connecting morphism),
Res. Math. Sci. doi 10.1007/s40687-018-0128-2 (holomorphic modular forms and cocycles).

---

## Step 1 — Plain-English proof (transcribed from the source, reply.md §1)

Let `Γ = Γ₁(N)`, `n = k−2`, `f ∈ S_k(Γ)` with `ι(f) = 0`, i.e. every period `∫_α^β f(τ)P(τ,1) dτ`
vanishes (all cusps α,β; all `P ∈ Sym^n`).

1. **Eichler integral.** `E_f(z) = Σ_{m≥1} (a_m / m^{k−1}) q^m = C_k ∫_z^{i∞} f(τ)(τ−z)^{k−2} dτ`
   (absolutely convergent by cusp decay). With `D = (1/2πi) d/dz`, **`D^{k−1} E_f = f`**.
2. **Modularity defect = period polynomial.** For `γ ∈ Γ`,
   `(E_f|_{2−k}γ − E_f)(z) = C_k ∫_{γ⁻¹∞}^∞ f(τ)(τ−z)^{k−2} dτ`; expanding `(τ−z)^n = Σ_j C(n,j)(−z)^{n−j}τ^j`
   makes every coefficient a period `∫_{γ⁻¹∞}^∞ f τ^j dτ`. Hence `ι(f)=0 ⟹ E_f|_{2−k}γ = E_f` ∀γ —
   `E_f` transforms as a modular form of weight `2−k`.
3. **Holomorphy/vanishing at every cusp.** The Eichler integral based at any cusp α equals `E_f`
   (their difference is a period = 0); after slashing by σ it becomes the Eichler integral at ∞ of
   `f|_kσ`, whose expansion `Σ b_m/(m/h)^{k−1} e^{2πimz/h}` has only positive Fourier powers ⟹ `E_f`
   holomorphic and vanishing at every cusp.
4. **Negative/zero-weight vanishing.** `n = k−2 > 0`: `E_f^{12} Δ^n` has weight `12(2−k)+12n = 0`,
   holomorphic on ℍ, vanishing at every cusp (Δ does) ⟹ a weight-0 form on the compact modular curve
   ⟹ constant ⟹ 0; `Δ ≠ 0` on ℍ ⟹ `E_f = 0`. (k=2: `E_f` already weight 0, same conclusion.) Then
   `f = D^{k−1} E_f = 0`. ∎

**Where Bol's identity actually enters (adversarial note).** The source invokes Bol only in §2 to
*explain* why `E_f` carries weight `2−k` (the exact sequence `0→V_{k−2}→O(ℍ)_{2−k}--D^{k−1}-->O(ℍ)_k→0`
is Γ-equivariant). The §1 proof derives the weight-`(2−k)` transformation **directly** from the
integral defect (2), so **no general Bol operator theorem is required as a leaf**; only the specific
integral transformation. This refutes the availability-scan's "Bol missing ⟹ infeasible" verdict.

---

## Step 2 — Decomposition tree (mirrors reply.md §1.1–§1.4)

```
R  periodMap'_injective_eichler (hk : 2 ≤ k) : Injective (periodMap' N k hk)
   = ι(f)=0 ⟹ f=0.   Source: reply.md §1.

  L0  ι(f)=0 ⟹ all cusp-difference periods vanish: rawPairing f ((α)-(β) ⊗ P)=0
      → LEAF (project, PROVEN): periodMap'/rawPairing unfolding, PeriodMap.lean.

  G1  Eichler integral E_f and D^{k-1}E_f = f.   Source: reply.md §1.1, (2)-(3).
      G1a  def eichlerIntegral f : ℍ → ℂ           [API GAP — new def]
      G1b  bol_iterated : D^{k-1}(E_f) = f          [API GAP — theta op / q-series]
      G1c  eichler_holomorphic : E_f holo on ℍ      → from isExactOn_upperHalf (project) / q-series

  G2  modularity-defect formula (the heart).   Source: reply.md §1.2, (5).
      G2a  eichler_slash_sub : (E_f|_{2-k}γ - E_f)(z) = ∫_{γ⁻¹∞}^∞ f(τ)(τ-z)^{k-2}dτ
                                                       [API GAP — integral CoV, grounded]
      G2b  defect_coeffs_are_periods : coeffs of (5) = periods ∫ f τ^j  → binomial bridge (project)
      L7  ι(f)=0 ⟹ E_f|_{2-k}γ = E_f ∀γ           → composition of G2a+G2b+L0

  G3  holomorphy/vanishing at every cusp.   Source: reply.md §1.3, (7)-(8).
      G3a  eichler_basepoint_indep : E_{f,α} = E_f (diff is a period = 0)  → from L0
      G3b  eichler_cusp_positive_fourier : only positive q-powers at every cusp  [API GAP]

  G4  negative/zero-weight vanishing ⟹ E_f = 0.   Source: reply.md §1.4.
      G4a  package E_f as ModularForm Γ (2-k)       [API GAP — needs L7+G1c+G3b]
      G4b  Δ : ModularForm SL₂ℤ 12, Δ ≠ 0 on ℍ      → LEAF (mathlib: discriminant, discriminant_ne_zero)
      G4c  E_f^{12}·Δ^n : ModularForm Γ 0, vanishes at a cusp  [API GAP — mul/pow + cusp val]
      G4d  weight-0 form on arithmetic Γ is constant → LEAF (mathlib: eq_const_of_weight_zero)
      L8  E_f^{12}·Δ^n = 0  (const + vanishes at cusp)  → composition
      L9  E_f = 0  (Δ≠0 on ℍ)                          → composition of L8 + G4b

  FINAL  f = D^{k-1}E_f = 0   → composition of G1b + L9.
```

LOC anchoring (reply.md is terse — ground in the source's own steps): §1.1 ≈ 6 lines → G1 ~80–120
LOC (the def + Bol via q-series is the fiddly part); §1.2 ≈ 8 lines → G2 ~120–200 LOC (the integral
CoV; reuses project `periodForm_mob_general`/`cuspDiff_const`); §1.3 ≈ 6 lines → G3 ~60–100 LOC;
§1.4 ≈ 8 lines → G4 ~80–150 LOC (mostly assembling existing mathlib `Δ`/weight-0). Total order: a
**bounded multi-lemma development (~weeks)**, not the multi-month modular-curve build of `interior_edges_cancel_sum`.

---

## Step 3 — Source quotes + Lean↔source (per leaf)

### L0 (LEAF, project — PROVEN)
- Lean: `periodMap' N k hk f = 0` unfolds (via `rawPairing`) to `Σ_c (D c)·cuspValue f P c = 0` for
  `D ∈ Div0`, i.e. all cusp-*difference* periods vanish. `PeriodMap.lean` (`periodMap'` :1881,
  `rawPairing` :623, `cuspValue` :538).
- Source (reply.md §1, (1)): *"for every pair of cusps α,β ∈ P¹(Q) and every polynomial P ∈ Sym^n,
  ∫_α^β f(τ)P(τ,1) dτ = 0."*
- Match: `ι(f)=0` ⟺ all `rawPairing f ((α)-(β) ⊗ P) = 0` ⟺ reviewer's (1) (cusp-difference form,
  which is exactly Div⁰).

### G1 (API GAP — Eichler integral, reply.md §1.1)
- Source (verbatim): *"Set `E_f(z) = Σ_{m≥1} a_m/m^{k−1} q^m`. With `D = (1/2πi) d/dz`, one has
  `D^{k−1} E_f = f`. Equivalently, up to a fixed nonzero constant `C_k`, `E_f(z) = C_k ∫_z^{i∞}
  f(τ)(τ−z)^{k−2} dτ`. The exponential decay of a cusp form makes this integral absolutely
  convergent."*
- Lean↔source: G1a defines `E_f`; G1b is `D^{k-1}E_f=f`; G1c is holomorphy. The integral form (for
  G2) and the q-series form (for G1b) must be proven equal (term-by-term integration) OR E_f defined
  one way and the other derived. Project has the primitive (`isExactOn_upperHalf` :87, `periodForm`
  :284) — the integral kernel side; mathlib has `qExpansion` + `PowerSeries.derivativeFun` — the
  series side.

### G2 (API GAP — modularity defect, reply.md §1.2)
- Source (verbatim): *"(E_f|_{2−k}γ)(z) − E_f(z) = C_k ∫_{γ⁻¹∞}^∞ f(τ)(τ−z)^{k−2} dτ ... Expanding
  (τ−z)^n = Σ_j C(n,j)(−z)^{n−j}τ^j shows that every coefficient of the right-hand side is a period
  ... Consequently (1) implies E_f|_{2−k}γ = E_f."*
- Lean↔source: G2a is the change-of-variables τ↦γτ in the integral, using f's weight-k modularity —
  the SAME computation as the project's `isPeriodInvariant_all` (:1856, via `cuspDiff_const`) and the
  Möbius CoV `periodForm_mob_general`, but at the function (not pairing) level. G2b is the binomial
  expansion (project has the binomial bridge `petersson_binomial_periodForm`). L7 composes with L0.

### G3 (API GAP — cusp holomorphy, reply.md §1.3)
- Source (verbatim): *"the Eichler integral based at α ... The difference ... is C_k ∫_α^∞
  f(τ)(τ−z)^n dτ, which is zero by (1). Hence E_{f,α} = E_f. After slashing by σ ... (E_f|_{2−k}σ)(z)
  = C_k' Σ_{m≥1} b_m/(m/h)^{k−1} e^{2πimz/h}. It therefore has only positive Fourier powers at that
  cusp. Thus E_f is holomorphic—and in fact vanishing—at every cusp."*
- Lean↔source: G3a (basepoint independence) is immediate from L0; G3b (positive Fourier powers) is
  the q-expansion of E_f at each cusp — reuses the project's cusp-decay (`tendsto_horizontal_cap`
  :375, `periodForm_norm_le`) and the slash machinery.

### G4 (mostly mathlib — vanishing, reply.md §1.4)
- Source (verbatim): *"E_f^{12} Δ^n has weight 12(2−k)+12n=0. It is holomorphic on ℍ, holomorphic at
  every cusp, and vanishes at every cusp because Δ does. It is therefore a holomorphic function on
  the compact modular curve, hence constant, and that constant is zero. Since Δ has no zeros on ℍ,
  E_f = 0."*
- Lean↔source: G4b = mathlib `discriminant` (`Δ z = (eta z)^24`, `discriminant_ne_zero`); G4d =
  mathlib `ModularForm.eq_const_of_weight_zero` (arithmetic subgroups — covers Γ₁N); G4a/G4c are the
  packaging (E_f as `ModularForm Γ (2-k)`, then the weight-0 product) — the only genuinely new API
  here, and it routes AROUND the level-1 restriction of `levelOne_neg_weight_eq_zero` exactly as the
  reviewer intends.

---

## Step 4 — Provability per leaf

| Node | Discharge | Status |
|---|---|---|
| L0 | project: `periodMap'`/`rawPairing` unfolding | PROVEN |
| G1c | project `isExactOn_upperHalf` (primitive) / convergent q-series | one-step |
| G1a, G1b | NEW def + theta-op/q-series `D^{k-1}E_f=f` (mathlib `PowerSeries.derivativeFun`, `qExpansion`) | **API GAP** |
| G2a | NEW: integral CoV, grounded in project `periodForm_mob_general`/`isPeriodInvariant_all` | **API GAP** |
| G2b | project binomial bridge `petersson_binomial_periodForm` | one-step |
| L7 | compose G2a+G2b+L0 | composition |
| G3a | from L0 | one-step |
| G3b | NEW: cusp q-expansion of E_f (project cusp-decay) | **API GAP** |
| G4a, G4c | NEW: package E_f / E_f¹²Δⁿ as `ModularForm Γ (2-k)` / `Γ 0` | **API GAP** |
| G4b | mathlib `discriminant`, `discriminant_ne_zero` | mathlib ✓ |
| G4d | mathlib `ModularForm.eq_const_of_weight_zero` (arithmetic) | mathlib ✓ |
| L8, L9, FINAL | compositions | composition |

**4 API-gap clusters: G1 (Eichler integral + Bol-via-q-series), G2 (integral defect), G3 (cusp
holomorphy), G4 (weight-(2−k) packaging).** Each bounded; each grounded in named existing pieces.

---

## Step 4.5 — Adversarial pass

### R (top) — composition attack
- [1] Could L0..L9 all hold but R fail? R = `Injective periodMap'` ⟺ `ι(f)=0⟹f=0`; FINAL gives
  `f=0` from `ι(f)=0`. Composition sound (linear map injective ⟺ ker trivial).
- [2] Edge: k=2 (n=0). Then `(τ-z)^{k-2}=1`, E_f = Σ a_m/m q^m, weight 2-k=0; the Δⁿ trick is
  vacuous (n=0) and E_f is *directly* weight-0 ⟹ const ⟹ 0. Source handles k=2 explicitly. ✓
- [3] Source-drift: R is the SAME `periodMap'_injective` the boundary route targeted (same statement,
  PeriodInjective.lean:164) — only the PROOF changes. No statement drift. ✓
- Verdict: SURVIVED.

### G1 (Eichler integral)
- [1] Counterexample: is `D^{k-1}E_f=f` actually true? `D q^m = m q^m` (D=(1/2πi)d/dz, q=e^{2πiz}),
  so `D^{k-1}(a_m/m^{k-1} q^m) = a_m q^m`; sum = f. Formal-q-series identity, no counterexample.
- [2] Edge: m=0 term — cusp form has a_0=0, sum starts m≥1, m^{k-1}≠0 ✓; k=2 ⟹ m^{k-1}=m ✓.
- [3] Convergence (E_f holo): a_m = O(m^{k-1}) (Hecke) or O(m^{(k-1)/2+ε}) (Deligne) ⟹ a_m/m^{k-1}
  bounded ⟹ q-series converges on ℍ. No divergence. (Deligne bound not needed — Hecke's trivial
  O(m^{k-1}) suffices for absolute convergence on ℍ since |q|<1.) ✓
- [4] Source-drift: matches reply.md (2)-(3) verbatim. ✓
- [5] Discharge: `PowerSeries.derivativeFun` (mathlib, Derivative.lean:44) gives the formal
  derivative; the theta-op (×m on coeff m) = `q · derivativeFun` — derivable, not a single named
  lemma ⟹ genuinely an API gap (not a ≤3-lemma discharge). Correctly classified API GAP.
- Verdict: SURVIVED as an API gap (true, bounded, not falsely claimed a leaf).

### G2 (modularity defect — the crux)
- [1] Counterexample to "defect = ∫_{γ⁻¹∞}^∞": this is the standard Eichler computation (change
  τ↦γ⁻¹τ in ∫_{γz}^{i∞}, split the contour at the cusp); no contradicting statement. The split
  contour ∫_z^{i∞} - ∫_{γ⁻¹z}^{i∞} reorganizes to ∫_{γ⁻¹∞}^∞ via f's weight-k automorphy.
- [2] Edge: γ = id ⟹ defect = 0 = ∫_∞^∞ ✓. Parabolic γ (fixes a cusp): ∫_{γ⁻¹∞}^∞ over a closed
  loop — must check it's the period, not 0; for γ∈Γ₁N the relevant cusp differs, nonzero in general
  but killed by ι(f)=0. ✓
- [3] Hypothesis: needs f weight-k modular (have), (τ-z)^{k-2} polynomial (k≥2 ⟹ k-2≥0 ✓; k<2 would
  give negative power — confirms the k≥2 gate is necessary, not over-specified).
- [4] Source-drift: reply.md (5) verbatim. The project's `isPeriodInvariant_all` proves the
  PAIRING-level version (defect of rawPairing = 0); G2a is the FUNCTION-level version. Risk: the
  function-level CoV is genuinely more than the pairing-level (an extra "differentiate under the
  integral / contour" layer). Flagged as the largest API gap. Honest.
- [5] Discharge: `periodForm_mob_general` + `cuspDiff_const` (project) are the grounding, but G2a is
  NOT a ≤3-lemma composition of them ⟹ correctly an API GAP, not a leaf.
- Verdict: SURVIVED as the principal API gap; honestly the riskiest (function-level integral CoV).

### G3 (cusp holomorphy)
- [1] Counterexample: could E_f have a pole/negative-power at a cusp? The reviewer's (8) shows only
  positive powers via the m^{k-1} denominator; no negative power arises (a_0=0 for cusp form, and the
  Eichler integral of a cusp form has no constant term). ✓
- [2] Edge: width-h cusps (N>1 has several) — (8) uses the width h; positive powers e^{2πimz/h},
  m≥1. ✓ Irregular cusps: covered by the slash-σ reduction.
- [3] Hypothesis: needs f a CUSP form (a_0=0 at every cusp) — if f were merely modular (a_0≠0), E_f
  would have a log/linear term. Confirms cusp-form hypothesis necessary. ✓
- [4] Source-drift: reply.md (7)-(8) verbatim. ✓
- [5] Discharge: project cusp-decay (`tendsto_horizontal_cap`, `periodForm_norm_le`) grounds it; the
  q-expansion-of-E_f-at-each-cusp is new ⟹ API GAP. ✓
- Verdict: SURVIVED as a bounded API gap.

### G4 (vanishing) — the part the scan called the wall
- [1] Counterexample: weight-0 holomorphic form on Γ₁N vanishing at a cusp but ≠0? `eq_const_of_weight_zero`
  ⟹ constant; vanishing at one cusp ⟹ const=0. No counterexample. ✓
- [2] Edge: k=2 ⟹ n=0 ⟹ Δ^0=1, E_f^{12}·1 = E_f^{12} weight 0 directly; same conclusion. ✓
- [3] Hypothesis: needs E_f holomorphic AT cusps (G3) to be a genuine `ModularForm` (not weakly
  holomorphic) — this is exactly why G3 is required; without it the weight-0 form could be a modular
  FUNCTION with poles. Source explicitly flags this ("invariance on ℍ by itself would permit weakly
  holomorphic negative-weight forms"). Hypothesis necessary, not over-specified. ✓
- [4] Source-drift: reply.md §1.4 verbatim; the Δⁿ-trick routes around level-1-only negative-weight
  vanishing — matches the source's "formalization-friendly" remark. ✓
- [5] Discharge attack: `lean_hover`-equivalent confirmed by the scan — `discriminant`/`discriminant_ne_zero`
  (mathlib Discriminant.lean:50,123) and `ModularForm.eq_const_of_weight_zero` (mathlib NormTrace.lean:164,
  arithmetic subgroups) EXIST with matching types. G4a/G4c packaging (E_f, E_f¹²Δⁿ as ModularForm) is
  the new part ⟹ API GAP. The scan's "architecture gap (CuspForm only k≥2)" is REAL but bounded: we
  build a `ModularForm Γ (2-k)` (not CuspForm), which the SlashAction-at-negative-k (confirmed
  present) supports.
- Verdict: SURVIVED; the mathlib pieces the scan feared missing are PRESENT. Overturns "infeasible".

### Internal-node / prior-B2 consultation
- `b2_log.jsonl`: checked — none pertains to the Eichler route (prior B2s, if any, concern the
  boundary route). No name/shape match.
- The whole tree's only unproven dependence is G1–G4 (new API), each grounded; no leaf falsely
  claimed discharged.

---

## Step 2.5 — Skeleton (compiled) + type-level findings

Skeleton: `LeanModularForms/HeckeRIngs/GL2/ModularSymbols/EichlerInjective.lean` —
**`lake build` clean, 9 sorries, 0 errors (3716 jobs).** 8 declarations: `eichlerIntegral` (G1a),
`differentiableOn_eichlerIntegral` (G1c), `bol_iterated_eichler` (G1b, `D^{k-1}` as
`((2πi)⁻¹)^(k-1).toNat · iteratedDeriv (k-1).toNat`), `eichler_basepoint_indep` (G3a),
`eichler_cusp_holo` (G3b), `eichler_slash_invariant` (L7), `eichlerModularForm` (G4a),
`eichler_eq_zero` (L9), `periodMap'_injective_eichler` (R).

**Findings that refine the gap assessment (these OVERTURN the availability scan further):**
- **G4a typechecks with NO weakening.** `eichlerModularForm : ModularForm ((Gamma1 N).map (mapGL ℝ))
  (2 - k)` elaborates — `ModularForm Γ w` is defined for *any* `w : ℤ`, so negative `2−k` is fine; no
  `CuspForm`-only restriction bites (we build a `ModularForm`, not a `CuspForm`). The scan's
  "architecture gap" was illusory. Its three fields `holo'`/`slash_action_eq'`/`bdd_at_cusps'` are
  exactly G1c / L7 / G3b.
- **G2/L7 (slash invariance) states cleanly** for the ℂ→ℂ Eichler integral via the `((↑) : ℍ → ℂ)`
  coercion bridge: `(eichlerIntegral f ∘ (↑)) ∣[2-k] (γ : SL(2,ℤ)) = eichlerIntegral f ∘ (↑)`. The
  `SlashAction ℤ SL(2,ℤ) (ℍ→ℂ)` instance accepts the non-positive weight. No mathematical weakening.
- **G4b/G4d mathlib pieces confirmed by signature:** `ModularForm.discriminant`/`discriminant_ne_zero`
  (`Mathlib/NumberTheory/ModularForms/Discriminant.lean`, also a `CuspForm 𝒮ℒ 12` form at :235);
  `ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0)` (`NormTrace.lean:164`);
  `IsArithmetic` for `(Gamma1 N).map (mapGL ℝ)` available via the project's `.conj`/`.map` machinery.
- **The REAL larger gap is G3 (cusp behaviour), not G2/G4:**
  - **New sub-gap G3a-def: `eichlerIntegralAt c`** (the Eichler integral *based at an arbitrary cusp*
    c) is not defined; the literal G3a (`E_{f,c} = E_f`) is not even stateable without it. The
    skeleton states the *provable driver* instead: `cuspValue f P c₁ = cuspValue f P c₂` (the Div⁰
    difference) — and the agent correctly **rejected the FALSE `cuspValue f P c = 0`** (only
    differences vanish under `ι(f)=0`, not individual cusp values). Soundness trap avoided.
  - **G3b** ("vanishing at *every* cusp") is stated only as the cusp-∞ shadow
    `IsBoundedAtImInfty (eichlerIntegral f ∘ (↑))`; the per-cusp content is deferred into
    `eichlerModularForm.bdd_at_cusps'`. Closing it needs the cusp q-expansion of E_f at all cusps.
- Namespace correction: `isExactOn_upperHalf` is project-namespace (`HeckeRing.GL2.ModularSymbols`,
  PeriodInvariant.lean:87), not `Complex.`. Bridge is `UpperHalfPlane.coe`, not `ofComplex` (the
  latter is an `OpenPartialHomeomorph`).

**Net:** G1/G2/G4 state type-correctly with no weakening; **G3 (cusp behaviour at all cusps + the
`eichlerIntegralAt c` definition) is the principal residual** — still bounded (the project has cusp
decay + the slash machinery), but larger than one clean statement. The order-of-difficulty is the
*reverse* of the availability scan's guess.

## Step 5 — Confidence gate

1. Every leaf discharged from mathlib (G4b, G4d), project (L0, G1c, G2b, G3a), or an explicit API gap
   with sub-structure (G1, G2, G3, G4a/c) — ✓.
2. Skeleton compiles — see EichlerInjective.lean (Step 2.5), `lake build` status reported below.
3. Verbatim source quotes per leaf — ✓ (Step 3).
4. Adversarial pass, ≥3 attacks per node — ✓ (Step 4.5).
5. Prior-B2 log consulted — ✓ (clean).
6. Tree mirrors the source (reply.md §1.1–§1.4 → G1–G4) with source line-count anchoring — ✓.

**No REVIEW-PENDING leaves.** Gate PASSES for the whole tree (the 4 API gaps are sub-developments,
not opaque blockers).

---

## Feasibility assessment

The Eichler-integral route to `periodMap'_injective` is **FEASIBLE and bounded**. Its hardest
analytic ingredients — a holomorphic primitive on ℍ, the Möbius change-of-variables, cusp decay, the
binomial expansion, and (crucially) the discriminant Δ with `Δ≠0` and **weight-0-⟹-constant for
arithmetic subgroups** — are ALL already present in the project or mathlib. The four API gaps (G1
Eichler integral + `D^{k-1}E_f=f`; G2 the integral modularity-defect formula; G3 cusp holomorphy of
E_f; G4 the weight-`(2−k)` `ModularForm` packaging + `E_f¹²Δⁿ` assembly) are genuine new code but each
is a bounded, source-grounded sub-development on the order of weeks, **not** the multi-month
modular-curve-boundary build that `interior_edges_cancel_sum` (Shimura 8.2.22) demands. The
availability scan's "infeasible (Bol missing)" verdict is **overturned**: the §1 proof needs only the
*specific* integral transformation (G2, grounded in the project's existing `isPeriodInvariant_all`
computation), not a general Bol operator theorem; and the Δⁿ weight-0 trick — whose pieces the scan
itself confirmed present — supplies the negative-weight vanishing at level Γ₁N. **Principal risk (revised after the skeleton compiled):**
G2/G4 state type-correctly with no weakening (the `ModularForm` at negative weight `2−k` typechecks;
the slash invariance states cleanly via the `ℍ↪ℂ` bridge). The deepest residual is **G3 — cusp
behaviour at *every* cusp**, which needs (i) a new `eichlerIntegralAt c` definition (the Eichler
integral based at an arbitrary cusp) and (ii) the cusp q-expansion of `E_f` showing only positive
powers; the literal "based-at-c equals based-at-∞" is not even stateable without (i). Still bounded
(project has cusp decay + slash machinery), but the order-of-difficulty is the reverse of the
availability scan's guess. **Fallback (reviewer-sanctioned):** if G1–G4 prove awkward in Lean, cite classical
period-map injectivity (ranked injectivity > IHR-c > FIH) and keep FIH downstream.

## Next step
If approved, run `/develop` (full) to create tickets for G1→G2→G3→G4→assembly (in dependency order),
then `/beastmode`. The superseded `interior_edges_cancel_sum` route stays in-tree but off the critical
path (its proven pieces — `tile_stokes_fd`, binomial bridge — are reusable, e.g. G2b).
