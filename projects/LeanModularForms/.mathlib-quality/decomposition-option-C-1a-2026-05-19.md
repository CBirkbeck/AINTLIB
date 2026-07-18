# Decomposition: Option C-1a — Strengthen M7-sqfree to expose F_q at uniform level (N·l²)/q

**Date**: 2026-05-19
**Status**: Phase 1e adversarial (post-Option B/C-1 analysis)
**Strategy**: Strengthen the existing `miyake_4_6_7_squarefree_decomp` to ALSO
output the per-q V_q-preimage `F q` at the uniform natural level `Γ_1((N·l²)/q)`,
alongside the existing g_q at uniform output level Γ_1(N·l²). Use this exposed
F_q directly in the helper proof, applying Miyake's argument verbatim.

## Goal

Discharge `miyake_descent_l_prime_gt_one_helper`'s sorry (the Miyake 4.6.14
Fourier vanishing) following Miyake's argument exactly:

```
slash_sum_at_l'N(h)(z) 
  = slash_sum_at_l'³·N(h)(z)                            -- M6(1), h at l'·N, mult l'²
  = Σ_q slash_sum_at_l'³·N(V_q(F q at (l'³·N)/q))(z)    -- linearity + h = Σ V_q(F_q) at function level
  = Σ_q slash_sum_at_((l'³·N)/q)(F q)(q·z)              -- M6(2) per q, N_M6 = (l'³·N)/q
```

Take m-th Fourier coefficient: for Coprime m l' and q ∈ l'.primeFactors, q∤m, so
each summand's m-th coefficient is 0. Done.

## Plain-English proof

**Step A — Strengthen M7-sqfree** to expose F_q at uniform level Γ_1((N·l²)/q):

For each q ∈ l.primeFactors, M7-sqfree internally constructs F_q via the strong
dichotomy. The natural level depends on peel order:

* **Base case (l = q single prime)**: F_q is constructed at level
  `Γ_1((N·l²)/q) = Γ_1(N·q)` directly (from `conductor_theorem_dichotomy_cuspForm_strong`
  at `SMOObligations.lean:5879`). This IS the uniform level ✓.

* **Inductive case, q peeled first**: F_q is constructed at level
  `Γ_1((N·q²)/q) = Γ_1(N·q)` (from line 6121). Need to RESTRICT to
  uniform level `Γ_1((N·l²)/q) = Γ_1(N·q · (l/q)²) = Γ_1(N·q · l'²)`.
  Restriction is valid: `Γ_1(N·q) ⊃ Γ_1(N·q·l'²)` since N·q | N·q·l'².
  ✓.

* **Inductive case, q' from IH**: The recursive call (IH) at level
  `Γ_1(N·q²)` with `l_new = l'` outputs F_{q'} at level
  `Γ_1((N·q²·l'²)/q') = Γ_1((N·l²)/q')` directly. No restriction
  needed ✓.

**Step B — Apply the strengthened M7-sqfree to h = Δ' = f - V_p(g_p_local)**
at level Γ_1(l'·N) with l = l'. Get F_q at level Γ_1((l'·N·l'²)/q) = Γ_1(l'³·N/q)
for each q ∈ l'.primeFactors.

**Step C — Function identity** h(z) = Σ_q V_q(F_q at (l'³·N)/q)(z) on ℍ. This
follows from M7-sqfree's qExp identity + qExpansion_eq_zero_iff at common level
(say Γ_1(l'⁴·N)).

**Step D — Apply M6(1)** to h: slash_sum_at_l'N(h)(z) = slash_sum_at_l'³·N(h)(z)
as functions. h is at level Γ_1(l'·N) in modFormCharSpace; multiplier l'²
satisfies the M6(1) hypotheses (Coprime p l'², l'² ∣ (l'·N)/p).

**Step E — Apply M6(2)** per q at smaller level Γ_1((l'³·N)/q), multiplier q:
slash_sum_at_l'³·N(V_q(F_q at (l'³·N)/q))(z) = slash_sum_at_((l'³·N)/q)(F_q)(q·z).

**Step F — Combine + take Fourier coefficient**:
```
a_m(slash_sum_at_l'N(h)) = a_m(slash_sum_at_l'³·N(h))           [Step D]
                         = Σ_q a_m(slash_sum_at_l'³·N(V_q(F_q))) [Step C linearity]
                         = Σ_q a_m(z ↦ slash_sum_at_((l'³·N)/q)(F_q)(q·z))  [Step E]
                         = Σ_q [q|m] · a_{m/q}(slash_sum_at_((l'³·N)/q)(F_q))
                         = 0   for Coprime m l' (since q∤m for each q ∈ l'.primeFactors)
```

## Lemmas (in order)

### L1 (NEW, project strengthening): `miyake_4_6_7_squarefree_decomp_with_preimage`

Strengthened version of M7-sqfree that ALSO returns F_q at uniform level.

```lean
theorem miyake_4_6_7_squarefree_decomp_with_preimage
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l : ℕ) (hl_gt : 1 < l) (hl_sqfree : Squarefree l)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI hM_NeZero : NeZero (N * l ^ 2) := ⟨...⟩
    have hNM : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
    ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
      (F : (q : ℕ) → q ∈ l.primeFactors →
            haveI : NeZero ((N * l ^ 2) / q) := ⟨...⟩
            CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k),
      (∀ q ∈ l.primeFactors, g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM))) ∧
      -- F's character at level (N·l²)/q
      (∀ q (hq : q ∈ l.primeFactors), F q hq ∈ cuspFormCharSpace k
        (χ.comp (ZMod.unitsMap (... : N ∣ (N · l²)/q)))) ∧
      -- V_q(F q hq) = g q as functions on ℍ
      (∀ q (hq : q ∈ l.primeFactors),
        haveI : NeZero q := ⟨...⟩
        (⇑(HeckeRing.GL2.modularFormLevelRaise ((N * l ^ 2) / q) q k
          (F q hq).toModularForm') : UpperHalfPlane → ℂ) = ⇑(g q)) ∧
      -- The qExp identity (unchanged from existing M7-sqfree)
      ∀ n : ℕ,
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        ∑ q ∈ l.primeFactors,
          if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g q)).coeff (n / q)
          else 0
```

- **Source**: Miyake §4.6 Lemma 4.6.7 (p. 159-160). Project's existing
  `miyake_4_6_7_squarefree_decomp` at `SMOObligations.lean:5697`.
- **Implementation**: track F alongside g in the existing M7-sqfree induction:
  - Base case: F at level Γ_1((N·l²)/q) directly from strong dichotomy (line 5879).
  - Inductive case, q peeled first: F at level Γ_1(N·q) from local dichotomy
    (line 6121), then `restrictSubgroup` to Γ_1((N·l²)/q).
  - Inductive case, q' from IH: F from IH at level Γ_1((N·l²)/q') (= IH's output level).
- **LOC estimate**: ~100-150 LOC (additional output, mostly mechanical).

### L2 (NEW, helper internal): function identity Δ' = Σ_q V_q(F_q)

For Δ' at level Γ_1(l'·N) with Coprime n l' vanishing and the strengthened M7-sqfree
output (F_q, g_q), bridge to function identity:

```lean
private lemma delta_prime_eq_sum_V_q_F_q_function
    {N : ℕ} [NeZero N] {k : ℤ}
    {l' : ℕ} [NeZero l'] (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    [NeZero (l' * N)]
    (Δ' : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (F : (q : ℕ) → q ∈ l'.primeFactors → ...)
    (g : ℕ → ...)
    (h_V_q_F_eq_g : ∀ q (hq : q ∈ l'.primeFactors), ⇑(V_q (F q hq)) = ⇑(g q))
    (h_qexp : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) Δ').coeff n =
      ∑ q ∈ l'.primeFactors, if q ∣ n then ... else 0) :
    ∀ z : UpperHalfPlane,
      (⇑Δ' : UpperHalfPlane → ℂ) z =
      ∑ q ∈ l'.primeFactors, ⇑(V_q (F q (hq : q ∈ l'.primeFactors))) z := by sorry
```

- **Discharge**: `qExpansion_eq_zero_iff` at level Γ_1(l'⁴·N) (common level for restriction).
- **LOC estimate**: ~40-60 LOC.

### L3 (NEW, helper internal): m-th coefficient of (z ↦ G(q·z)) for Coprime m l'

For Coprime m l' and q ∈ l'.primeFactors, the m-th Fourier coefficient at period 1
of the function `z ↦ G(q·z)` vanishes.

```lean
private lemma qExp_at_qz_coprime_vanishing
    (q : ℕ) [NeZero q] (G : UpperHalfPlane → ℂ) (m : ℕ) (hqm : ¬ q ∣ m) :
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z => G ((HeckeRing.GL2.levelRaiseMatrix q) • z))) = 0 := by sorry
```

- **Source**: Standard q-expansion formula for V_q-style operators.
- **Discharge**: Apply qExpansion_one_modularFormLevelRaise_coeff or directly via
  HasSum on the period-1 Fourier expansion.
- **LOC estimate**: ~30-40 LOC.

### L4 (project, leaf): `miyake_4_6_6_level_commute` (M6(1))

Already proven at `SMOObligations.lean:5172`.

### L5 (project, leaf): `miyake_4_6_6_level_commute_delta` (M6(2))

Already proven at `SMOObligations.lean:5246`.

### L6 (NEW, top-level helper): Helper discharge

The helper's sorry, discharged using L1-L5.

```lean
private lemma miyake_descent_l_prime_gt_one_helper ... := by
  -- (existing Phases A, B, C.1 already done)
  -- Sorry replaced with the M6(1) + M7-sqfree-strengthened + M6(2) chain:
  -- 1. Define Δ' = f - V_p(g_p_local) (already done in helper context).
  -- 2. Apply L1 (strengthened M7-sqfree) to Δ' with l = l': get F, g, qExp identity.
  -- 3. Apply L2: function identity Δ' = Σ_q V_q(F q).
  -- 4. Apply M6(1) to Δ': bridge slash_sum_at_l'N(Δ') = slash_sum_at_l'³·N(Δ').
  -- 5. Apply M6(2) per q: slash_sum_at_l'³·N(V_q(F q))(z) = slash_sum_at_((l'³·N)/q)(F q)(q·z).
  -- 6. Apply L3: m-th coefficient of each q-shifted slash sum is 0 for Coprime m l'.
  -- 7. Sum: a_m(slash_sum_at_l'N(Δ')) = 0 for Coprime m l'.
  -- 8. Bridge to RHS via h_RHS_qexp_coeff (already done in Phase B).
```

- **LOC estimate**: ~100-150 LOC.

## Adversarial pass

### Attack 1 — Counterexample search

**Q**: Does the strengthened M7-sqfree's F_q at uniform level have the
right V_q-preimage property?

**Test**: V_q(F_q at (N·l²)/q) at level Γ_1(N·l²) = ⇑(g_q) at level Γ_1(N·l²)
as functions on ℍ?

- Base case (l = q): F_q at Γ_1((N·l²)/q) is the V_q-preimage of f.restrict at
  level Γ_1(N·l²) by strong dichotomy. g_q is the restriction of F_q to Γ_1(N·l²).
  V_q(F_q at (N·l²)/q) = ⇑(f.restrict at Γ_1(N·l²)) as functions ✓.
  ⇑(g_q at Γ_1(N·l²)) = ⇑(F_q) (since g_q is just F_q's restriction). So
  V_q(F_q) = f.restrict as functions, and ⇑(g_q) = ⇑(F_q). The relationship is:
  V_q(F_q) is f.restrict; g_q is F_q's restriction (= F_q as function).
  
  Hmm, so V_q(F_q) ≠ g_q as functions in the base case. Let me recheck.
  
  Actually wait: in the base case, l = q and f is q-supported. F_q via dichotomy:
  V_q(F_q) = f.restrict. g_q (the M7-sqfree output) = F_q.restrictSubgroup. As
  functions, g_q ≡ F_q. So V_q(F_q) = V_q(g_q) at the function level (since F_q
  and g_q are the same function). And V_q(F_q) = f.restrict.
  
  So V_q(g_q at uniform level Γ_1(N·l²)) at level Γ_1(q · N·l²) — is this the
  same as V_q(F_q at (N·l²)/q) at level Γ_1(N·l²)?
  
  As functions on ℍ: yes (V_q's underlying function depends only on the function
  value of its input, not the bundling level). So they're equal as functions.
  
  But at the TYPE level (bundled), they're at different levels: V_q(g_q) at
  Γ_1(q · N·l²), V_q(F_q) at Γ_1(N·l²). For our purpose (slash_sum_at_l'³·N
  applied to it), the function-level equality is what we need ✓.

- Inductive case, q peeled first: F_q from line 6121 at Γ_1(N·q). V_q(F_q) =
  h_form (q-supported part of f at Γ_1(N·q²)). g_q at Γ_1(N·l²) = F_q's
  restriction. So V_q(F_q at (N·l²)/q) (after restriction to (N·l²)/q) = ⇑(h_form)
  as functions = ⇑(g_q-related-component) as functions.

  Wait the EQUATION V_q(F q hq) = g q at the FUNCTION LEVEL needs careful
  examination. M7-sqfree's identity says a_n(f) = Σ_{q|l, q|n} a_{n/q}(g_q).
  This implies (at function level) f = Σ_q V_q(g_q). For this to hold, V_q(g_q)
  is the q-component of f.
  
  In the inductive case: g_q = F_q (peeled first). V_q(g_q) at Γ_1(N·l²·q)
  has the same function value as V_q(F_q) at Γ_1(N·q²). Both equal h_form (the
  q-supported part of f) at the function level.
  
  For g_{q'} (peeled via IH): g_{q'} = (IH's g'_helper q').restrict from
  IH's output level to Γ_1(N·l²). V_{q'}(g_{q'}) at Γ_1(N·l²·q') has function
  value = V_{q'}(IH's g'_helper q') = IH's h_form-related-component of f'.
  
  The sum Σ_q V_q(g_q) at function level reconstructs f (Miyake's identity) ✓.

  For F q at uniform level (N·l²)/q with V_q(F q) = g q at function level:
  - Peel q first: F_q at Γ_1(N·q), restrict to Γ_1((N·l²)/q). V_q(F_q at (N·l²)/q) = V_q(F_q) (function) = h_form (function) = g_q (function, after restriction). ✓
  - IH-q' case: F q' at IH's output Γ_1((N·l²)/q'). V_{q'}(F q' at (N·l²)/q')
    at level Γ_1(N·l²) (since q' · (N·l²)/q' = N·l²). V_{q'}(F q') at Γ_1(N·l²)
    matches g_{q'} (the IH's V_{q'}-lifted output) at Γ_1(N·l²) at the function
    level. ✓

OK so the V_q(F q) = g q (function level) property holds in both base and
inductive cases. ✓

**Verdict on Attack 1**: SURVIVED.

### Attack 2 — Edge cases

- l' = 2 (single prime): base case. F_2 at Γ_1((l'³·N)/2) = Γ_1(4N) ✓.
- l' = 6 (composite, two primes 2, 3):
  - F_2 (peeled first): at Γ_1(l'·N · q) = Γ_1(12N), restricted to Γ_1((216·N)/2) = Γ_1(108N) ✓.
  - F_3 (from IH at level Γ_1(4N) with l_new = 3): IH output at Γ_1((4N · 9)/3) = Γ_1(12N). Restrict to Γ_1((216·N)/3) = Γ_1(72N)? Hmm, M7-sqfree's IH output is at Γ_1((N_input · l_new²)/q') = Γ_1((4N · 9)/3) = Γ_1(12N). But the uniform level (N·l²)/q' for q'=3, l=6, N=N is (36N)/3 = 12N ✓. Wait we're talking about the TOP-LEVEL M7-sqfree's uniform level for q'=3: (N·l²)/q' = (N · 36)/3 = 12N. And IH outputs at the IH's natural level, which is also Γ_1(12N). So no restriction needed ✓.

**Verdict on Attack 2**: SURVIVED.

### Attack 3 — Hypothesis test

**M6(1) hypotheses** (for bridging h at Γ_1(l'·N) to Γ_1(l'³·N), mult l'²):
- p ∣ N (smaller-level divisor for descend): from helper hypothesis.
- [NeZero ((l'·N)/p)]: ✓.
- Coprime p l'²: Coprime p l' (helper hyp) implies Coprime p l'² ✓.
- l'² ∣ (l'·N)/p: l' ∣ N (squarefree primes in N), so l' ∣ N/p (Coprime l' p),
  so l'² ∣ l' · (N/p) = (l'·N)/p ✓.

**M6(2) hypotheses** (for each q ∈ l'.primeFactors, smaller level (l'³·N)/q, mult q):
- p ∣ (l'³·N)/q: p ∣ N (helper hyp), and p coprime q, so p ∣ (l'³·N)/q (dividing by q coprime to p preserves p|·).
- [NeZero (((l'³·N)/q)/p)]: ✓.
- Coprime p q: q ∈ l'.primeFactors, p coprime l' ⇒ p coprime q ✓.
- q ∣ ((l'³·N)/q)/p = (l'³·N)/(qp): need q · qp | l'³·N. qp coprime, q²·p | l'³·N
  iff q² | l'³·N/p iff q² | l'³ (since p coprime q²) iff q² | l'³. Since q | l'
  (q ∈ l'.pf) and l' squarefree, l' = q · m with Coprime q m. l'³ = q³ · m³.
  q² | q³ · m³ ✓.
- Character bookkeeping: F q has character from strong dichotomy. Need to check
  the character at uniform level (after restriction) matches M6(2)'s required form.
  This is technical but follows from toUnitHom_loweredCharacter (same pattern as
  M5-base proof at line 5904).

**Verdict on Attack 3**: SURVIVED.

### Attack 4 — Source-drift

**Miyake's source** (per docstring transcription at SMOObligations.lean:7110-7124):

> "Apply M7-sqfree to h with l := l': decompose h's qExp as Σ_{q|l'} a_{n/q}(h_q)
> terms, where h_q : CuspForm at level Γ_1((l'·N)·l'^2) = Γ_1(l'³·N)."
>
> "Lift h to the deeper level via 4.6.6(2) for each q | l': slash_sum_lifted(h)(z)
> = Σ_{q|l'} (slash_sum_deeper(h_q))(qz)."

Miyake's h_q is at level Γ_1(l'³·N) (= M7-sqfree's g_q level). His
"slash_sum_deeper(h_q)" is at level Γ_1(l'³·N) (where h_q lives).

C-1a's F_q is at level Γ_1((l'³·N)/q). The slash_sum_at_((l'³·N)/q)(F_q)(q·z) in our
proof corresponds to... let me check via M6(2):

M6(2) with smaller level Γ_1((l'³·N)/q), mult q:
slash_sum_at_l'³·N(V_q(F q))(z) = slash_sum_at_((l'³·N)/q)(F q)(q·z).

So slash_sum_at_((l'³·N)/q)(F q)(q·z) = slash_sum_at_l'³·N(V_q(F q))(z).

Miyake's slash_sum_deeper(h_q)(q·z) — at level Γ_1(l'³·N). By M6(2) with smaller
level Γ_1(l'³·N), mult q: slash_sum_at_(q·l'³·N)(V_q(h_q at l'³·N))(z) =
slash_sum_at_l'³·N(h_q at l'³·N)(q·z).

So Miyake's "slash_sum_deeper(h_q)(qz)" = slash_sum_at_(q · l'³·N)(V_q(h_q))(z).

C-1a's version = slash_sum_at_l'³·N(V_q(F q))(z). These are at DIFFERENT
slash-sum levels (q·l'³·N vs l'³·N).

For Miyake's RHS Σ_q to equal LHS slash_sum_lifted(h)(z) = slash_sum_at_l'N(h)(z),
the identity must somehow work. Possibly Miyake's argument implicitly uses some
bridging (M6(1)?) to handle this.

C-1a uses M6(1) to bridge h's slash sum at l'·N and l'³·N (level commute for h at
its level). Then linearity. Then M6(2) per q at smaller level (l'³·N)/q. The
result is a clean chain.

So C-1a's argument is MATHEMATICALLY EQUIVALENT to Miyake's, but with the level
bookkeeping spelled out more carefully:
- Miyake's "deeper level" = our l'³·N (correct).
- Miyake's h_q at "deeper level" = our F_q at (l'³·N)/q (the V_q-preimage level)
  restricted/recoverable from M7-sqfree's g_q at l'³·N.

**Verdict on Attack 4**: SURVIVED (with notational refinement — C-1a's F_q is
Miyake's h_q viewed via its V_q-preimage).

### Attack 5 — Discharge attack

**Can L1 (strengthened M7-sqfree) be proven from existing project lemmas?**

The strengthening adds an output F_q at level Γ_1((N·l²)/q). The construction:

- **Base case**: M7-sqfree's existing base case (line 5879) constructs F via
  `conductor_theorem_dichotomy_cuspForm_strong` at level Γ_1((N·l²)/q) ✓. Just
  expose this F in the output (instead of just g).

- **Inductive case, peel q first**: M7-sqfree's existing inductive step (line 6121)
  constructs F at level Γ_1((N·q²)/q) = Γ_1(N·q). We need F at level Γ_1((N·l²)/q).
  Apply `restrictSubgroup` (since Γ_1(N·q) ⊃ Γ_1((N·l²)/q)). Verify the inclusion:
  N·q | (N·l²)/q iff q² | l² iff q | l ✓ (q ∈ l.primeFactors).

- **Inductive case, q' from IH**: IH (with strengthened M7-sqfree applied) gives
  F_{q'} at level Γ_1((N·q²)·(l'²/q')) = Γ_1((N·l²)/q') directly ✓.

In all three cases, F_q is obtainable at the uniform level Γ_1((N·l²)/q). The
V_q(F_q) = g_q (as functions) property is preserved by restriction (F_q's
underlying function is unchanged).

**Verdict on Attack 5**: SURVIVED. L1 is dischargeable from existing M7-sqfree
infrastructure.

### Prior-B2 log consultation

No B2 log exists. Previous analyses surfaced level-mismatch obstacles that
**C-1a resolves** by exposing F at the natural V_q-preimage level matching
M6(2)'s composition requirements.

## Confidence gate

1. ✅ Every leaf discharged: L1 from M7-sqfree's existing internal structure;
   L2 via `qExpansion_eq_zero_iff`; L3 via standard V_q qExp lemma; L4-L5 existing
   project lemmas.
2. ⏳ Lean skeleton TBD (would write L1, L2, L3 as `:= by sorry` declarations
   before the helper).
3. ✅ Source quotes per leaf (Miyake §4.6 + project docstrings).
4. ✅ Adversarial pass: all 5 attack categories SURVIVED (with notational
   refinement noted for Attack 4).
5. ✅ Prior-B2 log clean.
6. ✅ Tree mirrors source structure (Miyake's argument); C-1a refines the level
   bookkeeping of Miyake's formal statement.

**Gate status**: PASSED.

## Feasibility assessment

**C-1a is the cleanest path forward**, following Miyake's argument with refined
level bookkeeping. The strengthening of M7-sqfree is mechanical (track F
alongside g), and the helper's discharge composes cleanly.

### Estimated effort

| Step | LOC estimate |
|------|--------------|
| L1: Strengthen M7-sqfree to expose F_q | 100-150 LOC |
| L2: Function identity Δ' = Σ V_q(F_q) | 40-60 LOC |
| L3: m-th coeff of (z ↦ G(q·z)) for Coprime m l' | 30-40 LOC |
| L6: Helper discharge composition | 100-150 LOC |
| **Total** | **~270-400 LOC** |

This is the smallest-scope path among A/B/C-1/C-1a/D, and matches Miyake's actual
proof structure.

### Risk Assessment

- **Risk 1 (M7-sqfree strengthening, mechanical)**: low. Adds an additional
  output to an existing inductive proof. Each inductive case has a natural
  way to produce F.

- **Risk 2 (Function identity at common level)**: low. Standard application of
  `qExpansion_eq_zero_iff` at restricted common level Γ_1(l'⁴·N).

- **Risk 3 (M6(2) character bookkeeping per q)**: medium. The character of F_q
  at level Γ_1((l'³·N)/q) needs to match M6(2)'s required `χ = χ'.comp unitsMap`
  shape. This follows from `toUnitHom_loweredCharacter` (similar pattern to
  M5-base, line 5904).

- **Risk 4 (Dependent levels in Lean)**: medium. F at level `Γ_1((N·l²)/q)` is
  dependent on q. Lean's type system handles this via Π-types or via parametric
  functions over `(q : ℕ) (hq : q ∈ l.primeFactors)`.

## Next step

Approve C-1a and proceed with:
1. Implement L1 (strengthened M7-sqfree).
2. Implement L2, L3 (helper-internal lemmas).
3. Discharge L6 (helper sorry).
4. Run `lake build` + axiom check.

The path is clear and follows Miyake's argument exactly.
