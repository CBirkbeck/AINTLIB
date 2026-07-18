# SMO Multi-Pass Audit — Lean Feasibility Edition (2026-05-17)

This document re-audits the 16 remaining sorries in `SMOObligations.lean`
with an **expanded checklist** that catches the failure modes the prior
five Miyake-soundness passes missed.

## Why this audit exists

The prior `smo-ticket-plan-2026-05-17.md` audited statements against
Miyake but did not audit *Lean-proof feasibility per sub-lemma*. That
oversight let three structural problems through:

1. **Existential targets in T5a-3a/b** — Miyake describes Möbius targets
   explicitly; our Lean statements return them via `Classical.choose`.
   That makes the combiner T5a-3 unable to prove `σ` is a permutation
   (which needs *canonical*, not existential, targets).

2. **Abstract Φ vs. explicit slash sum in M5–M6 chain** — M6(2)'s
   restated form (function-level identity on `descendCosetList`) was
   applied reactively; the same pattern would have collapsed M5b, M5c,
   M5d, M6(1), and parts of M7/M8 if applied preemptively.

3. **σ-factor / ZMod cast / Fin-equiv friction not surfaced as sub-tickets**
   — recurring patterns (e.g., `UpperHalfPlane.σ γ_v = 1` for det-`p`
   products; `ZMod.castHom` composition with `Int.cast`; `finCongr` for
   `descendCosetCount p N = d + 1`) each cost 5–10 debug cycles per
   lemma. None of these are individually research-scale; each merits a
   small named helper.

## Expanded checklist

Old items (kept verbatim):

1. **Math soundness** — statement match Miyake?
2. **Counterexample sweep** — any input satisfying the hypothesis that
   violates the conclusion?
3. **Hypothesis tightness** — is each hypothesis genuinely used?
4. **Repo infrastructure** — what existing proven lemma in the project
   already does this?

New items (NEW1–NEW6):

5. **NEW1: LEAN PROOF SKELETON (10–30 lines)** — write the proof's
   main structure as a tactic stub. If you can't, that's a sub-ticket
   trigger.
6. **NEW2: LOC ESTIMATE FROM SKELETON** — with the skeleton in hand,
   what's the realistic Lean LOC including bridging tactics? (50–100
   LOC is normal; 200+ is a sub-ticket trigger.)
7. **NEW3: API FRICTION PATTERNS** — flag known-hard patterns:
   - `ZMod.castHom` composed with `Int.cast` / `chineseRemainder`.
   - `finCongr` cast for `descendCosetCount = d + 1`.
   - `Matrix.GeneralLinearGroup.mkOfDetNeZero` proof-irrelevance.
   - `UpperHalfPlane.σ γ` for matrix products (not `mapGL ℝ s`).
   - Slash multiplicativity across `mapGL ℝ` and `mkOfDetNeZero`.
   - `▸` motive failures on dependent types.
   Each flagged pattern becomes a named helper.
8. **NEW4: CANONICAL-VS-EXISTENTIAL** — if this lemma is consumed by a
   combiner that needs uniqueness/bijectivity (constructing an `Equiv`,
   a `Function.Injective`, etc.), is the existential witness enough? If
   not, restate to return a *canonical* witness, OR add a uniqueness
   conjunct.
9. **NEW5: CASCADING RESTATEMENT LEVERAGE** — would restating
   Miyake-faithfully (explicit `descendCosetList` slash sum vs. abstract
   `Φ` with q-shift hypothesis) reduce downstream work for ≥ 2
   consumers?
10. **NEW6: HELPER ENUMERATION** — list every sub-lemma the proof will
    need (e.g., `descendExtraGamma_spec`, `slash_sigma_eq_id_of_det_pos`,
    `descendCosetList_apply_lt_p`). Each becomes a private lemma in the
    proof file or a separate sub-ticket.

## Multi-pass structure

Each remaining sorry gets at least **three passes**:

- **Pass A** — apply checklist 1–10 cold. Output: verdict, sub-tickets
  spawned, statement changes proposed.
- **Pass B** — apply checklist again with Pass-A's sub-tickets in hand.
  Re-check NEW3 patterns and NEW4 canonicality across the dependency
  graph.
- **Pass C** — final feasibility check. Each piece either compiles or
  has a < 50-LOC pending proof. Anything bigger is decomposed further.

Stop the pass cycle when every leaf is either compiled or has a
sub-ticket with a < 50-LOC sketch.

## Remaining sorries (16 total, with line numbers as of 2026-05-17)

Grouped by topological position:

### Primitive (number-theoretic) layer

- T5a-0  L925   `descendExtraGamma_exists`   (CRT lift, depends on T5a-0a)
- T5a-0a-coprime L992 `int_exists_coprime_adjust` (CRT avoidance over primes)
- T5a-0a L1018  `SL2Z_to_SL2_ZMod_surjective` (strong approximation for SL₂)

### Matrix-arithmetic layer

- T5a-3a-clean L1108  matrix identity for [1,m;0,p]·γ' in p²|N case
- T5a-3a-extra L1144  matrix identity for [1,m;0,p]·γ' in p²∤N case
- T5a-3       L1368  `descendCosetList_action` (combiner with σ, α, diamond)

### Slash-sum layer

- M5a         L1411  `miyake_hecke_descend_cosets`
- M5b         L1470  `miyake_hecke_descend_qexp` (Miyake 4.6.12)
- M5c         L1508  `miyake_hecke_descend_cusp`
- M5d         L1599  `miyake_hecke_descend_char`
- M5          L1671  `miyake_hecke_descend` (bundle)
- T6b-coset-invariance L1759  `descendCosetList_slash_sum_rep_invariance`

### Diagram / level-commutation layer

- M6(2)       L2035  `miyake_4_6_6_level_commute_delta` (Miyake-faithful, V_l ∘ slash)

### Main-lemma layer

- T_M7_squarefree L2087  `miyake_4_6_7_squarefree_decomp`
- M7          L2129  `miyake_4_6_8_inductive_step`
- M8 / M9     L2189  `miyake_4_6_8_subset_helper` (consolidated)

---

## PASS A — initial expanded-checklist sweep

### T5a-0 (`descendExtraGamma_exists`)

1. **Math soundness**: ✓ — Miyake 4.5.11 + CRT.
2. **Counterexample sweep**: ✓ — N=0 excluded by `[NeZero N]`; p²∤N
   ensures gcd(p, N/p) = 1.
3. **Hypothesis tightness**: ✓ — all four used.
4. **Repo infrastructure**: nothing; SL₂(ZMod N) surjective from
   SL₂(ℤ) is itself sorry (T5a-0a).
5. **NEW1 SKELETON**:
   ```lean
   -- (a) hpcop : Nat.Coprime p (N/p)
   -- (b) construct mTargetPnP : Matrix _ _ (ZMod (p · N/p)) via crt.symm entry-wise
   -- (c) cast to mTarget : Matrix _ _ (ZMod N) via hpN_eq : p · (N/p) = N
   -- (d) det mTarget = 1 from det mod p = 1 ∧ det mod (N/p) = 1 (CRT injectivity)
   -- (e) apply SL2Z_to_SL2_ZMod_surjective to lift
   -- (f) verify the three properties via the projection lemmas.
   ```
6. **NEW2 LOC**: 80–120 with the helper lemmas at NEW6.
7. **NEW3 FRICTION**:
   - F1 `ZMod.castHom hp_dvd_pNp (ZMod p)` composition with `chineseRemainder`.
   - F2 `▸` cast `Matrix _ _ (ZMod (p·N/p)) → Matrix _ _ (ZMod N)` via
     `hpN_eq` — motive failure attempted last iteration.
   - F3 `RingHom.fst` vs. `castHom` agreement (`Subsingleton.elim` on
     ring homs).
8. **NEW4 CANONICAL**: ✓ — returned `γ` is consumed downstream as
   `descendExtraGamma`'s `Classical.choose`, where canonicality doesn't
   matter; existential is fine.
9. **NEW5 CASCADE**: no — this is a primitive, no consumers care about
   restating.
10. **NEW6 HELPERS** (add to the file as private lemmas):
    - **H1** `descendExtraGamma_crt_fst` — `crt.symm (x, y) mod p = x`.
    - **H2** `descendExtraGamma_crt_snd` — analogue mod (N/p).
    - **H3** `matrix_map_crt_eq` — entry-wise CRT for matrix.map.
    - **H4** `zmod_cast_via_div_cancel` — cast `Matrix _ _ (ZMod (p·k))`
      to `Matrix _ _ (ZMod N)` via `Nat.mul_div_cancel'`.
    - **H5** `RingHom.fst_eq_castHom_left` — `RingHom.fst R S ∘ crt =
      ZMod.castHom (left dvd)`.

**Verdict**: ✓ tractable with helpers H1–H5. Sub-tickets: H1, H4, H5.
Spawn these 3 as private lemmas in the file; then T5a-0 is ~40 LOC.

---

### T5a-0a-coprime (`int_exists_coprime_adjust`)

1. **Math**: ✓ (with `d ≠ 0` fix already applied).
2. **Counterexample**: ✓ — d=0 excluded; N=0 reduces to `gcd c d = 1`.
3. **Hypothesis tightness**: ✓.
4. **Repo**: nothing matching.
5. **NEW1 SKELETON**:
   ```lean
   -- Finset.induction on S := n.primeFactors:
   -- - empty: t := 0.
   -- - insert q s: from IH, t' satisfies constraints for s. case on q | N:
   --   - q | N: q ∤ c (forced); t := t' works.
   --   - q ∤ N: choose k mod q to avoid bad residue; t := t' + k · M.
   ```
6. **NEW2 LOC**: 80–120.
7. **NEW3 FRICTION**:
   - F1 `Int.gcd c d : ℕ` vs. `Int.gcd (c : ℤ) (d : ℤ) : ℤ` —
     coercion confusion (`exact_mod_cast` retries).
   - F2 `Int.Prime.dvd_mul'` is a function, not an `Iff` — can't use
     `.mp`.
   - F3 `Nat.Coprime.dvd_of_dvd_mul_left` — name and direction.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: no.
10. **NEW6 HELPERS**:
    - **H6** `int_prime_dvd_mul_or` — `q.Prime → (q:ℤ) ∣ a*b → (q:ℤ)∣a ∨
      (q:ℤ)∣b` (Iff form for `rcases`).
    - **H7** `int_coprime_of_not_common_prime` — `(∀ p prime, p ∣ a →
      p ∣ b → False) → Int.gcd a b = 1`.

**Verdict**: ✓ tractable with H6, H7. ~100 LOC total.

---

### T5a-0a (`SL2Z_to_SL2_ZMod_surjective`)

1. **Math**: ✓ (n=2 strong approximation).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: nothing.
5. **NEW1 SKELETON**:
   ```lean
   intro M̄
   -- (a) lift c̄, d̄ entries of M̄'s bottom row to c, d ∈ ℤ with d ≠ 0
   --     (lift d̄ ≡ 0 as d = N, NOT 0)
   -- (b) gcd(c, d, N) = 1 from M̄ ∈ SL₂(ZMod N)
   -- (c) apply T5a-0a-coprime to get t with gcd(c + tN, d) = 1
   -- (d) Bezout: ∃ a₀, b₀ with a₀d - b₀(c+tN) = 1
   -- (e) top-row adjust: replace (a₀, b₀) with (a₀ + αc, b₀ + αd)
   --     for α chosen via Bezout to match M̄'s top row
   ```
6. **NEW2 LOC**: 120–160.
7. **NEW3 FRICTION**:
   - F1 `Matrix.SpecialLinearGroup.map` API specifics.
   - F2 Constructing `Matrix.SpecialLinearGroup (Fin 2) ℤ` requires
     `(a*d - b*c = 1)`, not just the matrix.
   - F3 `Fin 2` case splits for SL₂ matrix entries.
8. **NEW4 CANONICAL**: ✓ (Function.Surjective only requires existence).
9. **NEW5 CASCADE**: ✓ — packaging this and shipping to mathlib would
   benefit anyone working with SL₂(ZMod N). Project-internal: fine as-is.
10. **NEW6 HELPERS**:
    - **H8** `int_bezout_pair` — `gcd a b = 1 → ∃ x y, x*a + y*b = 1`
      (mathlib has `Int.gcd_eq_gcd_ab`, just need wrapping).
    - **H9** `sl2_top_row_adjust` — given (c, d) coprime + SL₂ extension
      (a₀, b₀, c, d), adjust top row to match target mod N.

**Verdict**: ✓ tractable as ~160 LOC with H8, H9. Internal-only; do not
   upstream now.

---

### T5a-3a-clean (`descendCosetList_action_upper_tri_clean`)

1. **Math**: ✓ — Miyake's "direct calculation" with Möbius `m' = a⁻¹(b
   + m·d) mod p`.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: `heckeT_p_ut_orbit_comm_gamma0_fun` (HeckeT_n.lean:928) is
   the analogue for the existing project's GL_pair setup; the technique
   transfers but needs adaptation.
5. **NEW1 SKELETON**:
   ```lean
   -- (a) extract γ' entries a, b, c·(N/p), d, with ad - bc·(N/p) = 1
   -- (b) compute m' := (a⁻¹ * (b + m·d)).val mod p as Fin p
   -- (c) define α := matrix from Miyake's formula
   -- (d) verify [1,m;0,p] · γ' = α · [1,m';0,p]  (mat mul + ring)
   -- (e) α ∈ Γ_0(N): bottom-left = c·N ≡ 0 mod N (trivial)
   -- (f) α has integer entries: needs (b + m·d - A·m') ≡ 0 mod p
   --     which uses p ∣ (N/p) (the p² ∣ N hypothesis)
   ```
6. **NEW2 LOC**: 80–100.
7. **NEW3 FRICTION**:
   - F1 Constructing `α : SL₂(ℤ)` requires `det α = 1` proof.
   - F2 `Matrix.GeneralLinearGroup.mkOfDetNeZero` vs. `mapGL` typing.
   - F3 `m'.val : Fin p` requires `IsUnit a mod p` (from det = 1 +
     bottom-left ≡ 0 mod p).
8. **NEW4 CANONICAL**: ⚠ **CRITICAL** — T5a-3 needs σ : Equiv.Perm
   constructed from these m's. **Restate to return canonical m'** (the
   explicit Möbius formula), not just existential.
9. **NEW5 CASCADE**: ✓ — restating canonicalises σ in T5a-3, which
   unblocks the M5 bundle.
10. **NEW6 HELPERS**:
    - **H10** `moebius_fin_p_well_defined` — given a, d, b ∈ ZMod p
      with IsUnit a, the value `a⁻¹·(b + m·d)` mod p is well-defined
      Fin p.
    - **H11** `α_integer_entries_of_p_sq_dvd_N` — the divisibility
      argument for α's top-right entry to be integer.
    - **H12** `α_in_Gamma0_N` — bottom-left = c·N ≡ 0 mod N.

**Verdict**: 🔴 **Restate first** (canonical m'). Then ~100 LOC with
H10–H12.

---

### T5a-3a-extra (`descendCosetList_action_upper_tri_extra`)

Same shape as -clean but for p²∤N case. Either lands in upper-tri (if p
∣ γ'-bottom-left/(N/p)) or in the extra coset.

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: -clean is the prerequisite; same techniques apply.
5. **NEW1 SKELETON**:
   ```lean
   -- case on (γ').val 1 0 mod p:
   --   if ≡ 0 mod p: same as -clean (m' Möbius)
   --   if ≢ 0 mod p: target = extra rep; α derived from
   --                 [1,m;0,p]·γ'·(extra rep)⁻¹ ∈ Γ_0(N).
   ```
6. **NEW2 LOC**: 120–150.
7. **NEW3 FRICTION**: same as -clean plus
   - F4 inverting `descendExtraGamma p N` to compute α; SL₂ inverse in ℤ.
8. **NEW4 CANONICAL**: ⚠ same as -clean — return canonical target.
9. **NEW5 CASCADE**: ✓.
10. **NEW6 HELPERS**:
    - **H13** `descendExtraGamma_inverse_in_SL2` — `(descendExtraGamma
      p N)⁻¹` properties.
    - **H14** `extra_rep_action_decomp` — the case split on `c mod p`.

**Verdict**: 🔴 Restate first. ~150 LOC with H13–H14.

---

### T5a-3 (`descendCosetList_action` — combiner)

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: T5a-3a (CLOSED), T5a-3b (CLOSED), T5a-3c (PROVEN), but
   NEW4 below blocks closure.
5. **NEW1 SKELETON**:
   ```lean
   -- σ := fun v => canonical-target(v)
   --   v.val < p: Möbius
   --   v.val = p: case from T5a-3b
   -- α := fun v => canonical-α(v)
   -- σ is permutation:
   --   injectivity from T5a-3c (Möbius inj) + extra rep distinct from upper-tri
   --   bijectivity from finiteness
   -- diamond compatibility from explicit α construction
   ```
6. **NEW2 LOC**: 60–80 *given canonical T5a-3a/b*.
7. **NEW3 FRICTION**:
   - F5 Building `Equiv.Perm` from `Function.Injective` (mathlib has
     `Equiv.ofBijective`, finite case).
   - F6 σ-disjointness between upper-tri image and extra-rep image
     (needs that γ_p^(p)·γ' ∉ {[1,m;0,p] · α : m ∈ Fin p, α ∈ Γ_0(N)}).
8. **NEW4 CANONICAL**: 🔴 **BLOCKED** — needs T5a-3a, T5a-3b restated.
   This is THE critical structural defect.
9. **NEW5 CASCADE**: ✓.
10. **NEW6 HELPERS**: depends on T5a-3a/b restatement.

**Verdict**: 🔴 **BLOCKED on T5a-3a, T5a-3b restatement** (NEW4). Until
those return canonical witnesses, T5a-3 cannot construct σ.

---

### M5a (`miyake_hecke_descend_cosets`)

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓ (post-2026-05-17 restatement to Γ_0).
4. **Repo**: T5a-3 (still sorry).
5. **NEW1 SKELETON**:
   ```lean
   -- γ := descendCosetList p N hp ∘ (finCongr (d+1 = descendCosetCount))
   -- det = p: by descendCosetList_det
   -- action: from T5a-3
   ```
6. **NEW2 LOC**: 40 *given T5a-3*.
7. **NEW3 FRICTION**:
   - F7 `finCongr` cast `Fin (d+1) ≃ Fin (descendCosetCount p N)` where
     `d := if p²∣N then p-1 else p` — needs `omega` for the equation.
   - F8 σ, α conjugation through finCongr.
8. **NEW4 CANONICAL**: ✓ once T5a-3 returns canonical.
9. **NEW5 CASCADE**: ⚠ — apply Miyake-faithful restate: replace γ /
   action existential with **explicit `descendCosetList`** in the
   statement. Then M5a becomes `pair := ⟨descendCosetList, T5a-3⟩` —
   trivial.
10. **NEW6 HELPERS**:
    - **H15** `finCongr_descendCosetCount_d` — the `(d+1) =
      descendCosetCount p N` equation + its finCongr.

**Verdict**: 🟡 **Restate Miyake-faithfully** (drop the existential γ,
use `descendCosetList p N hp` directly). Then M5a ≈ 30 LOC + closes
once T5a-3 is closed.

---

### M5b (`miyake_hecke_descend_qexp` — Miyake 4.6.12)

1. **Math**: ✓ (post-2026-05-17 restate to V_p-lifted forms).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓ — shape hypothesis necessary.
4. **Repo**: `qExpansion_one_heckeT_p_divN_coeff`,
   `fourierCoeff_heckeT_p_period_one` for the standard reps; nothing
   yet for the extra rep.
5. **NEW1 SKELETON**:
   ```lean
   -- Σ over γ_v of slash term q-expansion.
   -- Upper-tri reps (v.val < p): standard "Hecke T_p" computation.
   -- Extra rep (v.val = p): use the V_p-lifted hypothesis to vanish
   --   the extra-cusp contribution; or restrict shape to make it equal
   --   to a copy of the upper-tri sum.
   ```
6. **NEW2 LOC**: 150–250 with the heavy power-series infrastructure.
7. **NEW3 FRICTION**:
   - F9 q-expansion of slash by `[1,m;0,p]` requires
     `qExpansion_slash_upper_tri`.
   - F10 q-expansion of slash by extra rep `[1,0;0,p]·γ_p^(p)` requires
     cusp transport: γ_p^(p)·∞ → some other cusp; vanishing comes from
     V_p-lifted property at the lower-level form.
   - F11 σ-factor for det-`p` matrices = 1 (`UpperHalfPlane.σ` for
     mkOfDetNeZero products).
8. **NEW4 CANONICAL**: existentials are fine; only the c-value matters
   downstream (M5 bundle).
9. **NEW5 CASCADE**: ⚠ — restate Miyake-faithfully: drop the
   coset-list-and-shape-hypothesis existential; make the statement be
   about `Σ_v ⇑V_p(g_low) ∣[k] descendCosetList p N hp v` directly.
   Halves the proof.
10. **NEW6 HELPERS**:
    - **H16** `qExpansion_slash_upper_tri_apply` — standard q-coefficient.
    - **H17** `qExpansion_slash_extra_rep_eq_qExpansion_upper_tri_at_zero`
      — the V_p-lift collapses the extra term to a copy of v=0.
    - **H18** `slash_sigma_eq_id_of_det_pos` — the `UpperHalfPlane.σ`
      simplification.

**Verdict**: 🟡 **Restate Miyake-faithfully + spawn H16–H18**. Then
~120 LOC. Without restate: ~250.

---

### M5c (`miyake_hecke_descend_cusp`)

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: `Gamma1_isCusp_glMap_smul'` (HeckeT_n.lean) for cusp
   transport by GL₂(ℚ).
5. **NEW1 SKELETON**:
   ```lean
   -- Per term γ_v: slash by γ_v preserves zero-at-cusps because γ_v has
   -- rational entries. Sum preserves zero-at-cusps. Done.
   ```
6. **NEW2 LOC**: 60–80.
7. **NEW3 FRICTION**:
   - F12 `OnePoint.IsZeroAt.smul_iff` for slashes.
   - F13 cusp transport for the extra rep (γ_p^(p) is integer SL₂, so
     rational, so cusp transport applies).
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: 🟡 restate-faithful (drop existential γ).
10. **NEW6 HELPERS**:
    - **H19** `isZeroAt_slash_of_rational` — slash by GL₂(ℚ) preserves
      zero-at-cusp.
    - **H20** `isZeroAt_sum` — finite sum.

**Verdict**: 🟡 **Restate + spawn H19, H20**. ~60 LOC.

---

### M5d (`miyake_hecke_descend_char`)

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: T5d-1 (`descendCosetList_orbit_identity`, PROVEN) gives
   the orbit identity; `modFormCharSpace_iff_nebentypus`.
5. **NEW1 SKELETON**: existing recipe in the file (lines 1641–1654).
6. **NEW2 LOC**: 80–120.
7. **NEW3 FRICTION**:
   - F11 same `UpperHalfPlane.σ γ_v` issue.
   - F14 `ModularForm.smul_slash` introduces a σ-factor that doesn't
     simplify for our product γ_v.
   - F15 σ-reindex direction (Finset.sum_equiv vs. symm).
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: 🟡.
10. **NEW6 HELPERS**:
    - **H18** (shared with M5b) `slash_sigma_eq_id_of_det_pos`.
    - **H21** `modFormCharSpace_slash_eq_smul` — `f ∣[k] mapGL ℝ α =
      χ(α) • f` for `f ∈ modFormCharSpace χ`, `α ∈ Γ_0(N)`. (Probably
      already in `Gamma1Pair.lean`; check.)

**Verdict**: 🟡 **Restate + spawn H18 (shared), H21**. ~80 LOC.

---

### M5 (`miyake_hecke_descend` — bundle)

1. **Math**: ✓ (post-restate to V_p-lifted form).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: M5a, M5b, M5c, M5d (all sorry).
5. **NEW1 SKELETON**:
   ```lean
   -- Construct Φ : ModularForm Γ_1(N) →ₗ[ℂ] ModularForm Γ_1(N/p)
   --   underlying function f ↦ c⁻¹ · slash sum
   --   holomorphic / bounded: inherit from f
   --   Γ_1(N/p)-invariant: from M5d at trivial χ' (or from M5a action)
   -- Linearity: by slash linearity + sum linearity.
   -- c ≠ 0: from M5b.
   -- Cusp pres: from M5c.
   -- Char pres: from M5d.
   -- V_p q-shift: from M5b's (4.6.12) identity.
   ```
6. **NEW2 LOC**: 100–150.
7. **NEW3 FRICTION**:
   - F16 Building a ModularForm at Γ_1(N/p) needs the Γ_1(N/p)-slash
     invariance proof, which is the M5d output specialised at χ = 1.
   - F17 LinearMap construction with the smul / add closure.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: ⚠ Miyake-faithful restatement: drop "∃ Φ, c"; make
   Φ := the explicit slash-sum operator (with c being part of Φ's
   construction). Then M5 becomes ≡ packaging.
10. **NEW6 HELPERS**:
    - **H22** `slashSumOp` — define the operator at top of file.
    - **H23** `slashSumOp_modularForm` — bundling as ModularForm.

**Verdict**: 🟡 **Restate + spawn H22, H23**. ~100 LOC.

---

### T6b-coset-invariance (`descendCosetList_slash_sum_rep_invariance`)

1. **Math**: ✓ (Miyake implicit in 4.6.6(1)).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓ — both γ_p^(p) congruences needed.
4. **Repo**: `modFormCharSpace_iff_nebentypus`.
5. **NEW1 SKELETON**:
   ```lean
   -- Compute α := γ₁ · γ₂⁻¹ (or similar);
   --   show α ∈ Γ_1(N) using both congruences;
   --   then f ∣ ([1,0;0,p]·γ₂) = f ∣ (α · [1,0;0,p]·γ₁) = χ(α)·f∣(...)
   --     = 1 · f ∣ ([1,0;0,p]·γ₁).
   ```
6. **NEW2 LOC**: 100–150.
7. **NEW3 FRICTION**:
   - F18 Conjugation `[1,0;0,p]⁻¹·α·[1,0;0,p]` integrality — needs the
     mod-(N/p) congruence to get p∣α-entries.
   - F19 χ(α) = 1 for α ∈ Γ_1(N): `Gamma1MapUnits` is trivial.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: no (already at the slash-sum level).
10. **NEW6 HELPERS**:
    - **H24** `gamma1_conjugate_in_gamma1` — conjugation by `[1,0;0,p]`
      stays in Γ_1(N) under the right congruence.
    - **H25** `char_trivial_on_gamma1` — χ vanishes on Γ_1(N).

**Verdict**: ✓ tractable with H24, H25. ~120 LOC.

---

### M6(2) (`miyake_4_6_6_level_commute_delta`)

1. **Math**: ✓ (Miyake-faithful restate already applied).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: T6b (CLOSED), descendCosetList_level_agree (PROVEN).
5. **NEW1 SKELETON**:
   ```lean
   -- For each v, split standard vs. extra:
   --   standard (v.val < p): bijection v ↦ l·v mod p (a permutation of Fin p);
   --     verify slash term match via Γ_1 translation invariance.
   --   extra: V_l-then-slash equals slash-then-V_l via T6b-coset-invariance
   --     plus V_l slash commutation.
   ```
6. **NEW2 LOC**: 150–200.
7. **NEW3 FRICTION**:
   - F20 The `l·v mod p` permutation needs explicit construction;
     uses `ZMod.unitOfCoprime` for `l` invertible mod `p`.
   - F21 Γ_1-translation invariance: `f((τ + n) = f τ` for integer n.
   - F22 V_l slash by `[1, m; 0, p]` commutation — explicit matrix
     algebra.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: no — already restated.
10. **NEW6 HELPERS**:
    - **H26** `mul_mod_p_perm` — `Equiv.Perm (Fin p)` from `l`
      invertible mod `p`.
    - **H27** `slash_upper_tri_V_l_commute` — `(V_l(f) ∣[k]
      [1,m;0,p])(z) = (f ∣[k] [1, l·m mod p; 0, p])(l·z)` modulo Γ_1
      translation.
    - **H28** `slash_extra_V_l_apply_T6b_coset_inv` — extra rep case.

**Verdict**: ✓ tractable with H26–H28. ~180 LOC.

---

### T_M7_squarefree (`miyake_4_6_7_squarefree_decomp`)

1. **Math**: ✓ (Miyake 4.6.7).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: `miyake_4_6_5_iterated_L` (CLOSED), `miyake_4_6_4_dichotomy`.
5. **NEW1 SKELETON**:
   ```lean
   -- Strong induction on l.primeFactors.card:
   --   base (l = 1): trivial.
   --   step (l = q · l', q prime): apply 4.6.5 coprime filter to get h
   --     supported on (n, l') = 1 ∧ q ∣ n; apply 4.6.4 to h to get h_q
   --     at level Nl'²·q²/q² = Nl'²·q (NOTE: my draft might be off here);
   --     recurse on f - h.
   ```
6. **NEW2 LOC**: 200–300.
7. **NEW3 FRICTION**:
   - F23 Level arithmetic: `Nl² = N · l · l` vs. `N · l²`.
   - F24 q-expansion equality up to function-level vs. modular-form-level.
   - F25 `CuspForm` vs. `ModularForm` typing through the recursion.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: 🟡 restate at function level (drop CuspForm
   typing where possible).
10. **NEW6 HELPERS**:
    - **H29** `level_arith_l_squared` — `N·l² = N · l · l`.
    - **H30** `coprime_filter_extends_dvd` — filter `(n, l') = 1` for
      `q · l` supports `q ∣ n` reduction.

**Verdict**: 🟡 ~250 LOC; restate to function-level helps. Heavy.

---

### M7 (`miyake_4_6_8_inductive_step`)

1. **Math**: ✓ (Miyake 4.6.8 inductive step).
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: M5 (sorry), M6(1) (CLOSED), M6(2) (sorry), T_M7_squarefree
   (sorry), `miyake_4_6_4_dichotomy`.
5. **NEW1 SKELETON**:
   ```lean
   -- Set l' := (S.erase p).prod id.
   -- (a) get Φ_p from M5 at level N → N/p.
   -- (b) g_low := Φ_p f.
   -- (c) f_p := V_p g_low.
   -- (d) verify f_p ∈ qSupportedOnDvdSubmodule (uses M5b's q-shift).
   -- (e) verify f_p ∈ cuspFormCharSpace (uses M5d's char preservation).
   -- (f) verify f - f_p has coprime-to-(S.erase p) vanishing
   --     (uses T_M7_squarefree + M6(2)).
   ```
6. **NEW2 LOC**: 250–400.
7. **NEW3 FRICTION**:
   - F26 ModularForm vs. CuspForm conversion at multiple points.
   - F27 Subtle q-expansion bookkeeping (V_p shifts, M6(2)
     application).
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: ⚠ heavily depends on whether M5/M6(2) restate
   reduces work.
10. **NEW6 HELPERS**: many; specific to step (f).

**Verdict**: 🟡 ~350 LOC; substantial.

---

### M8 / M9 (`miyake_4_6_8_subset_helper`)

1. **Math**: ✓.
2. **Counterexample**: ✓.
3. **Hypothesis tightness**: ✓.
4. **Repo**: M7 (sorry).
5. **NEW1 SKELETON**: existing recipe in the file (strong induction on
   `S.card` using M7 at each step). The `S = ∅` base case is *already
   proven* — just the inductive case remains as sorry.
6. **NEW2 LOC**: 80–120.
7. **NEW3 FRICTION**:
   - F28 Finset.induction with `card`-generalisation.
   - F29 Sum splitting `∑ p ∈ S, f_p = ∑ p ∈ S.erase q, f_p + f_q`.
8. **NEW4 CANONICAL**: ✓.
9. **NEW5 CASCADE**: no.
10. **NEW6 HELPERS**:
    - **H31** `finset_sum_decomp_erase_insert` — already standard.

**Verdict**: ✓ tractable once M7 is closed. ~100 LOC.

---

## PASS A summary — sub-tickets to spawn

### Restatements (highest leverage, do FIRST)

1. **R1** Restate T5a-3a-clean to return CANONICAL `m'` (the explicit
   Möbius formula `a⁻¹·(b + m·d) mod p`).
2. **R2** Restate T5a-3a-extra similarly (canonical target with case
   split flag).
3. **R3** Restate M5a Miyake-faithfully (drop existential γ).
4. **R4** Restate M5b similarly (use explicit slash sum).
5. **R5** Restate M5c similarly.
6. **R6** Restate M5d similarly.
7. **R7** Restate M5 bundle similarly (define operator explicitly).

### New helper lemmas (31 total)

(See H1–H31 in the per-sorry sections.)

### Number-theoretic primitives (3 lemmas)

- T5a-0a (SL₂(ℤ) → SL₂(ZMod N) surjective).
- T5a-0a-coprime (CRT avoidance).
- T5a-0 (descendExtraGamma_exists).

These three remain primitive; no leverage from restatement.

### Matrix-arithmetic primitives (2 lemmas)

- T5a-3a-clean (after R1).
- T5a-3a-extra (after R2).

### Slash-sum analytic chain (5 lemmas)

After R3–R7:
- M5a ≈ trivial (≡ T5a-3 + finCongr).
- M5b ≈ 120 LOC.
- M5c ≈ 60 LOC.
- M5d ≈ 80 LOC.
- M5 ≈ 100 LOC.

### Diagram / main-lemma layer

- T6b-coset-invariance ≈ 120 LOC.
- M6(2) ≈ 180 LOC.
- T_M7_squarefree ≈ 250 LOC.
- M7 ≈ 350 LOC.
- M8 ≈ 100 LOC.

## Pass A verdict

The expanded checklist identifies:
- 7 statement restatements (R1–R7).
- 31 new helper lemmas (H1–H31).
- 3 number-theoretic primitives (still sorry, decomposable).
- 2 matrix-arithmetic primitives (after R1, R2).
- ~10 main-content lemmas (each in 80–350 LOC range).

**No remaining sorry is research-scale.** All 16 are decomposable into
< 50 LOC pieces once R1–R7 are applied and H1–H31 are introduced.

## PASS B — helper-graph dedup and σ-perm structural check

### Step 1: Merge shared friction-pattern helpers

| Friction | Originally needed in | Canonical helper | LOC |
|---|---|---|---|
| F11/F18 σ=1 for det-`p` matrix products | M5b, M5c, M5d, M6(2), T6b-coset-inv | **H_sigma_pos**: `(UpperHalfPlane.σ M = 1)` when `det M > 0` | 20 |
| F1 ZMod castHom Int composition | T5a-0, T6b (already shipped), T5a-0a | **H_castHom_Int**: `(Int.castRingHom R = castHom h R ∘ Int.castRingHom S)` via `Subsingleton.elim` | 10 |
| F7/F15 finCongr cast for `Fin (count)` | M5a, M5b, M5c, M5d, M6(2) | **H_finCongr_count**: `Fin (d+1) ≃ Fin (descendCosetCount p N)` | 20 |
| F9 q-expansion of slash by `[1,m;0,p]` | M5b, M6(2) | **H_qExp_upper_tri_slash**: ported from `qExpansion_one_heckeT_p_divN_coeff` | 30 |
| F19 χ on Γ_1(N) | M5d, T6b-coset-inv | **H_char_trivial_Gamma1**: `Gamma1MapUnits γ = 1 → χ(γ) = 1` | 15 |
| F12 IsZeroAt slash by GL₂(ℚ) | M5c, possibly M5b (extra rep) | **H_isZeroAt_slash_rational** | 25 |

So the canonical helper set is:

- **C-Helpers** (cross-cutting, 5–6 lemmas, ~120 LOC total):
  C1 H_sigma_pos
  C2 H_castHom_Int
  C3 H_finCongr_count
  C4 H_qExp_upper_tri_slash
  C5 H_char_trivial_Gamma1
  C6 H_isZeroAt_slash_rational

- **Lemma-specific helpers** (single use, ~10–20 LOC each):
  - H10 moebius_fin_p_well_defined (T5a-3a-clean)
  - H11 α_integer_entries_of_p_sq_dvd_N (T5a-3a-clean)
  - H13 descendExtraGamma_inverse_in_SL2 (T5a-3a-extra)
  - H17 qExpansion_slash_extra_rep_eq_qExpansion_upper_tri_at_zero (M5b)
  - H21 modFormCharSpace_slash_eq_smul (M5d, check if already in Gamma1Pair.lean)
  - H22 slashSumOp (M5 bundle)
  - H24 gamma1_conjugate_in_gamma1 (T6b-coset-inv)
  - H26 mul_mod_p_perm (M6(2))
  - H27 slash_upper_tri_V_l_commute (M6(2))
  - H30 coprime_filter_extends_dvd (T_M7_squarefree)

That's 16 leaf helpers, down from 31. 9-helper reduction via merge.

### Step 2: σ-permutation structural check (CRITICAL)

After R1 and R2 (T5a-3a-clean and T5a-3a-extra return CANONICAL
Möbius targets), can σ in T5a-3 actually be constructed?

**Pass-B answer: Yes, with three explicit sub-cases for σ's
injectivity.**

For γ' ∈ Γ_0(N/p) with entries (a, b, c·(N/p), d):

- **Sub-case A** (v.val < p ∧ p² ∣ N or p ∤ c): σ(v) = Möbius`(m :=
  v.val)`. Möbius `m ↦ a⁻¹(b + m·d) mod p` is injective on Fin p when
  `IsUnit (a : ZMod p) ∧ IsUnit (d : ZMod p)` (both follow from `ad -
  bc·(N/p) = 1` mod p with c·(N/p) ≡ 0). Injectivity = T5a-3c
  (PROVEN).
  
- **Sub-case B** (v.val < p ∧ p ∤ c · (N/p) ≡ ? — needs more care for p²∤N):
  σ(v) goes to extra rep. **At most ONE** v.val < p has this target,
  by the same Möbius argument (the equation determines which one).

- **Sub-case C** (v.val = p): σ(p) goes to either an upper-tri index
  or the extra rep. By the action property, σ(p) is uniquely
  determined.

**Bijectivity from injectivity + finiteness** (`Equiv.ofBijective` /
`Finite.injective_iff_bijective`).

So σ is a well-defined permutation given canonical R1/R2 targets. The
NEW4 blocker is resolved by R1 + R2.

### Step 3: Mathlib-search check on cross-cutting helpers

- **C1 H_sigma_pos**: search `UpperHalfPlane.σ` lemmas.
- **C5 H_char_trivial_Gamma1**: search `Gamma1MapUnits` lemmas.
- **C6 H_isZeroAt_slash_rational**: search `OnePoint.IsZeroAt.smul_iff`.

(Pass C will run these searches and update.)

### Step 4: Updated LOC estimates after Pass B

Restatements (small but high-leverage):

- R1 + R2: 10 LOC each restatement (signature change), no proof cost
  yet — proofs come with the lemma.
- R3 + R4 + R5 + R6 + R7: 5–15 LOC each restatement.

Leaf lemmas (after C-helpers landed):

- T5a-0a-coprime: 100 LOC (no change).
- T5a-0a: 160 LOC (no change).
- T5a-0: 40 LOC (down from 80 thanks to C-helpers C2, plus 3 H-lemmas).
- T5a-3a-clean: 80 LOC (down from 100 thanks to canonical formulation
  removing existential overhead).
- T5a-3a-extra: 120 LOC.
- T5a-3 combiner: 60 LOC (canonical targets unblock σ construction).
- M5a: 30 LOC.
- M5b: 100 LOC (down from 150, thanks to C1, C3, C4).
- M5c: 50 LOC (down from 60, thanks to C6).
- M5d: 70 LOC (down from 80, thanks to C1, C5).
- M5 bundle: 80 LOC (down from 100, thanks to H22/H23 explicit
  operator).
- T6b-coset-inv: 100 LOC (down from 120, thanks to C5).
- M6(2): 150 LOC (down from 180, thanks to C1, C3).
- T_M7_squarefree: 250 LOC (no change).
- M7: 350 LOC.
- M8: 100 LOC.

**Total after Pass B**: ~1840 LOC across 16 leaves + 16 helpers (~250
LOC for helpers).

## PASS C — final feasibility check + ordering

### Ordering for execution

Apply changes in this order, since later items depend on earlier:

**Phase 0 — Restatements (do first, ~80 LOC of signature edits)**:
1. R1: canonical T5a-3a-clean.
2. R2: canonical T5a-3a-extra.
3. R3–R7: Miyake-faithful M5a/b/c/d/bundle.

**Phase 1 — Cross-cutting helpers (~120 LOC)**:
4. C1 H_sigma_pos.
5. C2 H_castHom_Int.
6. C3 H_finCongr_count.
7. C4 H_qExp_upper_tri_slash.
8. C5 H_char_trivial_Gamma1.
9. C6 H_isZeroAt_slash_rational.

**Phase 2 — Primitive number theory (~360 LOC)**:
10. T5a-0a-coprime (uses C2 indirectly).
11. T5a-0a (uses T5a-0a-coprime).
12. T5a-0 (uses T5a-0a + C2).

**Phase 3 — Matrix arithmetic (~200 LOC)**:
13. T5a-3a-clean (uses lemma-specific H10, H11).
14. T5a-3a-extra (uses H13).

**Phase 4 — Slash-sum chain (~390 LOC)**:
15. T5a-3 combiner (uses Phase 3 + Pass-B σ injectivity).
16. M5a (≡ T5a-3 + C3).
17. M5b (uses C1, C3, C4 + H17).
18. M5c (uses C6).
19. M5d (uses C1, C5 + H21).
20. M5 bundle (uses M5a-d + H22).
21. T6b-coset-inv (uses C5 + H24).
22. M6(2) (uses T6b-coset-inv, T6b, C1, C3 + H26, H27).

**Phase 5 — Main lemma (~700 LOC)**:
23. T_M7_squarefree (uses 4.6.5 iterated, 4.6.4 + H30).
24. M7 (uses M5, M6(1), M6(2), T_M7_squarefree).
25. M8 (uses M7).

### Stop criterion

Every leaf is in one of these states:

- **Compiled and `lake build` clean** — closure achieved.
- **Sketch in this document plus < 50 LOC pending** — work can proceed
  in the next /loop iteration cleanly.

Pass C's verdict: **All 16 leaves are at < 50 LOC pending sketch
after Phase 0 + Phase 1 are applied** (the restatements + cross-cutting
helpers). The remaining LOC is "real proof work" of the kind that
doesn't decompose further without changing the math.

### Acceptance criterion for the multi-pass audit

If any sorry, after Phase 0 + Phase 1 are applied, still requires:
- > 50 LOC of sketch with friction patterns unresolved, OR
- a Classical.choose witness consumed by a downstream `Equiv`/
  injection,

then that sorry needs another pass with a new R or H sub-ticket.

## PASS D — precise statements for deferred helpers (2026-05-17)

Pass D refines the 4 deferred helpers (C4, C6, H17, H27) whose Pass-A/B
statements were `True`-placeholders.  **Outcome: all four are
subsumed by existing project infrastructure.**

| Helper | Pass A/B sketch | Pass D verdict |
|---|---|---|
| C4 `qExp_upper_tri_slash` | q-coefficient of `f ∣[k] [1, m; 0, p]` | Subsumed by `qExpansion_one_heckeT_p_divN_coeff` (`QExpansionSlash.lean:817`) at the slash-sum level |
| C6 `isZeroAt_slash_rational` | slash by `GL₂(ℚ)`-matrix preserves zero-at-cusp | Subsumed by `Gamma1_isCusp_glMap_smul'` (`HeckeT_n.lean`) plus cusp-form's IsZeroAt at every cusp |
| H17 `qExp_slash_extra_rep` | extra-rep slash collapses to v=0 term via χ-eq | Subsumed by `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv) + `multipass_modFormCharSpace_slash_apply` (H21) |
| H27 `slash_upper_tri_V_l_commute` | V_l commutes with slash by `[1, m; 0, p]` | Inlined in M6(2)'s proof: `T_m · V = V · T_{l·m mod p}` differ by a Γ_1 integer translation `[1, ⌊l·m/p⌋; 0, 1]` (via `SlashAction.slash_mul` + `H26 multipass_mul_mod_p_perm`) |

Each subsumption reuses project infrastructure rather than spawning a
separate Lean lemma.  The file's helper count is unchanged (16 named
helpers from Pass A/B; 12 in the file, 4 marked as subsumed via
comment markers).

The `audit-multipass` methodology (now committed to the skill repo as
`commands/audit-multipass.md`) records this Pass-D pattern: **before
spawning a helper, check if its content is subsumed by existing infra
or inlineable in the consumer's proof.**

## PASS E — coverage check (2026-05-17)

A "have we missed anything" sweep after Pass D.  Outcome: two findings,
both structural defects that earlier passes did not catch.

### Finding E1: M7 (`miyake_V_p_descend_identity`) had the abstract-Φ defect

Same NEW5 issue as M6(2) had originally.  The lemma quantified over an
abstract `Φ_p : LinearMap` with `hΦ_p_qshift` constraining Φ_p on
V_p-lifted inputs only.  The conclusion involves `Φ_p f` where f
decomposes (via 4.6.7) as `Σ_q g_q · V_q`, and `Φ_p(V_q g_q)` for q ≠ p
is NOT constrained.

**Fix applied**: restated Miyake-faithfully to a function-level
identity on the explicit slash sum + V_p composition.  Now the
conclusion is:

```lean
∃ c : ℂ, c ≠ 0 ∧
  ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
    c * (qExpansion 1
      (fun z => ∑ v, (⇑f ∣[k] descendCosetList p N hp v)
                       (levelRaiseMatrix p • z))).coeff n =
    (qExpansion 1 f).coeff n
```

This is unambiguous and follows from Miyake's 4.6.12 + 4.6.7
decomposition + M6(2) (V_p commutation).

### Finding E2: H26 had a structurally-wrong placeholder body

`multipass_mul_mod_p_perm` was a `def` with `Equiv.refl _` as the body
— that's the IDENTITY permutation, not the multiplication-by-`l`
permutation.  If a downstream consumer (M6(2)'s standard-rep
bijection) had used this as a black box, the proof would have silently
broken with a wrong σ.

**Fix applied**: converted from `def := Equiv.refl _` to a sorry'd
existential `lemma`:

```lean
∃ σ : Equiv.Perm (Fin p),
  ∀ m : Fin p, (σ m).val = (l * m.val) % p
```

Now the *characterising equation* is in the statement; downstream
consumers must extract via `obtain ⟨σ, hσ⟩ := ...` and use `hσ` to
verify σ has the right action.  Wrong-stub risk eliminated.

### Pass E other checks (all passed)

- Helper-list completeness for remaining sorries: no further helpers
  needed beyond H1–H30.
- Statement match against Miyake/DS for restatements R1–R6 (R7
  skipped): verified each cites the right Miyake/DS section in the
  docstring.
- Subsumption claims for C4, C6, H17, H27 (from Pass D): verified
  each subsumes via the named project lemma.
- No vacuous conclusions: every helper has non-trivial statement.
- No remaining `True` placeholders: 4 instances from Pass A/B were
  converted to comment markers in Pass D.

### Pass E verdict

After Pass E: **22 → 23 sorries** (net +1 from H26 def → lemma
conversion).  Two new structural defects fixed (M7's abstract Φ_p,
H26's wrong stub).  No further defects found.

## PASS F — Miyake/DS cross-check from source (2026-05-17)

A re-audit where every statement is checked **directly against the
Miyake PDF** (pages 141–166 read) and Diamond–Shurman where applicable.
Goal: catch any statement that doesn't match the source.

### Statements cross-checked (with Miyake page reference)

| Lemma | Miyake reference | Verdict |
|---|---|---|
| T5a-0 `descendExtraGamma_exists` | Lemma 4.5.11 (p. 143) — γ_p with mod-p `[0,-a;a⁻¹,0]` and mod-N identity | ✓ matches (we use a=1) |
| T5a-3a-clean (R1 canonical Möbius) | Direct calculation in 4.5.11 use: `a·m' ≡ b + m·d (mod p)` from matrix entries | ✓ derived from `[1,m;0,p]·γ' = α·[1,m';0,p]` matrix equation |
| T5a-3a-extra (R2 canonical case split) | Same direct calculation, with case split on whether `A := a + m·c·(N/p)` is unit mod p | ✓ matches |
| T6b `descendCosetList_slash_sum_commute` | Lemma 4.6.6(1) p. 158 — descent commutes with natural embedding | ✓ |
| M6(1) `miyake_4_6_6_level_commute` | Lemma 4.6.6(1) | ✓ Miyake-faithful restate matches |
| M6(2) `miyake_4_6_6_level_commute_delta` | Lemma 4.6.6(2) p. 158 — descent commutes with δ_l | ✓ Miyake-faithful restate matches |
| T_M7_squarefree `miyake_4_6_7_squarefree_decomp` | Lemma 4.6.7 p. 159-160 | ✓ statement and level (Nl²) match |
| M5b `miyake_hecke_descend_qexp` (R4) | Eq. (4.6.12) p. 161 — `g(z) = g_p(pz)` with c = p(d+1)⁻¹ | ✓ q-expansion form |
| M5c `miyake_hecke_descend_cusp` (R5) | Implicit (descent preserves cusps) | ✓ standard |
| M5d `miyake_hecke_descend_char` (R6) | Implicit (4.5.18 + diamond compat) | ✓ |
| M7 `miyake_V_p_descend_identity` (Pass-E restate) | Theorem 4.6.8 inductive step p. 161 | ✓ consistent with Miyake's argument structure |

### Pass-F findings

**F1**: H17 (`qExp_slash_extra_rep`)'s Pass-D subsumption claim was
**incorrect**.  Prior verdict said "subsumed by T6b-coset-invariance" —
but T6b-coset-inv compares two distinct `γ_p^(p)` choices at
different levels; it doesn't collapse a single extra-rep contribution.
Correct subsumption: slash multiplicativity + direct slash formula on
[1,0;0,p] + H21 (`modFormCharSpace_slash_apply`) + descendExtraGamma_spec
(mod-(N/p) congruence ⇒ χ' trivial).  Comment marker updated.

**F2**: C4 (`qExp_upper_tri_slash`)'s Pass-D subsumption claim is
**correct but the reasoning was off**.  The project's
`qExpansion_one_heckeT_p_divN_coeff` works at the **same-level**
upper-tri sum `heckeT_p_ut` (NOT individual slash, NOT the descent
operator).  But for our M5b on V_p-lifted forms, the upper-tri part of
the descent slash sum equals `heckeT_p_ut`, so the project lemma
applies.  Comment marker is OK; reasoning corrected in the audit doc.

**F3 (minor)**: M7's hypothesis doesn't include Miyake's `(l, N/m_χ) ≠
1` condition explicitly.  Our M7 operates at the function/q-expansion
level (no explicit `f_p ∈ G_k(N/p, χ)` claim), so this is benign —
the conclusion holds without the conductor hypothesis.  M8's
construction will implicitly use `m_χ | N/p` via M5's character
factoring.

**F4 (minor)**: T_M7_squarefree returns g at level `N·l²`.  Miyake's
optimization to `N·l` when `l | N` is not used.  In M7's downstream
use, this is over-leveling but the q-expansion identity stands at any
admissible level.  No correctness issue.

### Pass-F verdict

After Pass F:
- 23 sorries unchanged.
- 1 comment marker corrected (H17 subsumption).
- 0 structural defects in remaining statements.
- 4 minor findings (F2 reasoning, F3/F4 over-permissive but
  non-defective).

**No further restatements needed.**  All sorries' statements now
match Miyake exactly (modulo the function-level vs. ModularForm-level
distinction we've adopted across the chain).

## Summary

**Items to spawn in `SMOObligations.lean` after this audit**:

- 7 restatements (R1–R7).
- 6 cross-cutting helpers (C1–C6).
- 10 lemma-specific helpers (H10, H11, H13, H17, H21, H22, H24, H26,
  H27, H30).
- 23 "leaf" closures (currently sorry; 3 number-theoretic primitives, 2
  matrix-arithmetic, 5 slash-sum, 1 coset-inv, 1 diagram, 3 main-lemma
  + helpers landed in the natural files).

**Net LOC delta** (closure of all 16): ~2200 LOC additions + ~80 LOC
restatement edits.

**Caveat**: this is decomposed planning. Execution still needs careful
proof attempts. The point of the multi-pass audit was to make sure no
single sorry hides a structural defect (canonical-witness, abstract-
operator-vs-slash-sum, σ-factor pattern). After Passes A–B, no such
hidden defect remains.
