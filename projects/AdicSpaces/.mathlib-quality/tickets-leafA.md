# Ticket board — Separation spine (Leaf A), Wedhorn Thm 8.28(b)

Created 2026-06-23 by /develop. Source-grounded against `references/wedhorn.txt`
(pdftotext of the Wedhorn PDF) + `references/huber1.txt`. Full decomposition in
`.mathlib-quality/decomposition-leafA.md`. **Start order (user):** L-A1 first.
**L-A4 (user):** build Prop 7.49 (option a).

Target: `cor_8_32_productRestriction_faithfullyFlat` (RPK:2342) axiom-clean → the
injective half of the `IsSheafy` embedding. Already-clean upstream: per-step flatness
`prop_8_30_basic_laurent_step_flat` ✓, Example-6.38 strong-noeth
`presheafValue_isStronglyNoetherian_faithful` ✓, mem_plus continuity ✓ (T-SPVAI-4).

## Dependency graph
```
T-LA1 (Remark 7.55 chain)  ──────────────────────────┐
T-LA3a (Prop 7.19) → T-LA3b (7.47(4) IRIE) ──┐        │
T-LA4a (Lemma 7.45) → T-LA4b (Prop 7.49/LL-unit) ┐    │
                                   T-LA-WIRE (HasLocLift discharge) ── cor_8_32 / Leaf A
```
T-LA1 is independent and on the flatness path; T-LA3*/T-LA4* discharge the
`[HasLocLiftPowerBounded A]` instance the presheaf restriction maps carry.

---

## [T-LA1] Remark-7.55 geometric chain  — START HERE
- **Status**: open
- **File**: RelativePieceKeystone.lean
- **Depends on**: none (per-step + fold already proven)
- **Type**: theorem (geometric construction, ~300 LOC)
- **Target**: `prop_8_30_imagePiece_wholeSpace_flat` (RPK:2129) → `prop_8_30_imagePiece_assembled`
  (RPK:2052), eliminate `sorryAx`.

### Statement (existing, fill the sorry)
```lean
theorem prop_8_30_imagePiece_wholeSpace_flat
    (D E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    @Module.Flat (presheafValue D) (presheafValue (imagePieceDatum D E.T E.s hspanE)) _ _
      ((imagePieceDatum D E.T E.s hspanE).canonicalMap).toModule
```

### Proof sketch (Wedhorn Remark 7.55, wedhorn.txt:3504–3517)
1. `U := imagePieceDatum D E.T E.s` = `R(E.T/E.s)`. By Cor 7.32 (`cor_7_32_dominating_unit`,
   PROVEN) get a unit `u` with `|u(x)| < |s(x)|` on `U`. Set `X₀ := {1 ≤ x(s/u)}`.
2. Build `laurent_cover_from_dominating_unit`: the inductive `X : Fin (n+1) → RationalLocData (presheafValue D)`
   (or `ℕ→…`), `X₀` as above, `Xᵢ := Xᵢ₋₁ ∩ {x(tᵢ/s) ≤ 1}` (`interSamePair` + `unitDatum`,
   LaurentRefinementCore:361/474), each step `LaurentNormalized`.
3. Containments `rationalOpen Xᵢ₊₁ ⊆ rationalOpen Xᵢ` and `Xₙ = imagePieceDatum` (= U) and
   `presheafValue X₀ ≅ presheafValue D` (whole-space identification).
4. Fold: each `Xᵢ → Xᵢ₋₁` is flat by the AXIOM-CLEAN per-step `prop_8_30_basic_laurent_step_flat`;
   compose by `restrictionMap_flat_chain` (RestrictionFlatness:894, `Module.Flat.trans`).
- **In-repo ingredients**: `cor_7_32_dominating_unit` (proven), `prop_8_30_basic_laurent_step_flat`
  (axiom-clean), `restrictionMap_flat_chain` (proven), `interSamePair`/`unitDatum`
  (LaurentRefinementCore), `relativePiece_equiv` (8.16, proven).
- **Missing (the leaf)**: `laurent_cover_from_dominating_unit` + the inductive chain object +
  the `Xₙ = imagePieceDatum` / `presheafValue X₀ ≅ B` identifications.
### Sources
- Wedhorn Remark 7.55, p.70 (wedhorn.txt:3504). Cor 7.32, p.62 (wedhorn.txt:3153).
### Generality
- `section Wedhorn828` `A`-bundle only. NO noeth-A₀, NO data/witness params. The theorem IS
  the construction (not isolable into one sub-lemma).

---

## [T-LA3a] Prop 7.19 — precompletion ring of integral elements
- **Status**: open
- **File**: Example638.lean / Presheaf.lean (where `locSubring`/`completedPlusSubring` live)
- **Depends on**: none
- **Type**: theorem
- **Target**: `C := (A⁺[T/s])^int` (integral closure in `A_s`) is a ring of integral elements:
  open, integrally closed in `A_s`, `⊆ (A_s)°`.

### Sources
- Wedhorn Prop 7.19, p.61 (wedhorn.txt:3015). "Let A = (A,A⁺) be an affinoid ring and (Tᵢ) a
  finite [system] … then A(T/s)⁺ … is a ring of integral elements."
### Notes
- Precompletion (before `Â`); feeds T-LA3b. Check Example638/LocalizationTopology for what
  `locSubring`/`locPlusSubring` already prove (the integral-closure construction exists).

---

## [T-LA3b] Lemma 7.47(4) / IRIE #68 — completion correspondence
- **Status**: open
- **File**: Presheaf.lean
- **Depends on**: T-LA3a
- **Type**: instance (3 fields)
- **Target**: `presheafValuePlus_isRingOfIntegralElements` (Presheaf:502), fields
  `isOpen` / `isIntegrallyClosed` / `subset_powerBounded`, eliminate the 3 `sorry`.

### Proof sketch (Wedhorn Lemma 7.47(4), wedhorn.txt:3393–3405)
1. Under the Example-5.33 open-subgroup bijection `{open G ⊆ A} ↔ {open G' ⊆ Â}`, rings of
   integral elements correspond. `(presheafValue D)⁺ = completedPlusSubring = Ĉ` (the completion
   of `C` from T-LA3a).
2. `isOpen`: `Ĉ` open ⟸ `C` open (T-LA3a) + completion preserves open subgroups.
3. `isIntegrallyClosed`: `Ĉ` integrally closed in `Â` ⟸ `C` integrally closed (T-LA3a) + 7.47(4).
4. `subset_powerBounded`: `Ĉ ⊆ Â°` ⟸ `C ⊆ A_s°` (T-LA3a, ring of integral elements ⊆ power-bounded)
   + `Aᵒ ↔ Âᵒ` (7.47(1)).
### Sources
- Wedhorn Lemma 7.47(4), p.67 (wedhorn.txt:3393). **Proof = [Hu1] 2.4.3** (`huber1.txt:7467`,
  German, "Vervollständigung"; §2.4 "Ganzheitsringe").
### ⚠️ Source-faithfulness STOP-check (CLAUDE.md rule 4)
- Wedhorn defers the proof to [Hu1] 2.4.3. If discharging fields 1–3 in Lean requires building
  *substantial* missing infrastructure (open-subgroup ↔ completion correspondence as a general
  topological-group fact, or integral-closure-commutes-with-completion), STOP and report — treat
  as a cited external leaf, do NOT invent a route. Read huber1.txt:7467 first.
### Role
- Discharges the LL-bdd half of `[HasLocLiftPowerBounded A]`: `mem_plus` →
  `isPowerBounded_of_forall_vle_one_spa_of_complete` → `locLift_divByS_isPowerBounded_faithful`
  bottom solely here. (NOT on the flatness path.)

---

## [T-LA4a] Lemma 7.45 — analytic non-open-prime Spa point
- **Status**: open
- **File**: Presheaf.lean (with downstream completion primitives — may need a bridge file)
- **Depends on**: none (but consumes deep Cont(A) theory)
- **Type**: theorem
- **Target**: `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` (Presheaf:2785), eliminate sorry.

### Proof sketch (Wedhorn Lemma 7.45 general case, wedhorn.txt:3336–3356)
1. `A₀` ring of def, `I` f.g. ideal of def, `p₀ := p ∩ A₀` (non-open ⟹ `I ⊄ p₀`).
2. `m ⊇ p₀` maximal; `I ⊆ m` (Prop 5.38, completeness); `u` valuation of `A₀` with `supp u = p₀`,
   `u(a) < 1 ∀ a ∈ m` (dominating `(A₀/p₀)_{m/p₀}`).
3. Retraction `r : Spv B₀ → Spv(B₀, I)` (7.1.2); `r(u) < 1` on `I` ⟹ `r(u) ∈ Cont(B₀)` (Thm 7.10);
   `I ⊄ supp(r(u))` (Lemma 7.5(3)).
4. Lemma 7.44(3): unique continuous analytic `v` on `A` with `v|A₀ = r(u)`; `supp v ∩ A₀ ⊇ p₀`.
5. `v` microbial (Rem 7.40(5)) ⟹ height-1 vertical generization `x` (Remark 4.12); `x` continuous
   (Rem 7.11(2)); height-1 ⟹ `x ∈ Spa A` (Prop 7.41).
### Sources
- Wedhorn Lemma 7.45, p.66 (wedhorn.txt:3336); Prop 7.41 (wedhorn.txt:3281, in-repo
  `heightOne_le_one_on_powerBounded`); Lemma 7.44(3) (wedhorn.txt:3308); retraction 7.1.2.
- [Hu1] Cont(A)/height-1 theory (`huber1.txt:272+`).
### Notes
- DEEP. Inventory ContinuousValuations / ValuationContinuity / ValuationCoarsening for the
  retraction (7.1.2), Lemma 7.44(3), Remark 4.12 vertical-generization, Prop 7.41 first — much
  may exist. If the retraction/7.44 apparatus is genuinely absent, this is a sub-development.

---

## [T-LA4b] Prop 7.49 + LL-unit wiring
- **Status**: open
- **File**: Presheaf.lean
- **Depends on**: T-LA4a
- **Type**: theorem
- **Target**: `exists_spa_point_supp_eq_nonOpen_maxIdeal_of_complete` (Presheaf:2750) sorry-free
  ⟹ `isUnit_canonicalMap_s_faithful` (LL-unit) clean.

### Proof sketch (Wedhorn Prop 7.49 / 7.51, wedhorn.txt:3417–3470)
1. `m` maximal, non-open. `A/m` Hausdorff (`m` closed: `maxIdeal_isClosed_of_complete_huber`, PROVEN).
2. `{v ∈ Spa A ; supp v = m} = Spa(A/m) ≠ ∅` by Prop 7.49(2): use Lemma 7.45 (T-LA4a) for the
   analytic point, pull back along `A → A/m`.
### Sources
- Wedhorn Prop 7.51, p.69 (wedhorn.txt:3457); Prop 7.49 (wedhorn.txt:3417); Prop 7.52(2)
  (wedhorn.txt:3472).
### Role
- Discharges the LL-unit half of `[HasLocLiftPowerBounded A]`.

---

## [CLEANUP-LA1] /cleanup RelativePieceKeystone.lean
- **Status**: open
- **Depends on**: T-LA1
- **Type**: cleanup

---

## [T-LA-WIRE] Discharge `[HasLocLiftPowerBounded A]` + close cor_8_32 / Leaf A
- **Status**: open
- **File**: FaithfulLocLift.lean / WedhornCechAcyclicity.lean
- **Depends on**: T-LA3b, T-LA4b
- **Type**: wiring
- **Target**: with L-A3 + L-A4 clean, `hasLocLiftPowerBounded_faithful` is axiom-clean; wire the
  faithful instance into the headline so `cor_8_32_productRestriction_faithfullyFlat` (with T-LA1)
  becomes axiom-clean for concrete strongly-noeth-Tate complete `A`.

---

## [CLEANUP-LA-FINAL] /cleanup-all on the Leaf-A files
- **Status**: open
- **Depends on**: T-LA1, T-LA3b, T-LA4b, T-LA-WIRE
- **Type**: cleanup
