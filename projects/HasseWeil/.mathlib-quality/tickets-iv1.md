# Ticket Board — IV.1 Formal-Group Program

*Companion to `.mathlib-quality/plan-iv1.md` (read it first: print-error warnings, decisions D1/D2, risks). Created 2026-06-11 at HEAD cfb13a7.*

Conventions for ALL tickets:
- Worker context: worktree `/Users/mcu22seu/Documents/GitHub/Hasse-Weil-silverman`. Mathlib CACHED — targeted `lake build HasseWeil.<Module>` only; full root build at milestones. Axiom gate per project: `[propext, Classical.choice, Quot.sound]`, no sorryAx, no maxHeartbeats, no new axioms.
- Lean statements below are CANONICAL IN SHAPE, not in binder spelling — the worker adapts variable blocks/instance args to the host file's conventions (Step 2.5 discipline: state with `sorry`, make it elaborate, THEN prove). When a referenced existing decl's exact name differs (e.g. `formalWPS` vs however `FormalGroup.lean` packages `formalW_coeff` as a PowerSeries), grep first and use the real name; if no PowerSeries packaging exists, add `def formalWPS (W) : PowerSeries F := PowerSeries.mk (formalW_coeff W)` as part of FG-A1.
- B2 discipline: if a statement is discovered false (esp. the A5/A6 hardcode risks), do NOT force it — formal counterexample where cheap, restate honestly, append `.mathlib-quality/b2_log.jsonl`, record in the ticket's Progress.
- Source: [Sil] = Silverman AEC 2nd ed., in-repo PDF, PDF page = book page + 18. The plan file carries verbatim quotes; tickets cite by page.

## Summary
- Proof/def tickets: 16 (A1–A6, B1–B5+B4a, C1–C4, D1–D3) + 6 cleanup tickets.
- Milestone: FG-B5 (BRIDGE-003). Phase D is isolated and may end REVIEW-PENDING.
- Parallelism: A1‖A2‖A3 from the start; A4/A5 after A1; B-chain mostly serial; C1‖C2 after B5; D after C4 or parallel to C if a second worker exists.

---

### [FG-A1] Bivariate slope series λ: definition + divided-difference spec + diagonal
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` (NEW) | **Depends on**: none | **Parallel**: yes | **Type**: def + 3 API lemmas
- **Progress**: DONE, all axiom-clean `[propext,Classical.choice,Quot.sound]`, build GREEN 8386. No `formalWPS` needed — legacy `formalW` already packages `mk formalW_coeff`; shipped `coeff_formalW`/`constantCoeff_formalW`/`three_le_order_formalW`/`hasSubst_formalW` instead. Decls: `formalSlopeBiv` + `coeff_formalSlopeBiv`(rfl,@[simp]) + `formalSlopeBiv_spec` (coefficientwise per sketch, via new helpers `coeff_subst_X`/`coeff_X_mul` + `Finsupp.tsub_apply` — NOT `sub_apply`, ℕ-finsupps are tsub) + `constantCoeff_formalSlopeBiv` + `coeff_single_one_formalSlopeBiv` + `formalSlopeBiv_diag_X` + `formalSlopeBiv_diag`. DEVIATION: diag proved via private constant-family form `formalSlopeBiv_diag_const` (`fun _ : Fin 2 => X`) because `![·,·]`(Matrix.cons) makes σ unify as `Fin (Nat.succ 1)`, breaking `rw` of Fin-2-stated lemmas; public `![X,X]`/`![f,f]` forms recovered by funext-rfl bridge + `MvPowerSeries.subst_comp_subst_apply`. Antidiagonal count: `finsum_eq_sum_of_support_subset` + `Finset.sum_image` (**`Set.InjOn` form in current mathlib**) + `Finset.Nat.card_antidiagonal`; derivative side `PowerSeries.coeff_derivative` (`d⁄dX R`). Whole file over `CommRing R` (the actual FormalGroup.lean context; field never needed). ~190 LOC incl. helpers.

#### Statement
```lean
/-- The bivariate slope series λ(z₁,z₂) = (w(z₂) − w(z₁))/(z₂ − z₁), as polynomial divided
differences: coeff (a,b) = formalW_coeff W (a+b+1). Source: [Sil] IV §1, p. 119. -/
noncomputable def formalSlopeBiv (W : WeierstrassCurve F) : MvPowerSeries (Fin 2) F :=
  fun d => formalW_coeff W (d 0 + d 1 + 1)

theorem formalSlopeBiv_spec (W : WeierstrassCurve F) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * formalSlopeBiv W
      = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (formalWPS W)
        - PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalWPS W) := by sorry

theorem constantCoeff_formalSlopeBiv (W) : MvPowerSeries.constantCoeff _ F (formalSlopeBiv W) = 0 := by sorry
-- also: linear coefficients vanish (formalW_coeff 1 = formalW_coeff 2 = 0; w starts at z³)

theorem formalSlopeBiv_diag (W) (f : PowerSeries F) (hf : 1 ≤ f.order) :
    MvPowerSeries.subst ![f, f] (formalSlopeBiv W)
      = PowerSeries.subst f (PowerSeries.derivative (R := F) (formalWPS W)) := by sorry
```

#### Proof sketch
1. Spec, coefficientwise at `d = (a, b)`: LHS coeff = λ(a, b−1) − λ(a−1, b) (X-mul shifts); RHS coeff = `formalW_coeff (b)` if a = 0, minus `formalW_coeff (a)` if b = 0, else 0 (subst into a single variable: `PowerSeries.coeff_subst` with the monomial substitution X i — each w-monomial zⁿ ↦ Xᵢⁿ contributes only to pure-i multi-indices). Case-split on a = 0 / b = 0; the telescoping (`formalW_coeff (a+b)` appears from both shift terms and cancels except at the boundary) is [Sil] p. 119's `(z₂ⁿ − z₁ⁿ)/(z₂ − z₁) = Σ_{i+j=n−1} z₁ⁱ z₂ʲ` read backwards.
2. Constant/linear vanishing: `formalW_coeff W 1 = 0`, `2 = 0` (w = z³(1 + …); these facts exist near `formalW_recurrence`, FormalGroup.lean:336–439 — grep; if absent, 2-line consequences of the recurrence base).
3. Diagonal: coeff n of both sides = `(n+1) · formalW_coeff (n+1)`-shaped; LHS via `MvPowerSeries.coeff_subst` over ![f,f] collapses pairs (i,j) with i+j fixed: Σ_{i+j=m} λ(i,j) = (number of pairs) × A — careful: λ(i,j) depends only on i+j, so Σ_{i+j=m} = (m+1)·formalW_coeff (m+1); RHS: derivative coeff. Then both are `PowerSeries.subst f` of the same series (state the cleaner intermediate `subst ![f,f] λ = subst f (mk fun m => (m+1) • formalW_coeff (m+1))` and identify with `derivative`).
4. `HasSubst` side conditions throughout via `hasSubst_of_constantCoeff_zero` (f has order ≥ 1; X i has constant 0).

#### Mathlib lemmas
`MvPowerSeries.coeff_subst`, `MvPowerSeries.hasSubst_of_constantCoeff_zero`, `PowerSeries.coeff_subst`, `PowerSeries.coeff_derivative` (verify exact name: `PowerSeries.coeff_derivative` exists), `MvPowerSeries.coeff_X_mul`-shaped shifts (or `coeff_mul` + support analysis).

#### Sources
[Sil] IV §1 p. 119 (PDF 137): the λ display `λ = Σ_{n=3}^∞ A_{n−3}(z₂ⁿ−z₁ⁿ)/(z₂−z₁)`; verbatim quote in plan-iv1.md.

#### Generality
Over any `Field F` (matching FormalGroup.lean's context; no DecidableEq unless the host file forces it). `formalSlopeBiv` total (no hypotheses); specs carry only what they need.

---

### [FG-A2] w-uniqueness in F[[z]] (Silverman IV.1.1(b) / Hensel uniqueness)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: none | **Parallel**: yes | **Type**: lemma (+1 helper def if needed)
- **Progress**: DONE, axiom-clean. Stated PARAMETRICALLY from the start per FG-B1's design note: `weierstrassZWAt (W) (z₀ s : PowerSeries R)`. Decls: `weierstrassZWAt`, `formalW_fixedPoint` (`:= formalW_recurrence W`, pure defeq repackage), `weierstrassZWAt_unique` (hypotheses all at the weakest `1 ≤ order`, per the ticket's check — proof = order bootstrap via the shipped `PowerSeries.eq_zero_of_self_eq_self_mul` from PowerSeriesHelpers, no `order_mul`/domain needed), `subst_formalW_fixedPoint`, `constantCoeff_subst_formalW`, `one_le_order_subst_formalW`, and the B1 engine `eq_subst_formalW_of_fixedPoint` (any 1≤order fixed point at z₀ IS `subst z₀ (formalW W)`). LANDMINE (confirmed, the FormalGroup.lean:441 note is real): `ring` FAILS on `PowerSeries R` goals in this toolchain (produces `*1+0` junk; works fine on `MvPowerSeries (Fin 2) R`) — the factorization is the private abstract lemma `weierstrassZW_sub_factor` over a generic CommRing `A`, instantiated by `exact` (defeq unfolds `weierstrassZWAt`). Also: dot-`.order` on `PowerSeries.subst` output resolves to `MvPowerSeries.order` (subst returns `MvPowerSeries Unit R`) — statements spell `PowerSeries.order (...)` explicitly; subst-of-constants handled by new `subst_C`/`subst_C'` (via `Polynomial.coe_C`+`subst_coe`+`aeval_C`, `algebraMap R (MvPowerSeries τ R) r = C r` is rfl). ~95 LOC.

#### Statement
```lean
/-- The (z,w)-Weierstrass equation as an operator on power series:
f(z, s) = z³ + a₁ z s + a₂ z² s + a₃ s² + a₄ z s² + a₆ s³. -/
noncomputable def weierstrassZW (W : WeierstrassCurve F) (s : PowerSeries F) : PowerSeries F :=
  PowerSeries.X ^ 3 + C W.a₁ * X * s + C W.a₂ * X ^ 2 * s + C W.a₃ * s ^ 2
    + C W.a₄ * X * s ^ 2 + C W.a₆ * s ^ 3

theorem formalWPS_eq_weierstrassZW (W) : formalWPS W = weierstrassZW W (formalWPS W) := by sorry
-- (likely a repackaging of the existing formalW_recurrence — grep FormalGroup.lean:336-439)

theorem weierstrassZW_unique (W) (s : PowerSeries F) (hs : 3 ≤ s.order)
    (heq : s = weierstrassZW W s) : s = formalWPS W := by sorry
```

#### Proof sketch
1. Repackage `formalW_recurrence` (exists, proven) into the fixed-point form `formalWPS_eq_weierstrassZW`; if the existing recurrence is coefficientwise, this is `PowerSeries.ext` + that recurrence.
2. Uniqueness, by the order-bootstrap (Silverman IV.1.2 step 5 made quantitative): let `u := s − formalWPS W`. The factorization `f(z,X) − f(z,Y) = (X−Y)·g(z,X,Y)` with `g = a₁z + a₂z² + a₃(X+Y) + a₄z(X+Y) + a₆(X²+XY+Y²)`; for X,Y of order ≥ 3, `g` evaluated has order ≥ 1. So `u = weierstrassZW W s − weierstrassZW W (formalWPS W) = u · G` with `order G ≥ 1`, giving `order u ≥ order u + 1` unless `u = 0`; conclude `u = 0` (use `PowerSeries.order_eq_top` ⟺ zero; the inequality forces order = ⊤).
3. Mind `WithTop ℕ∞` arithmetic; the project's `Curves/WithTopArith` may have helpers.

#### Mathlib lemmas
`PowerSeries.order_mul` (domain), `PowerSeries.order_eq_top`, `le_order` API; `PowerSeries.ext`.

#### Sources
[Sil] IV.1.2 p. 117–118 (PDF 135–136): the factorization device "F(X) − F(Y) = (X−Y)(F′(0) + XG + YH)" and the uniqueness paragraph (step 5 in the plan's extraction); IV.1.1(b) p. 116.

#### Generality
Any `Field F`; `hs : 3 ≤ s.order` matches IV.1.1's shape (could weaken to 1 ≤ order with the same proof — TAKE 1 ≤ order if the bootstrap goes through, since B1's w_α a priori has order = 3·(orderTop f_α) ≥ 3 anyway; state with the weakest hypothesis the proof supports).

---

### [FG-A3] ν, the chord cubic coefficients A and B, and z₃
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: FG-A1 | **Parallel**: after A1 | **Type**: defs + API
- **Progress**: DONE, axiom-clean. Decls: `formalNuBiv` + `constantCoeff_formalNuBiv`, `line_eval_left` (mul_comm + `add_sub_cancel`), `line_eval_right` (**direct `linear_combination (formalSlopeBiv_spec W)`** — linear_combination/ring DO work on `MvPowerSeries (Fin 2) R`), `chordA` + `constantCoeff_chordA` + `isUnit_chordA` (`MvPowerSeries.isUnit_iff_constantCoeff`, available over CommRing) + `chordA_mul_inv`/`chordA_inv_mul` (`IsUnit.mul_val_inv`/`.val_inv_mul`), `chordB` (CORRECTED form, `2 •`/`3 •` ℕ-smul char-safe) + `constantCoeff_chordB`, `formalZ3` + `constantCoeff_formalZ3`. DEVIATION: `formalZ3` spells the inverse as `Units.val (isUnit_chordA W).unit⁻¹` — bare `↑u⁻¹` in a def body (no expected-type context) gets stuck on `HMul (MvPowerSeries..) (..)ˣ` unification. Polynomial-cubic apparatus NOT built, per ticket (B4 works in KE). ~85 LOC.

#### Statement
```lean
noncomputable def formalNuBiv (W) : MvPowerSeries (Fin 2) F :=
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalWPS W) - MvPowerSeries.X 0 * formalSlopeBiv W

/-- A = 1 + a₂λ + a₄λ² + a₆λ³ — the chord cubic's leading coefficient. -/
noncomputable def chordA (W) : MvPowerSeries (Fin 2) F := 1 + C a₂ * λ + C a₄ * λ^2 + C a₆ * λ^3
/-- B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν — the z²-coefficient. ⚠ CORRECTED form;
the 2nd-ed print (p. 119) has wrong signs — see plan-iv1.md. Matches the legacy code's `B`. -/
noncomputable def chordB (W) : MvPowerSeries (Fin 2) F := C a₁ * λ + C a₂ * ν + C a₃ * λ^2 + 2 • (C a₄ * λ * ν) + 3 • (C a₆ * λ^2 * ν)

theorem isUnit_chordA (W) : IsUnit (chordA W) := by sorry          -- constant coeff 1
noncomputable def formalZ3 (W) : MvPowerSeries (Fin 2) F :=
  - MvPowerSeries.X 0 - MvPowerSeries.X 1 - chordB W * (isUnit_chordA W).unit⁻¹

theorem constantCoeff_formalZ3 (W) : constantCoeff _ F (formalZ3 W) = 0 := by sorry
-- line-evaluation specs (the two points are on the line w = λz + ν):
theorem line_eval_left (W) : formalSlopeBiv W * X 0 + formalNuBiv W
    = PowerSeries.subst (MvPowerSeries.X (0:Fin 2)) (formalWPS W) := by sorry   -- definitional from ν
theorem line_eval_right (W) : formalSlopeBiv W * X 1 + formalNuBiv W
    = PowerSeries.subst (MvPowerSeries.X (1:Fin 2)) (formalWPS W) := by sorry   -- from A1's spec
```

#### Proof sketch
1. `line_eval_left`: unfold ν — `λ·z₁ + (w₁ − λ·z₁) = w₁`, pure ring.
2. `line_eval_right`: `λ·z₂ + ν = λ·z₂ + w₁ − λ·z₁ = w₁ + (z₂−z₁)·λ = w₁ + (w₂−w₁) = w₂` by FG-A1's spec. Ring + the spec; division-free ([Sil]'s "two of whose roots are z₁ and z₂" justification, p. 119).
3. `isUnit_chordA`: constant coefficient of λ is 0 (A1) ⟹ constantCoeff A = 1 ⟹ unit (`MvPowerSeries.isUnit_iff_constantCoeff` — verify name; over a field constantCoeff ≠ 0 suffices).
4. `constantCoeff_formalZ3`: all three summands have constant coeff 0 (λ, ν have const 0 — ν: w₁ has order ≥ 3 under subst, z₁λ const 0; so B const 0).
5. Optional (only if B4's primary route wants it): the generic cubic facts — `(chordA W) * X^3-shaped` polynomial identity. DO NOT build the full polynomial apparatus unless B4 pulls it; the line/Vieta work happens in KE (see B4).

#### Mathlib lemmas
`MvPowerSeries.isUnit_iff_constantCoeff`-shaped (or build the unit via `Units.mkOfMulEqOne` with the geometric-series inverse — the legacy `binv` exists for the coefficient world; prefer mathlib's `MvPowerSeries.invOfUnit`), `constantCoeff_subst` (mathlib, `constantCoeff_subst_eq_zero`).

#### Sources
[Sil] IV §1 p. 119 (PDF 137): ν definition, the line, the substituted cubic; the CORRECTED z₃ display (plan-iv1.md §References — print error verified).

#### Generality
Any field. `2 •`/`3 •` as ℕ-smul (char-free — do NOT write `2 *` with coercions that break in char 2/3).

---

### [CLEANUP-FG-1] /cleanup on FormalGroupLawSpec.lean (cadence)
- **Status**: open | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: FG-A1, FG-A2, FG-A3 | **Parallel**: no | **Type**: cleanup

---

### [FG-A4] The bcomp/bmul/binv ↔ MvPowerSeries dictionary
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: FG-A1, FG-A3 | **Parallel**: with A5 | **Type**: lemmas
- **Progress**: DONE, all axiom-clean `[propext,Classical.choice,Quot.sound]`, build GREEN (root 8386). DEVIATION: the legacy `bmul/binv_by_degree/binv_aux/binv/bpow/bcomp/invDenom_coeff` were `private` in FormalGroup.lean — DE-PRIVATED (visibility-only edit; dictionary statements cannot name privates). Decls: `F_of` + `coeff_F_of`(@[simp],rfl) + `constantCoeff_F_of`; `F_of_bmul` (Finset.sum_bij' between `Finset.antidiagonal d` and the `range×ˢrange` rectangle) + ticket-shaped `coeff_F_of_mul`; `binv_by_degree_eq` (wf.fix unfold — `change wf.fix _ N = _; rw [fix_eq]; rfl`, dite-with-constant-body ≡ ite is defeq) + `binv_zero_zero` + `binv_eq_of_ne` (the `a+b<N` truncation guard discharged by omega: sub-corner indices have strictly smaller total degree); `F_of_binv_mul : f 0 0 = 1 → F_of (binv f) * F_of f = 1` via corner-splitting helpers `sum_rect_corner`/`sum_rect_split_corner`; `bpow_zero/succ` (rfl) + `bpow_one` + `F_of_bpow` + `bpow_eq_zero_of_lt`; **`coeff_subst_F_of`** (the bcomp dictionary: `PowerSeries.coeff_subst` finsum truncated onto `range (d 0 + d 1 + 1)` by `bpow_eq_zero_of_lt` + `finsum_eq_sum_of_support_subset`). Ingredient chain for A6 also here: private `lamS/w1S/nuS/AS/BS/z3S` mirror the legacy `let`-streams; `F_of_lamS` is `rfl` (as predicted); `F_of_w1S/nuS` via `coeff_subst_X`/`coeff_X_mul`; `F_of_AS/BS` coefficientwise-decompose + `ring` (works on Mv); `F_of_binv_AS = ↑(isUnit_chordA W).unit⁻¹` via `left_inv_eq_right_inv` against `chordA_mul_inv`; `F_of_z3S = formalZ3 W`.

#### Statement
```lean
-- For the legacy coefficient-level bivariate pipeline in FormalGroup.lean:77-101
-- (bmul = Cauchy product, binv = unit inverse, bcomp = composition of a univariate
--  coefficient stream with a bivariate one), prove it computes the same thing as the
--  MvPowerSeries operations. Exact shapes (adapt names to the file):
theorem bmul_eq_coeff_mul (f g : ℕ → ℕ → F) : ... = MvPowerSeries.coeff F d (F_of f * F_of g) := by sorry
theorem binv_eq_coeff_inv ... := by sorry
theorem bcomp_eq_coeff_subst (c : ℕ → F) (g : ℕ → ℕ → F) (hg : g 0 0 = 0) :
    bcomp c g i j = MvPowerSeries.coeff F (fin2Idx i j) (PowerSeries.subst (F_of g) (PowerSeries.mk c)) := by sorry
```
(`F_of` = the obvious (ℕ→ℕ→F) → MvPowerSeries (Fin 2) F repackaging; define it with @[simp] coeff lemma.)

#### Proof sketch
1. Read the legacy `bmul/binv/bcomp` definitions FIRST (FormalGroup.lean:77-101); state the dictionary against what they actually are.
2. `bmul`: both sides are the convolution Σ over antidiagonal pairs — `MvPowerSeries.coeff_mul` + reindexing `Finset.Nat.antidiagonal`-style for Fin 2 →₀ ℕ (the finsupp antidiagonal; mathlib `MvPowerSeries.coeff_mul` sums over `Finsupp.antidiagonal d` — biject with the ℕ×ℕ rectangle).
3. `binv`: both satisfy the same recursion against bmul ⟹ agree by strong induction on total degree (uniqueness of inverses: prove `F_of (binv f) * F_of f = 1` from the recursion + step 2, then `inv` uniqueness).
4. `bcomp`: `PowerSeries.coeff_subst` gives a finsum over n of `c n · coeff d (g-series ^ n)`; the legacy bcomp is the same truncated sum (finitely many n contribute since `order (F_of g) ≥ 1` from `hg`... NOTE: bcomp may assume more — match its actual guard). Induction on total degree or direct finsum manipulation.
5. This ticket is bookkeeping-heavy, math-light. Budget accordingly; `decide`-free, char-free.

#### Mathlib lemmas
`MvPowerSeries.coeff_mul`, `PowerSeries.coeff_subst`, `finsum` API (`finsum_eq_sum_of_support_subset`), `Finsupp.antidiagonal`.

#### Sources
None (pure translation layer; the legacy pipeline transcribes [Sil] p. 119–120's arithmetic).

#### Generality
Any field (or even CommRing where the legacy defs allow — match the legacy context).

---

### [FG-A5] The inversion series spec (or B2-restate)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: FG-A2 | **Parallel**: with A4 | **Type**: lemma (RISK: hardcode mismatch)
- **Progress**: DONE, axiom-clean; **NO B2 — the recursion matches the closed form on the nose**. Reconstructed closed form: `D := mk (invDenom_coeff W)` satisfies `D·(1 − C a₁·X − C a₃·formalW W) = 1` (`invDenom_mul_eq_one`; the `n ≥ 3` branch's `Σ_{k∈range(n−2)} u_k d_{n−3−k}` IS `coeff (w·D)` after dropping w₀..w₂ + `sum_Ico_consecutive`/`sum_Ico_eq_sum_range` reindex), and `formalInverse W = −(X·D)` (`formalInverse_eq_neg_X_mul`, via `eq_neg_of_add_eq_zero_right` — Neg-free proof). Headline `formalInverse_spec : formalInverse W * (1 − C a₁·X − C a₃·formalW W) = −X`. Also: `invDenom_coeff_eq` (fix-unfold, rfl) + `_zero/_one/_two/_three/_succ`, `coeff_formalInverse`(@[simp]), `constantCoeff_formalInverse = 0`(@[simp]), `coeff_one_formalInverse = −1`, `hasSubst_formalInverse`. The ticket's Laurent ratio form (formalX/formalY) NOT here — LocalExpansion sits ABOVE this file (plan's cycle-safe order); it's Phase-B material. NEW LANDMINES (PowerSeries R instance-path disease, sharper than the known ring-failure): **Neg-headed rewrites (`map_neg`, `neg_mul`, also `mul_one`/`zero_pow`/`map_zero`-on-coeff) do NOT fire via `rw`/`simp` on `PowerSeries R`** while `map_sub`/`coeff_C_mul`/`coeff_succ_X_mul`/`map_add` DO; instantiate abstract CommRing lemmas by `exact`/`Eq.trans` (defeq) instead. **`show` does NOT decontaminate a goal whose type came from unifying with an abstract lemma's RHS** — state the intermediate as a standalone `have` (fresh elaboration) and `Eq.trans` at the end.

#### Statement
```lean
/-- i(z) is the z-coordinate of the negated point: as series,
i = x(z)/(y(z) + a₁x(z) + a₃) — equivalently, the USABLE form below avoids Laurent division:
(w-form) the pair (i(z), w∘i(z)) is the (z,w)-image of negation. Target spec, in the
form Phase B consumes (negation under substitution): -/
theorem formalInversePS_spec (W) :
    (formalWPS_y_unit-form making the three series x_ser, y_ser expressible) ... := by sorry
-- CANONICAL CONCRETE FORM (design target — adapt):
-- (ofPS (formalInversePS W)) * (y_ser + C a₁ * x_ser + C a₃ |>.map ofPS-as-Laurent)
--   = x_ser-as-Laurent     in LaurentSeries F,
-- where x_ser := localExpand-free: HahnSeries.single (−2) 1 * (unit from formalU)… — USE the
-- existing formalX/formalY (LocalExpansion.lean:114-121) which ARE x_ser, y_ser:
theorem formalInversePS_ratio (W) [DecidableEq F] :
    HahnSeries.ofPowerSeries ℤ F (formalInversePS W)
        * (formalY W + HahnSeries.C (W.a₁) * formalX W + HahnSeries.C (W.a₃))
      = - formalX W := by sorry
```
**Sign check is part of the ticket**: Silverman p. 120: `i(z) = x(z)/(y(z) + a₁x(z) + a₃)` — but i(z) = −z − a₁z² − … starts NEGATIVE (extraction §1.7.5: computed i(z) = −z − a₁z² − a₁²z³ − …) while x/(y+a₁x+a₃) = (z⁻²+…)/(−z⁻³+…) = −z+…: consistent ✓; fix the project's sign convention against formalInverse_coeff's actual recursion before stating.

#### Proof sketch
1. READ `formalInverse_coeff`/`invDenom_coeff` (FormalGroup.lean:49-61) and reconstruct what identity its recursion enforces (the comment says invDenom = `(1 − a₁z − a₃z³u(z))⁻¹`-ish: i(z) = −z·invDenom? Derive: x/(y+a₁x+a₃); with x = z/w, y = −1/w: = (z/w)/((−1+a₁z+a₃w)/w) = z/(−1+a₁z+a₃w(z)) = −z·(1−a₁z−a₃w(z))⁻¹. So i = −z·(1 − a₁z − a₃·w(z))⁻¹ with w(z) = z³u(z)-shaped). Verify the Lean recursion against THIS closed form.
2. Prove the closed form: `formalInversePS W * (1 − C a₁ * X − C a₃ * formalWPS W) = −X` in PowerSeries (coefficientwise from the recursion, or via uniqueness of inverses).
3. Derive the Laurent ratio form: multiply through by the unit relating (1 − a₁z − a₃w) to (y+a₁x+a₃)·(−w)-style — using formalX = z/w-as-Laurent, formalY = −1/w (their defining lemmas in LocalExpansion.lean:114-121 + formalXY_weierstrass :391). Pure ring-hom algebra in LaurentSeries.
4. **B2-escape**: if the recursion does NOT match the closed form (constant/sign drift), restate `formalInverse_coeff` to the closed form (it has ZERO theorem consumers — audit verified; only `formalGroupLaw_coeff`'s bcomp consumes it, so FG-A6's band check must then be re-run against the new values), b2-log, proceed.

#### Mathlib lemmas
`PowerSeries.invOfUnit`-style uniqueness or direct coefficient induction; `HahnSeries.ofPowerSeries` ring-hom lemmas.

#### Sources
[Sil] IV §1 p. 120 (PDF 138): the i(z) display + "an argument similar … shows that the w-coordinate of the inverse … equals w(i(z))" (the w-leg, if needed in B5, follows from A2-uniqueness exactly as Silverman says).

#### Generality
Any field; `[DecidableEq F]` only if LocalExpansion's formalX/formalY context forces it.

---

### [FG-A6] The spec: formalGroupLaw = i ∘ z₃ (+ the band check)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/FormalGroupLawSpec.lean` | **Depends on**: FG-A3, FG-A4, FG-A5 | **Parallel**: no | **Type**: theorem (RISK: band mismatch → B2)
- **Progress**: DONE — **`formalGroupLaw_eq_chord` PROVEN, axiom-clean, root build GREEN 8386**. **BAND CHECK PASSED at all six multi-indices, NO B2**: (1,1)→−a₁ ✓, (2,1)/(1,2)→−a₂ ✓, (3,1)/(1,3)→−2a₃ ✓, (2,2)→a₁a₂−3a₃ ✓ (canary (1,1) verified first; the hardcode matches the CORRECTED print as the plan predicted). Band machinery: `formalW_coeff_four/_five` (public), value-lemma layers AS(6)/binv-AS(5)/BS(13)/z3S(13) + general `bpow_two/three/four` (funext-collapse of `bpow_succ`), six `band_ij` lemmas by full-`simp` expansion + `ring`. **SKETCH DEVIATION (important)**: the ticket's "degrees 0–1" step is really the FULL unit rows — the legacy branches hardcode `coeff (0,j) = δ_{j1}` for ALL j (and the i-row), so the RHS needs the genuine row identity `i(z₃)|_{z_{s'}:=0} = z_s`, an infinite-family statement. Proven via: `rowFamily s := (X at s, 0 else)` substitution + row extraction `coeff_subst_rowFamily` (coeff n ∘ subst(rowFamily s) = coeff (single s n)); both rows collapse to the SAME univariate data (ν ≡ 0 on both rows!): `lam0 := mk (w_{n+1})` with `X·lam0 = w`, quadratic `lam0 = A0·X² + B0·X` (w-recursion at w = X·λ₀ + cancel the regular X), Vieta transport to `ζ = −X − B0·v` (`quad_at_third_root`, division-free linear_combination), `w(ζ) = lam0·ζ` by FG-A2's `eq_subst_formalW_of_fixedPoint`, star identity `−ζ = X·(1 − a₁ζ − a₃w(ζ))`, and `row_final_abstract` assembly against FG-A5 (`subst_rowZ3_formalInverse`). Tail (i,j ≥ 1, i+j ≥ 5): `formalGroupLaw_coeff_tail` = if-reductions + `rfl` (the de-privated streams zeta-match the legacy lets) + the A4 dictionary `coeff_subst_F_of`. Final assembly: 4-way `by_cases` on d 0 = 0 / d 1 = 0 / i+j ∈ {2,3,4} with omega-rcases on the band indices. NEW LANDMINES: **`simp only` does NOT run the default simprocs' Nat-sub reduction in this setup** — `1 − 0`-style indices stay unreduced and value lemmas silently don't fire (use full `simp` for the numeric grinds); `fin_cases s` leaves `(fun i ↦ i) ⟨0,⋯⟩` artifacts that break `rw`-matching — normalize with `simp only [Fin.zero_eta, Fin.mk_one]` or close by `exact` (defeq ignores them); `MvPowerSeries.substAlgHom` needs explicit `(R := R)` (its source coefficient ring is otherwise a stuck meta); `map_one` on substAlgHom fails OneHomClass synthesis — route `1 = C 1` through `mv_subst_C`/`subst_C'` instead; `MvPowerSeries.coeff_subst`'s `d.prod (a ·)^·` term must be consumed via `finsum_congr`+`Eq.trans` (defeq unification), not `rw` (the pow-instance differs from a locally-stated lemma's).

#### Statement
```lean
theorem formalGroupLaw_eq_chord (W : WeierstrassCurve F) :
    (formalGroupLaw W).toMvPowerSeries
      = PowerSeries.subst (formalZ3 W) (formalInversePS W) := by sorry
```

#### Proof sketch
1. Coefficientwise at degree d := i + j. For d ≥ 5: the legacy definition IS `bcomp (formalInverse_coeff) z3 i j` — apply FG-A4's dictionary + the agreement of the legacy internal `lam/nu/A/B/z3` coefficient streams with FG-A3's named series (each is built from the same bmul/binv pipeline — this is a per-ingredient FG-A4 application; state per-ingredient equalities `F_of (legacy lam) = formalSlopeBiv W` etc. as private lemmas).
2. Degrees 0–1: both sides give 0 / X₀+X₁ (unit rows proven for LHS at `FormalGroupAssoc.lean:114,125` + FIS:141-155; RHS: i = −z+…, z₃ = −z₁−z₂+(≥2) ⟹ coeff comparison direct).
3. **The band 2 ≤ d ≤ 4** (9 multi-indices): compute the RHS coefficients explicitly (finite truncated computation: z₃'s coefficients to degree 4 need λ, ν to degree 4, w to degree 7 — all available; the plan's corrected F display gives the EXPECTED values: deg 2: −a₁z₁z₂; deg 3: −a₂(z₁²z₂+z₁z₂²); deg 4: −2a₃z₁³z₂ + (a₁a₂−3a₃)z₁²z₂² − 2a₃z₁z₂³) and compare with the hardcoded `formalGroupLaw_coeff` values (which match the corrected print — plan §References). Mechanically: `MvPowerSeries.ext_iff`-free — prove the 9 coefficient equalities as 9 lemmas by unfolding `coeff_subst` to the relevant finite sum + `ring`. Expect ~150–300 LOC of grind. **If ANY band value disagrees**: B2 — the hardcode is wrong; restate `formalGroupLaw_coeff` to pure recursion-from-degree-2, re-prove the five legacy coefficient facts (unit rows survive; the FIS:141-155 trio needs re-deriving from the recursion — small), b2-log, sweep consumers (statement-level only; all witness-parametric).
4. Sanity anchor (cheap, do first): verify coeff at (1,1) of RHS = −a₁ by hand-expansion BEFORE grinding all 9 — an early mismatch signal.

#### Mathlib lemmas
`PowerSeries.coeff_subst` (finsum), `MvPowerSeries.coeff_mul`, `ring`.

#### Sources
[Sil] IV §1 pp. 119–120 with the plan's print-error corrections (z₃ AND the F quartic band — both verified against independent recomputation; the extraction recomputed F two ways including the a₃-isolation check).

#### Generality
Any field.

---

### [CLEANUP-FG-2] /cleanup on FormalGroupLawSpec.lean (final per-file)
- **Status**: open | **Depends on**: FG-A4, FG-A5, FG-A6 | **Type**: cleanup

---

### [FG-B1] Keystone: w_α = w ∘ f_α (substitution principle via uniqueness)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` (NEW; imports FormalGroupLawSpec, FormalIsogenySeries) | **Depends on**: FG-A2 | **Parallel**: no | **Type**: theorem
- **Progress**: DONE, all axiom-clean `[propext,Classical.choice,Quot.sound]`, file 489 LOC, 0 sorries/maxHeartbeats, targeted + root builds GREEN (8387). NEW `HasseWeil/ChordExpansion.lean`, registered in root `HasseWeil.lean`. **Stated for the ABSTRACT pair per the design note** — `localExpand_wPair {ξ η : KE} {f : PowerSeries F} (h_weier : (W_KE W).toAffine.Equation ξ η) (hξ_neg : (W_smooth W).ordAtInfty ξ < 0) (hz : localExpand W (-ξ/η) = ofPowerSeries f) : localExpand W (-η⁻¹) = ofPowerSeries (subst f (formalW W))` — `hz` takes the z-expansion ABSTRACTLY (any `f`), so the B5 sum-point instantiation `(X₃, Y₃′, subst ![f_α,f_β] z₃-series)` plugs in directly (B5 derives its own `hξ_neg` via the FIS:1375 back-conversion). η-pole, η≠0, `1 ≤ order f` all DERIVED inside (the FIS abstract-pair bricks `ordAtInfty_y_ne_zero/_y_lt_..._of_equation_of_ord_x_neg` are already pair-generic — no adaptation needed). Supporting decls: `ofPowerSeries_mk_coeff` (Laurent→PowerSeries descent: `0 ≤ orderTop S → ofPowerSeries (mk fun n => S.coeff n) = S`; the FIS:80 `formalIsogenySeries` def IS that mk, so the bridge `localExpand_pullback_localParam` is `unfold + exact`), `constantCoeff_eq_zero_of_ofPowerSeries_orderTop_pos`, `ne_zero_of_ordAtInfty_neg`, `pullback_localParam_eq` (α*t = −α*x/α*y), isogeny corollary `localExpand_pullback_wFunc`. PROOF MECHANICS: (z,w)-identity via abstract-field helper `zw_identity_of_weierstrass` (field_simp + `linear_combination -h`; multiplier is −1 NOT y — field_simp normalizes to the −E form); push = `simp only [map_add, map_mul, map_pow, localExpand_algebraMap, hz, hwfact] at hL`; descent via `HahnSeries.ofPowerSeries_injective` + `simp only [weierstrassZWAt, map_add, map_mul, map_pow]` + `linear_combination hL` (LaurentSeries ring works); close with `eq_subst_formalW_of_fixedPoint`. NEW LANDMINES: (1) **the reconstruction equation is SELF-REFERENTIAL as a simp rule** (`localExpand w = ofPS (mk fun n => (localExpand w).coeff n)` loops simp to maxRecDepth) — introduce the power series as an OPAQUE fvar first (`obtain ⟨s, hs_def⟩ : ∃ s, s = mk ... := ⟨_, rfl⟩`), restate the equation against `s`, then simp terminates; (2) `rw [(W_smooth W).ordAtInfty_zero] at h` FAILS after `rw [h0] at h` (the rewritten `0` lands on a different instance path than the lemma's `0`) — derive `ξ ≠ 0` via `ordAtInfty_eq_top_iff` + `not_top_lt` instead; (3) inline `(by rintro ⟨n, rfl⟩; omega : j ∉ Set.range ⇑emb)` fails (omega can't see through the bundled embedding) — state the non-membership against the PLAIN cast `Set.range ((↑) : ℕ → ℤ)` as a standalone `have` (FIS:1802 pattern), `embDomain_notin_range` accepts it by defeq; (4) `le_or_lt` no longer exists in this mathlib — `le_or_gt`.

#### Statement
```lean
/-- For a genuine isogeny (x-pole at O), the expansion of α^*(−1/y) is the w-series
substituted with f_α := formalIsogenySeries W α. [Sil] IV.1.1(b) is the engine. -/
theorem localExpand_pullback_wFunc (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (α.pullback (-(y_gen W)⁻¹))
      = HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.subst (formalIsogenySeries W α) (formalWPS W)) := by sorry
```

#### Proof sketch
1. Notation: `f_α := formalIsogenySeries W α`; shipped: `orderTop (localExpand (α^*t)) > 0` from h_α (`FIS:1765`), and `localExpand (α^*t) = ofPowerSeries f_α` (reconstruction: orderTop ≥ 0 ⟹ the Laurent series is its own power-series part — `HahnSeries.X_order_mul_powerSeriesPart`/`ofPowerSeries_powerSeriesPart` at LaurentSeries.lean:251-257 + `formalIsogenySeries_coeff`; if FIS lacks this exact bridge lemma, prove it here as `localExpand_pullback_localParam_eq_ofPS` — ~30 LOC, reusable in B5/C2).
2. Set `s := powerSeriesPart (localExpand (α^*wFunc))`-style: first show `orderTop (localExpand (α^*wFunc)) ≥ 3` — wFunc = −1/y, ord_∞(y) = −3, pullback scales by e ≥ 1: use `ordAtInfty`-side (R5b transport `orderTop_localExpand_eq_ordAtInfty` FIS:1662 + the project's ord_∞(α^*y) facts; or directly: w = −t³/(t-cubed-relation)… simplest: w = t·x⁻¹·…: derive ord from h_α + curve equation via the shipped `ordAtInfty_y_lt_ordAtInfty_x` family FIS:1217).
3. The function-level identity in KE: `wFunc = weierstrassZW-as-function (t, wFunc)` — i.e. push the (z,w)-Weierstrass identity `w = z³ + a₁ z w + … + a₆ w³` (an identity in KE between t and −1/y — equivalent to the curve equation; prove by field_simp from `W_KE`'s equation, or reuse `formalXY_weierstrass` LocalExpansion:391 transported) through the ring hom `localExpand ∘ α.pullback`.
4. The resulting equation says `S := localExpand(α^*wFunc)` satisfies `S = (z³ + a₁zS + …)∘[z := ofPS f_α]` — pull back along `ofPowerSeries` (injective ring hom; all terms have orderTop ≥ 0) to a PowerSeries-level fixed point for `s` with `3 ≤ order s`; conclude `s = subst f_α formalWPS`?? — CAREFUL: A2's uniqueness is for `weierstrassZW W s` (z := X); here z := f_α. Generalize A2 mechanically: the SAME bootstrap proves uniqueness for the f_α-substituted operator `s = z₀³ + a₁z₀s + …` for ANY fixed z₀ with 1 ≤ order z₀ (state A2 in this parametric form FROM THE START — adjust FG-A2's statement: `weierstrassZWAt (z₀ s : PowerSeries F)` with `1 ≤ z₀.order`; then `subst f_α formalWPS` is a solution by substituting A2's fixed-point equation (PowerSeries.subst ring-hom laws + `subst_comp_subst`), and s is a solution by step 3-4 ⟹ equal.
5. NOTE for the worker: implement A2 parametrically as described (the ticket text of A2 shows the X-special case; the parametric form is the same proof — coordinate with FG-A2 if running in parallel, else just strengthen A2 when you get here).

#### Mathlib lemmas
`HahnSeries.ofPowerSeries` (+ injectivity), `PowerSeries.subst_comp_subst_apply`, `PowerSeries.le_order_subst` / project `order_subst`, `RingHom.map_*`.

#### Sources
[Sil] IV §1 p. 120 step "w₃ = f(z₃,w₃), while (IV.1.1b) says w(z) is the unique power series satisfying w = f(z,w); hence w₃ = w(z₃)" — the identical uniqueness-transport, used here at z₀ = f_α instead of z₃ (verbatim quote in plan/extraction §1.7.4).

#### Generality
Project context from FIS (any field with the standing instances); h_α only.

---

### [FG-B2] Coordinate expansions: x and y through w_α
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` | **Depends on**: FG-B1 | **Type**: lemmas
- **Progress**: DONE, axiom-clean. BOTH abstract-pair and isogeny forms shipped (the abstract ones fell out naturally and B5 wants them at the sum pair): `localExpand_x_pair`/`localExpand_y_pair` (same `{ξ η f}` + `h_weier/hξ_neg/hz` hypothesis pack as B1; conclusions `localExpand ξ = ofPS f / ofPS (w∘f)`, `localExpand η = −(ofPS (w∘f))⁻¹`) + `localExpand_pullback_x_gen`/`localExpand_pullback_y_gen` (isogeny corollaries, ticket shapes verbatim) + nonvanishing `subst_formalW_pair_ne_zero` (abstract) / `subst_formalIsogenySeries_formalW_ne_zero` (`w∘f_α ≠ 0`, via localExpand-injectivity from `−η⁻¹ ≠ 0`, NOT via order-of-subst) + `localExpand_pullback_z_eq_ofPowerSeries` (the packaged `hz` at pullbacks). Chart identities via abstract-field privates `x_eq_z_div_w`/`y_eq_neg_inv_w` + `congrArg (localExpand W)` (term-level — naive `rw` of `x = (−x/y)/(−y⁻¹)` would loop on the inner x). LANDMINE: `-x / y / -y⁻¹` parses `((-x)/y) / (-(y⁻¹))` — `neg_div_neg_eq` does NOT fire until after `rw [neg_div]`; `div_inv_eq` doesn't exist in this mathlib (use `div_div + mul_inv_cancel₀ + div_one`).

#### Statement
```lean
theorem localExpand_pullback_x_gen_eq (α) (h_α : …) :
    localExpand W (α.pullback (x_gen W))
      = HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α)
        / HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst (formalIsogenySeries W α) (formalWPS W)) := by sorry
theorem localExpand_pullback_y_gen_eq (α) (h_α : …) :
    localExpand W (α.pullback (y_gen W))
      = - (HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst (formalIsogenySeries W α) (formalWPS W)))⁻¹ := by sorry
```

#### Proof sketch
1. In KE: `x = t / wFunc` and `y = −wFunc⁻¹` (t = −x/y, wFunc = −1/y: check `t / wFunc = (−x/y)·(−y) = x` ✓) — two one-line field identities (y ≠ 0: `y_gen_ne_zero`).
2. Apply the ring hom `localExpand ∘ α.pullback` (`map_div₀`, `map_neg`, `map_inv₀`) + FG-B1 + step-1-of-B1's `localExpand(α^*t) = ofPS f_α`.
3. Nonvanishing bookkeeping: `subst f_α formalWPS ≠ 0` (its order is finite: = 3·order f_α via project `PowerSeries.order_subst`; or from w_α = localExpand(α^*wFunc) ≠ 0 since wFunc ≠ 0 and localExpand injective).

#### Mathlib lemmas
`map_div₀`, `map_inv₀`, `map_neg`; `HahnSeries.ofPowerSeries` casts vs `⁻¹` (division in the LaurentSeries FIELD — ofPS lands in the field, fine).

#### Sources
[Sil] IV §1 p. 115: "x = z/w and y = −1/w" (verbatim, the chart definition).

#### Generality
Same as B1.

---

### [FG-B3] The (z,w)-slope expansion (chord case)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` | **Depends on**: FG-B1, FG-A1 | **Type**: def + lemma
- **Progress**: DONE, axiom-clean. `zwSlope` def (ticket shape verbatim) + API `zwSlope_def` (rfl-lemma; `rw` can't unfold defs) + `zwSlope_comm`; headline `localExpand_zwSlope_eq` (ticket shape verbatim, hypotheses `h_α`/`h_β` x-pole + `h_t_ne`); the B4-wiring implication shipped PUBLIC as `pullback_localParam_ne_of_pullback_x_ne` (h_α + h_β + `α*x ≠ β*x` ⟹ `α*t ≠ β*t`; proof = B2-x both sides + `formalIsogenySeries_eq_of_pullback_localParam_eq` — t determines f coefficientwise BY DEFINITION, no B1 detour needed) + `formalIsogenySeries_eq_of_pullback_localParam_eq`. A1-spec substitution via privates: `mv_subst_sub` (substAlgHom map_sub transport, `(R := F)` explicit per A6 landmine), `subst_subst_X` (`subst b (subst (X i) φ) = subst (b i) φ` via `subst_comp_subst_apply` + `congr 1; funext; subst_X` — the ![·,·] landmine AVOIDED by proving the substituted spec `subst_formalSlopeBiv_spec` for a GENERAL `b : Fin 2 → F⟦X⟧` and only then instantiating at `![f_α,f_β]` + `simp only [Matrix.cons_val_zero, Matrix.cons_val_one]`); sign bookkeeping via abstract-CommRing `sub_swap_mul` instantiated by term (`linear_combination`-free on PowerSeries, per the ring-fails-on-PowerSeries landmine); final division `mul_div_cancel_left₀` after `← map_sub` packing. NEW LANDMINE: in a lemma STATEMENT, `PowerSeries.subst (MvPowerSeries.X i) φ` under an outer `MvPowerSeries.subst b` leaves the X's coefficient ring a STUCK metavariable (`Semiring ?m`) — ascribe `(MvPowerSeries.X i : MvPowerSeries (Fin 2) F)` in the statement (A1's spec dodged this because its ambient equation fixed the type).

#### Statement
```lean
/-- The (z,w)-chart slope of the chord through the α- and β-images of the generic point.
NOT the (x,y)-slope `addSlopePair`. -/
noncomputable def zwSlope (α β : Isogeny W.toAffine W.toAffine) : KE :=
  (α.pullback (-(y_gen W)⁻¹) - β.pullback (-(y_gen W)⁻¹))
    / (α.pullback (localParam W) - β.pullback (localParam W))

theorem localExpand_zwSlope_eq (α β) (h_α : …) (h_β : …)
    (h_t_ne : α.pullback (localParam W) ≠ β.pullback (localParam W)) :
    localExpand W (zwSlope α β)
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst ![formalIsogenySeries W α, formalIsogenySeries W β]
            (formalSlopeBiv W)) := by sorry
```

#### Proof sketch
1. Substitute FG-A1's spec at ![f_α, f_β] (MvPowerSeries.subst is a ring hom on these; `subst_comp_subst` collapses `subst ![f_α,f_β] (subst (X i) formalWPS)` to `subst f_i formalWPS` — i.e. w∘f_α, w∘f_β): get `(f_β − f_α) · λ∘ = w∘f_β − w∘f_α` in PowerSeries.
2. Push to Laurent via ofPS (ring hom), divide by `ofPS (f_β − f_α) = localExpand(β^*t − α^*t) ≠ 0` (h_t_ne + injectivity); rewrite numerator via FG-B1 ×2. Sign bookkeeping (the def above is (w_α−w_β)/(t_α−t_β) = (w_β−w_α)/(t_β−t_α) ✓ symmetric).
3. Note: h_t_ne vs the doubling dichotomy — the consumer (B4) case-splits on `α^*x = β^*x ∧ α^*y = β^*y` (the slope branch); show `¬(that)` ⟹ h_t_ne?? NO — t-pullbacks can coincide only if both coordinates do (t = −x/y and the curve equation… in fact α^*t = β^*t ∧ on-curve does NOT immediately give coordinate equality; the SAFE wiring: B4's chord case is conditioned on `α^*x ≠ β^*x`; derive h_t_ne FROM x ≠: if t_α = t_β and (chord) … derive contradiction via B2's x-formula: x_α = t_α/w_α and w determined by t through B1 ⟹ t_α = t_β ⟹ w_α = w_β ⟹ x_α = x_β. Clean ✓ — include this implication as a private lemma here.)

#### Mathlib lemmas
`MvPowerSeries.subst` ring-hom package (`subst_add/mul/X`), `subst_comp_subst_apply`.

#### Sources
[Sil] IV §1 p. 119: λ as the line's slope (the bivariate λ specialized at the two formal points — Silverman's z₁, z₂ play exactly the role of f_α, f_β).

#### Generality
Chord case only (x-pullbacks differ); tangent case is FG-B4a.

---

### [CLEANUP-FG-3] /cleanup on ChordExpansion.lean (cadence)
- **Status**: open | **Depends on**: FG-B1, FG-B2, FG-B3 | **Type**: cleanup

---

### [FG-B4] The chart-Vieta identity (chord case)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` | **Depends on**: FG-B2, FG-B3, FG-A3 | **Type**: theorem (the heavy compute)
- **Progress**: DONE, all axiom-clean `[propext,Classical.choice,Quot.sound]`, 0 sorries/maxHeartbeats, targeted + ROOT builds GREEN (8387), file now 1294 LOC. **B5-BINDING SHAPES**: line data `addLineC α β := α*y − addSlopePair α β * α*x`, `zwSlopeLine := -addSlopePair α β / addLineC`, `zwNuLine := -1 / addLineC` (+ `_def` rfl-lemmas). Headline = the CLEARED form (per step-4 design note), **ONE statement for BOTH branches** (no B5 case-split for the Vieta itself): `addPullback_vieta_cleared (α β) (h_α h_β : ord_∞ x-pullback < 0) (h_ni : AddNonInversePair α β) : (-addPullback_x_pair α β) * A = ((-α*(localParam) - β*(localParam)) * A - B) * (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)` with `A := 1 + C a₂*zwSlopeLine + C a₄*zwSlopeLine^2 + C a₆*zwSlopeLine^3`, `B := C a₁*zwSlopeLine + C a₂*zwNuLine + C a₃*zwSlopeLine^2 + 2 • (C a₄*zwSlopeLine*zwNuLine) + 3 • (C a₆*zwSlopeLine^2*zwNuLine)` (C := `algebraMap F KE`, `2 •`/`3 •` ℕ-smul mirroring chordA/chordB TERMWISE — B5 pushes both sides' nsmuls with map_nsmul symmetrically). **Free-ℓ VERDICT (the statement's CHECK)**: the Vieta identity with free ℓ + on-line-only is FALSE in the tangent case (counterexample y²=x³+1, P=(2,3) doubled, ℓ=1: cleared 0 ≠ −54; the `E(x₃,y₃′)`-strengthened variant ALSO false at ℓ=√6); the SHARED free-ℓ core is instead over the root-multiset hypotheses `he₁/he₂/he₃` (Φ = (x−x₁)(x−x₂)(x−x₃) coefficientwise) — branches differ ONLY in deriving he₂/he₃ (chord: divided differences of Φ(x₁)=Φ(x₂)=0, needs x₁≠x₂; tangent: Φ(x₁)=0 + Φ′(x₁)=0 ⟺ the cleared tangent-slope relation). Free-var privates (ALL `linear_combination`, offline-derived certs, no iteration needed except 2 sign-flips): `vieta_Ac` (c³A(λ) = ∏(ℓxᵢ+c); cert −ℓc²·he₁ − ℓ²c·he₂ − ℓ³·he₃), `vieta_Bc` (c³B(λ,ν) = Σᵢxᵢ∏_{j≠i}(ℓxⱼ+c); cert −c²·he₁ − 2ℓc·he₂ − 3ℓ²·he₃), `chord_e₂`/`chord_e₃` (`mul_left_cancel₀ (sub_ne_zero.mpr hx)` + cert `h₁ − h₂ + M₂·hline + M₁·hc` with Mᵢ = (yᵢ+ℓxᵢ+c+a₁xᵢ+a₃), e₃-version x-weighted), `tangent_e₂` (cert `htan + (2ℓ+a₁)·hc`), `tangent_e₃` (cert `x₁·htan + (x₁(2ℓ+a₁) − M₁)·hc − h₁`), `vieta_cleared_poly` (the polynomial Vieta; after `rw [← hy₁', ← hy₂']` the cert is EXACTLY `(−x₃Y₁Y₂ − (x₁Y₂+x₂Y₁)Y₃)·hAc + Y₁Y₂Y₃·hBc`, Yᵢ := ℓxᵢ+c), `vieta_assembly` (divided-λν form: `field_simp` then `linear_combination hpoly` — multiplier 1 on the nose). **c≠0 bricks**: `addLineC_ne_zero_of_x_ne {α β} (h_α h_β h_x)` (c=0 ⟹ t_α=t_β, contra `pullback_localParam_ne_of_pullback_x_ne`) + `addLineC_ne_zero_of_x_eq {α β} (h_x h_ni)` (NO pole hyp! `c·(2y₁+a₁x₁+a₃) = −α*(x³−a₄x−2a₆+a₃y)` by `linear_combination 2·Eq − x₁·htan`, then NEW `x_gen_cubic_ne_zero : x_gen³ − C a₄·x_gen − 2·C a₆ + C a₃·y_gen ≠ 0` via mathlib `Affine.CoordinateRing.smul_basis_eq_zero` power-basis independence, p = X³−a₄X−C(2a₆) monic-coeff-3). **Bridges (item 4)**: `zwSlopeLine_eq_zwSlope {α β} (h_α h_β h_x)` (cleared two-point identity + `div_eq_div_iff`) and `zwNuLine_eq_sub {α β} (hc) : zwNuLine = α*(−y⁻¹) − zwSlopeLine·α*(localParam)` (branch-free). **Chord λ-leg**: `localExpand_zwSlopeLine_of_x_ne {α β} (h_α h_β h_x) : localExpand (zwSlopeLine W α β) = ofPS (MvPowerSeries.subst ![f_α, f_β] (formalSlopeBiv W))` (bridge + B3). **ν-legs**: parametric `localExpand_zwNuLine_eq {α β} (h_α h_β hc h_lam)` + corollaries `localExpand_zwNuLine_of_x_ne (h_α h_β h_x)` / `localExpand_zwNuLine_of_x_eq (h_α h_β h_x h_ni)`, conclusion `localExpand (zwNuLine W α β) = ofPS (subst ![f_α, f_β] (formalNuBiv W))`. Shared helpers (public): `pullback_weierstrass_eq` (the algebraMap-spelled curve equation — the form linear_combination wants), `pullback_y_gen_ne_zero`, `pullback_y_eq_of_x_eq`, `pullback_u_ne_zero_of_x_eq`, `addSlopePair_mul_u_of_x_eq` (the cleared tangent slope = htan). LANDMINES: (1) `(W_KE W).toAffine.aᵢ` vs `algebraMap F KE W.aᵢ` are rfl-equal but DISTINCT ring/linear_combination ATOMS — state everything algebraMap-spelled and convert mathlib-derived facts by have-with-ascription + `exact h` (B1's :206 pattern); `addPullback_x_pair α β = ℓ²+a₁ℓ−a₂−x₁−x₂` and the negY-unfold are `rfl`. (2) `Affine.negY_negY _ _` with a have-ascription identifies `negY X₃ (addPullback_y_pair) = ℓ(X₃−x₁)+y₁` (addY/negAddY unfold by defeq). (3) `simp only [map_mul]` splits INSIDE `Polynomial.C (2*a₆)` (C is a RingHom) — fold with the C-transport lemma in the SAME simp set, not sequential rw. (4) `field_simp` picks up ≠0 facts from the local context — `have hxx : x₁ − x₂ ≠ 0` before it.

#### Statement
```lean
/-- The z-coordinate of the third intersection point, in KE: with R₃ = (addX…, line-value-Y),
z(R₃) = −X₃/Y₃' equals the Vieta value −t_α − t_β − B/A formed from the (z,w)-slope.
Chord case. All modulo the two curve equations. -/
theorem zR3_eq_vieta_chord (α β) (hx : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    let ℓ := addSlopePair α β   -- the (x,y)-slope, chord branch
    let X₃ := addPullback_x_pair α β
    let Y₃' := (W_KE W).toAffine.negY X₃ (addPullback_y_pair α β)  -- the PRE-negation line value
    let λz := zwSlope α β
    let νz := α.pullback (-(y_gen W)⁻¹) - λz * α.pullback (localParam W)
    (-X₃ / Y₃')
      = -(α.pullback (localParam W)) - β.pullback (localParam W)
        - (C a₁*λz + C a₂*νz + C a₃*λz^2 + 2•(C a₄*λz*νz) + 3•(C a₆*λz^2*νz))
          / (1 + C a₂*λz + C a₄*λz^2 + C a₆*λz^3) := by sorry
```
(C a_i := algebraMap F KE W.a_i; binder spelling per file.)

#### Proof sketch
**This is a rational-function identity in the function field** — no series yet. Primary route:
1. mathlib's `addX x₁ x₂ L = L² + a₁L − a₂ − x₁ − x₂` is ALREADY the (x,y)-Vieta; `Y₃' = L·(X₃ − x_α) + y_α` the line value. So the LHS is an explicit rational expression in `(x_α, y_α, x_β, y_β, L)` with `L = (y_α−y_β)/(x_α−x_β)`.
2. The RHS's λz, νz are explicit in the same four coordinates: `λz = (−y_α⁻¹+y_β⁻¹)/(−x_α/y_α + x_β/y_β)`, t's likewise. EVERYTHING is rational in (x_α, y_α, x_β, y_β).
3. The identity is then a `field_simp` + `linear_combination`/`ring` computation MODULO the two Weierstrass equations (for (x_α,y_α) and (x_β,y_β)) — the project's precedent for exactly this scale is `kaehler_D_addPullback_x_pair_ring_identity` (SilvermanIV14:3462, a free-variable linear_combination core): FOLLOW THAT PATTERN — first state a FREE-VARIABLE version over a generic field (variables x₁ y₁ x₂ y₂ with two equation hypotheses + the nonvanishing side conditions: x₁ ≠ x₂, y's ≠ 0, denominators ≠ 0), prove by field_simp + linear_combination with the two equations; then instantiate at pullbacks (generic_equation `MulByIntPullback:81` supplies the curve equations for pullbacks; y ≠ 0 from `ψ_ff_ne_zero`-style/`y_gen_ne_zero` + injectivity).
4. Denominator nonvanishing inventory (each needs a lemma or hypothesis): `x_α ≠ x_β` (hx), `y_α, y_β ≠ 0` (pullback-injective ∘ y_gen_ne_zero), `Y₃' ≠ 0` (the sum is not 2-torsion-at-generic — CAUTION: this can fail for special pairs? Y₃' = 0 ⟺ R₃ is 2-torsion-shaped ⟺ the SUM point has y-coordinate = negY ⟺ … At the GENERIC point this is an honest nonvanishing fact: Y₃' is a nonconstant function unless… SAFEST: add `(hY : Y₃' ≠ 0)` as a hypothesis to this ticket's identity and discharge it in B5 from h_ni + the established pole orders (Y₃' has a pole at O of order 3e-ish by the B5-side order computation `orderTop = −3` analogue — the (id,−π) template proved exactly this at SilvermanIV14:1898; in B5 the general-pair analogue comes from the assembled identity'd RHS having a genuine pole... DESIGN NOTE: to avoid circularity, prove in B5 first the RHS-side orderTop facts (z₃∘-substituted series has orderTop ≥ 1, A∘-unit etc. — pure series), conclude LHS-denominator ≠ 0 by contraposition through the identity applied in a cleared-denominator form. CONCRETELY: state THIS ticket in the CLEARED form `(-X₃) * A-denom * (t-sum-denoms…) = (vieta-numerator) * Y₃' * …` — polynomial identity, NO division, NO nonvanishing hypotheses beyond hx and y's ≠ 0. Then B5 divides at will under its own nonvanishing facts. DO THE CLEARED FORM.)
5. A-denominator `1 + a₂λz + …` relation to mathlib's slope: NOT needed as nonvanishing here if cleared. (It IS a unit after expansion — B5's job.)

#### Mathlib lemmas
`WeierstrassCurve.Affine.slope_of_X_ne` (the chord-branch formula), `Affine.addX`, `Affine.negY`, `Affine.addY`/`addY'` spellings (read mathlib's current API: in recent mathlib `addY W x₁ x₂ y₁ L = negY (addX …) (addY' …)`-shaped — grep `addY'`/`negAddY`; the project's AdditionPullback.lean:553-560 shows the spellings in use), `field_simp`, `linear_combination`.

#### Sources
[Sil] IV §1 pp. 119–120: the substituted cubic + "looking at the quadratic term … the third root" (Vieta), with the CORRECTED z₃ (plan §References). The (x,y)↔(z,w) chart correspondence is implicit in Silverman (same projective line); here it is the computational content.

#### Generality
Free-variable core over any field K with two Weierstrass-equation hypotheses (maximal reuse: state it for `WeierstrassCurve K` + variables, NOT for pullbacks); instantiation layer thin.

---

### [FG-B4a] The tangent case (doubling)
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` | **Depends on**: FG-B4 (pattern), FG-A1 (diagonal) | **Type**: theorem
- **Progress**: DONE, axiom-clean, **NO separability hypothesis — the inseparable tangent case (`f_α′ = 0`, e.g. α = β = Frobenius) is COVERED**: the route is the *substituted univariate implicit-differentiation identity* (never the chain rule, never dividing by `f′`), exactly the brief's resolution. The cleared Vieta itself is FG-B4's branch-uniform headline (tangent he₂/he₃ from `tangent_e₂/e₃` at `htan := addSlopePair_mul_u_of_x_eq`); this ticket's deliverable is the tangent λ-leg. Chain: (i) `derivative_formalW_key` (private): `d⁄dX F (formalW W) * (1 − (C a₁*X + C a₂*X^2 + 2*(C a₃*w) + 2*(C a₄*(X*w)) + 3*(C a₆*w^2))) = 3*X^2 + C a₁*w + 2*(C a₂*(X*w)) + C a₄*w^2` (NUMERAL-mul on the series side, matching `derivative_pow`'s output style) — differentiate `formalW_fixedPoint` by `simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X, PowerSeries.derivative_C, smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]`, close by abstract-CommRing `implicit_diff_rearrange` taking the simp output VERBATIM as its h-shape (`linear_combination h`). (ii) `subst_derivative_formalW_key (f) (hf : PowerSeries.HasSubst f)` (private): the same identity at `(f, w∘f)` — `congrArg (substAlgHom hf)` + TWO-stage simp (`map_*` first, then `coe_substAlgHom, subst_X hf, subst_C' f hf`). (iii) `tangent_zwslope_core` (private free-var): `−ℓ/c · (1 − fw(−x₁/y₁, −y₁⁻¹)) = fz(−x₁/y₁, −y₁⁻¹)` mod {curve eq, cleared htan}; `subst hcdef; field_simp;` cert `(−3ℓ)·h₁ + y₁·htan` (offline-derived, first try); KE form `zwSlopeLine_mul_eq_of_x_eq` (private). (iv) headline `localExpand_zwSlopeLine_of_x_eq {α β} (h_α) (h_x : α*x = β*x) (h_ni) : localExpand (zwSlopeLine W α β) = ofPS (MvPowerSeries.subst ![f_α, f_β] (formalSlopeBiv W))` — t-pullbacks equal ⟹ `f_β = f_α` rewrite, `formalSlopeBiv_diag` to `w′∘f`, push (iii) through localExpand (haves `hfw`/`hfz` matching both sides' factor expansions), push (ii) through ofPS, cancel the common factor `1 − ofPS(fw∘)` by `mul_right_cancel₀` (≠0 via ofPowerSeries-injectivity + constantCoeff = 1, brick `constantCoeff_subst_formalW`). Tangent ν-leg = `localExpand_zwNuLine_of_x_eq` (see FG-B4). NEW LANDMINES (BINDING for FG-C4/P, which differentiates series): **`Derivation.leibniz`- and `map_mul`-headed simp/rw rewrites do NOT match through the `d⁄dX`/`substAlgHom` coercions under the default `backward.isDefEq.respectTransparency`** — set it `false` per-lemma (mathlib's own `PowerSeries.derivative_pow` does exactly this); **`map_ofNat` does not FIRE as a simp lemma** on `ofPowerSeries _ 2`/`constantCoeff 2`-shaped terms though it APPLIES term-level — add `show ofPS (2 : F⟦X⟧) = 2 from map_ofNat _ 2`-instances to the simp set; `simp only` needs `Nat.reduceSub` spelled for the `3−1` exponents (A6 landmine confirmed); the constantCoeff-of-`w∘f` brick is the project's `constantCoeff_subst_formalW W _ hf0` (mathlib has no `constantCoeff_subst_eq_zero` under that name).

#### Statement
Same shape as FG-B4 with: hypothesis `α.pullback (x_gen W) = β.pullback (x_gen W) ∧ α.pullback (y_gen W) = β.pullback (y_gen W)` (the tangent branch of mathlib's `slope`; under it f_α = f_β at the series level), `ℓ := slope`'s tangent value, and `λz := ` the (z,w)-tangent slope — DEFINE it as the value forced by the chart: `λz_tan := (3 x_α² + 2a₂x_α + a₄ − a₁y_α) / (…chart-transformed…)` — DESIGN STEP (part of ticket): derive the (z,w)-tangent slope from the (x,y) one by the chart's derivative transform (z = −x/y, w = −1/y: dz, dw in terms of dx, dy via the curve's differential; λz_tan = dw/dz at the point = (w-numerator-derivative)/(z-…) — concretely λz_tan = (y_α⁻²·dy-form)/((−1/y + x/y²·dy/dx-form)) …); the SERIES-side target: `localExpand λz_tan = ofPS (subst ![f_α,f_α] λ_biv) = ofPS (subst f_α (derivative formalWPS))` (FG-A1 diagonal). Then the cleared Vieta identity, tangent branch.

#### Proof sketch
1. Tangent (z,w)-slope: from w = f(z,w) implicit differentiation: `w′ = f_z + f_w·w′` ⟹ `w′ = f_z/(1−f_w)` with f_z = 3z² + a₁w + 2a₂zw + a₄w², f_w = a₁z + a₂z² + 2a₃w + 2a₄zw + 3a₆w². Define `λz_tan := (3t² + a₁wf + 2a₂t·wf + a₄wf²) / (1 − a₁t − a₂t² − 2a₃wf − 2a₄t·wf − 3a₆wf²)` AT the pullback (t := α^*t, wf := α^*wFunc) — all in KE.
2. Series side: `localExpand λz_tan = ofPS (subst f_α (derivative formalWPS))`: differentiate the fixed-point equation `formalWPS = weierstrassZWAt X formalWPS` formally (PowerSeries.derivative + product rule) to get `w′·(1−f_w∘) = f_z∘`; substitute f_α; both numerator and denominator localExpand-match by B1/B2-style ring-hom pushing; denominator is a unit (constant term 1: f_w has order ≥ 1). Combine with FG-A1's diagonal lemma.
3. Chart compatibility: show mathlib's tangent slope ℓ_tan relates to λz_tan the same way the chord slopes relate (the SAME rational chart-transform — prove the transform identity once in B4's free-variable style with ℓ as a FREE variable subject to no chord constraint, if possible — RE-EXAMINE B4: if B4's cleared identity can be stated with ℓ free (not substituted by the chord value), then B4 covers BOTH branches and B4a only supplies the two slope-expansion lemmas. PREFER THAT FACTORING: B4-cleared-with-free-ℓ + per-branch "localExpand(chart-transform of ℓ) = λ∘" lemmas (chord: B3; tangent: this ticket). The Vieta identity is line-vs-curve algebra and does not care which line.)
4. Doubling Vieta then follows from B4-with-free-ℓ at the tangent ℓ.

#### Mathlib lemmas
`Affine.slope_of_Y_ne` (tangent branch formula: `(3x₁² + 2a₂x₁ + a₄ − a₁y₁)/(y₁ − negY)`), `PowerSeries.derivative` API (`derivative_mul` etc. — mathlib has `PowerSeries.derivative` with Leibniz; project `FormalGroup/PDeriv` for the Mv side if needed).

#### Sources
[Sil] dodges doubling (z₁, z₂ independent indeterminates; Example 3.1.3's footnote concedes the z = z′ case needs "an explicit, albeit messy, calculation with power series and the duplication formula" — p. 123, quoted in the extraction). This ticket IS that missing computation, organized via implicit differentiation instead of the duplication formula.

#### Generality
Tangent branch; char-free (no division by 2 — the tangent slope formula is the a₁/a₃-aware mathlib one).

---

### [CLEANUP-ALL-FG] /cleanup-all (pre-milestone)
- **Status**: open | **Depends on**: all open A/B tickets except FG-B5 | **Type**: cleanup

---

### [FG-B5] ★ MILESTONE: BRIDGE-003 — `formalIsogenySeries_add`
- **Status**: done (2026-06-11) | **File**: `HasseWeil/ChordExpansion.lean` (statement MOVES here from FIS:485 — grep `formalIsogenySeries_add` for by-name consumers first; expected none (sorried); Genuine takes the conclusion as hypothesis h_iv14) | **Depends on**: FG-B1..B4a, FG-A5, FG-A6, CLEANUP-ALL-FG | **Type**: theorem
- **Progress**: **DONE — BRIDGE-003 PROVEN, axiom-clean `[propext, Classical.choice, Quot.sound]`, NO sorryAx**; targeted + ROOT builds GREEN; statement relocated VERBATIM from FIS:485 (FIS keeps a doc-pointer section; FIS census now exactly 1 sorry = BRIDGE-001 :364). Consumer shape-check `addPullback_x_pair_sum_reduces_of_iv14_witness W h_α₁ h_α₂ h_y_sum_ne h_base (formalIsogenySeries_add W α₁ α₂ h_α₁ h_α₂ h_ni)` TYPECHECKS over finite K (scratch-verified, deleted). **PLAN DEVIATION (major simplification): NO pole bound on `X₃` and NO basepoint hypothesis are needed anywhere** — the ticket's step-3 `hξ_neg`-derivation (FIS:1375 back-conversion, which would have needed the UNAVAILABLE `h_base : ord X₃ ≤ 0`) is bypassed: the sum pair's **w-leg comes from the LINE** (the third intersection point lies on `y = ℓx + c`, so `−1/Y₃′ = λ·z₃′ + ν` is pure chart algebra; its expansion is `ofPS (λ∘·z₃∘ + ν∘)`), and the new no-pole Hensel brick `subst_formalW_of_expansions` (= `localExpand_wPair` with the reconstruction replaced by a SUPPLIED expansion; constant-coeff-zero hypotheses only) identifies it with `w∘z₃∘`. Equally, the X₃ = 0 degenerate case needs NO split (the final field algebra is uniform in `f₃ = 0`). Proof structure: (1) per-branch legs `⟨hc, h_lam, h_nu⟩` via one `by_cases` on `α*x = β*x` (B4/B4a legs), everything after is branch-uniform; (2) cleared Vieta `nsmul`-normalised (`simp only [nsmul_eq_mul, Nat.cast_ofNat]`, B4's own pattern) then pushed by the new abstract `cleared_push` (transports A/B/T-sum factors as WHOLE atoms via `simp only [← map_*]` folds — dodges the simp-splits-the-composite conflict) against the series mirror `formalZ3_mul_chordA` (`linear_combination (-(chordB W)) * chordA_inv_mul W`) substituted+pushed; cancel the unit `ofPS A∘` (`constantCoeff = 1` via `subst_chordA_eq`) ⟹ `hXY : −localExpand X₃ = ofPS f₃ · localExpand Y₃′`; (3) `Y₃′ ≠ 0` by the c-trick: `Y₃′ = 0 ⟹ X₃ = 0` (hXY + injectivity) `⟹ Y₃′ = addLineC` (negY_negY line value at X₃ = 0) `= 0`, contra `hc`; (4) z-leg `hz₃` by `map_div₀` + `mul_div_cancel_right₀`; (5) w-leg per the line + Hensel as above; (6) NEW reusable `localExpand_neg_div_negY_of_expansions` (the IV §1 p.120 `i(z₃)` move: z+w expansions ⟹ the NEGATED chart coordinate expands to `ofPS (i∘f)`; needs NO curve equation, NO poles — internals: substituted FG-A5 spec via `PowerSeries.substAlgHom` push, `hU_ne`/`hWb_ne` nonvanishing via constant-coefficient + injectivity (B4a hD_ne pattern), final abstract `neg_div_negY_field` over a generic field); (7) `negY_negY` converts `negY X₃ Y₃′ = Y₃`, then `formalGroupLaw_eq_chord` + the new composition brick `mv_subst_powerSeries_subst` (`subst b (PowerSeries.subst g φ) = PowerSeries.subst (subst b g) φ` via `MvPowerSeries.subst_comp_subst_apply`, mirroring `subst_subst_X`) close. NEW decls (11, ~390 LOC): private `cleared_push`/`neg_div_negY_field`/`mv_subst_C`(local copy of the FormalGroupLawSpec private)/`mv_subst_powerSeries_subst`/`formalZ3_mul_chordA`/`subst_chordA_eq`/`subst_chordB_eq`(numeral form, `rw [chordB]; ring` converts the nsmuls INSIDE Mv where ring works)/`subst_formalZ3_mul_chordA` + public `subst_formalW_of_expansions`/`localExpand_neg_div_negY_of_expansions`/`formalIsogenySeries_add`. NEW LANDMINES: (a) after a `rw [..., ← map_neg]` fold whose result is syntactically the target, the closing `rfl` of `rw` can FAIL on `ofPS (-(f))`-shaped goals (Neg instance-path); append an explicit `rfl` line (default-transparency closes it). (b) `map_neg`/`map_ofNat` on `ofPowerSeries`/`substAlgHom` applications: USE the `show ... from map_neg _ _`/`map_ofNat _ 2` term-level instances inside `rw`/`simp only` sets (B4a landmine confirmed again); `map_add/map_mul/map_sub/map_pow/map_one` all fire normally on `ofPS`-of-PowerSeries-ops. (c) The substAlgHom pushes all carry `set_option backward.isDefEq.respectTransparency false in` (B4a pattern) — with it, `map_neg` DOES fire through `MvPowerSeries.substAlgHom` in `simp only` (subst_formalZ3_mul_chordA worked first try).

#### Statement
Exactly the current FIS:485-496 statement (quoted in plan-iv1.md §Goal), relocated.

#### Proof sketch
1. Case-split per mathlib's `slope`: chord (`α^*x ≠ β^*x`) vs tangent (x equal ∧ y equal); the residual case (x equal ∧ y ≠ y — i.e. y_β = negY) is EXCLUDED by `h_ni` (AddNonInversePair) — wait, h_ni excludes x-AND-y-negY-matching; with x equal, either y equal (tangent) or y = negY-of-other (excluded). ✓ Total.
2. Per branch: the cleared B4 identity + the slope-expansion lemma (B3 / B4a) + B2's coordinate expansions give: `localExpand(−X₃/Y₃-pre-negation-form…)` — assemble to `localExpand(z(R₃)) = ofPS (subst ![f_α,f_β] (formalZ3 W))` (the substituted Vieta value: A∘ is a unit — constant coeff 1; division realized in Laurent then pulled back to PowerSeries via ofPS-injectivity; orderTop ≥ 1 of the result from constantCoeff_formalZ3 + subst).
3. Negation: the target's LHS is `−X₃/Y₃` with Y₃ the POST-negation y (addPullback_y_pair). Relate: `−X₃/Y₃ = X₃/(Y₃' + a₁X₃ + a₃-form)` (negY unfold). Apply FG-A5's ratio spec AT the sum point: the pair (X₃, Y₃') satisfies the curve equation (`addPullback_pair_equation` AdditionPullback:571), so the same chart algebra that proves A5's ratio for the generic point proves `localExpand(−X₃/Y₃) = ofPS (subst (z(R₃)-series) (formalInversePS W))` — concretely: push A5's PowerSeries identity through subst by z(R₃)-series (subst_comp_subst) and match against the B2-style expansions of X₃, Y₃ in terms of (z(R₃)-series, w∘z(R₃)-series) — which hold by B1 APPLIED TO THE SUM PAIR: define the sum point's t-pullback `t₃ := −X₃/Y₃' …` hmm — CLEANER: R₃'s functions (X₃, Y₃') form a "point-like pair" satisfying the curve equation with z-function `zR₃ := −X₃/Y₃'`... wait sign: z = −x/y at R₃: zR₃ = −X₃/Y₃'. Re-run B1's uniqueness argument verbatim for this pair (B1 should be stated/refactored to take an ABSTRACT pair (ξ, η) ∈ KE² satisfying the curve equation + pole condition, not an isogeny — DO THAT in B1 from the start: `localExpand_wPair` for any equation-satisfying pair with x-pole; isogeny pullbacks and the R₃ pair are two instantiations). Then w-of-R₃ = w∘(zR₃-series), x = z/w etc., and the negation ratio assembles.
4. Compose: `subst (subst ![f,g] z₃) i = subst ![f,g] (subst z₃ i)` (`MvPowerSeries.subst_comp_subst`) `= subst ![f,g] F` (FG-A6). Descend `ofPowerSeries`-equalities to the stated form.
5. Sanity: `#print axioms` the result; verify the conclusion is verbatim-acceptable to `Genuine.lean:1298`'s h_iv14 slot (build a scratch `example := addPullback_x_pair_sum_reduces_of_iv14_witness … (formalIsogenySeries_add …)` — the restatement strike already verified this shape-match once; re-verify post-move).

#### Mathlib lemmas
`MvPowerSeries.subst_comp_subst_apply`, `HahnSeries.ofPowerSeries` injectivity, field algebra in LaurentSeries.

#### Sources
[Sil] IV §1 p. 120: "F(z₁,z₂) = i(z₃(z₁,z₂))" + the w₃-uniqueness step (extraction §1.7.4–1.7.6).

#### Generality
Exactly the restated :485 hypotheses (h_α, h_β poles + h_ni). No Fintype/IsAlgClosed/CharP.

---

### [CLEANUP-FG-4] /cleanup on ChordExpansion.lean (final per-file)
- **Status**: open | **Depends on**: FG-B5 | **Type**: cleanup

---

### [FG-C1] Wall A discharge
- **Status**: done (2026-06-11) | **File**: `HasseWeil/Verschiebung/Genuine.lean` (+ import ChordExpansion — cycle-checked: ChordExpansion's closure has no Verschiebung files) | **Depends on**: FG-B5 | **Parallel**: with C2 | **Type**: theorem (close the :1356 sorry)
- **Progress**: **DONE — `addPullback_x_pair_x_ord_neg` PROVEN, axiom-clean `[propext, Classical.choice, Quot.sound]`; Genuine.lean sorry-free; targeted + ROOT builds GREEN.** **PLAN DEVIATION (simplification): the proof does NOT consume `formalIsogenySeries_add`/h_iv14 at all** — neither the FIS:1375 back-conversion (which needs the unavailable `ord X₃ ≤ 0`/`Y₃ ≠ 0`/`X₃ ≠ 0`) nor a B5-extraction was needed. Route that landed = pure `ord`-arithmetic on the FG-B3/B4 `(z,w)`-chart line data, by contradiction from `¬(ord X₃ < 0)` i.e. `0 ≤ ord X₃`: (1) the chord-branch legs `localExpand_zwSlopeLine_of_x_ne`/`localExpand_zwNuLine_of_x_ne` (h_x_ne ⟹ always chord; NO branch split) + `constantCoeff_formalSlopeBiv`/`_formalNuBiv` + `constantCoeff_subst_bivariate_eq_zero` + `orderTop_ofPowerSeries_pos_of_order_pos` + R5b ⟹ `0 < ord λ`, `0 < ord ν`; (2) `ν = −1/c` (`zwNuLine_def`) ⟹ `ord c =: mc ≤ −1`; `λ = −ℓ/c` ⟹ `ord ℓ ≥ mc+1` ⟹ `ord (ℓ·X₃) ≥ mc+1` (zero cases via `le_top`); (3) `(X₃, Y₃′ := negY X₃ Y₃)` on the curve (`equation_neg` + `addPullback_pair_equation`); with `0 ≤ ord X₃` the monic quadratic in `Y₃′` (rearranged `Y₃′·Y₃′ = X-terms − a₁X₃Y₃′ − a₃Y₃′`, ultrametric min-chain mirroring FIS:1424-1439) forces `0 ≤ ord Y₃′`; (4) line `c = Y₃′ − ℓX₃` (`negY_negY` + `addLineC_def` + ring) ⟹ `mc ≥ min(0, mc+1) = mc+1`, absurd. The B5-context depth enters ONLY through the B4 legs (the chart slope/intercept positive order — invisible to naive (x,y)-ord, the −6 tie). NEW LANDMINES (all confirmed by build failures): (a) **rw is broken across the KE-vs-`(W_smooth W).FunctionField` instance-path divide** — `rw [(W_smooth W).ordAtInfty_zero/_mul/...]` fails "did not find pattern" even on display-identical goals whenever the lemma's fixed subterms (0, *, ^) elaborate at the FF path while the goal's are KE-path; `exact`/term-mode (`le_of_le_of_eq`, `.trans`, `le_of_eq`) bridges fine (full-transparency unification). Local-hyp rewrites fire normally. (b) `rw [sq]/[pow_succ]` also fail there — use PRODUCT spelling (`X₃*X₃*X₃`) in the local `have`s; `linear_combination` bridges spellings against `equation_iff`'s pow-form. (c) A bare `(W_smooth W).ordAtInfty (addSlopePair α₁ α₂)` as a CALC middle term re-elaborates `addSlopePair`'s implicit W to `(W_smooth W).toAffine` (unifier goes through `SmoothPlaneCurve.FunctionField` unfolding) and dies on `IsElliptic (toAffine (W_smooth W).toAffine)` — avoid re-stating ord-of-project-terms in calc middles; keep them in `have`s whose statements you control, or pin `(W := W)`. Downstream de-tainted (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`): `addPullback_x_pair_sum_reduces_to_O`, `addPullback_x_pair_ord_neg_of_summands_reduce`, `genuineIsogSmulSubV_universal_unconditional`, `WallA.genuineIsogSmulSub_degree_eq_signed_closed`.

#### Statement
Existing `addPullback_x_pair_x_ord_neg` (Genuine.lean:1350-1356, quoted in the audit) — fill the sorry.

#### Proof sketch
1. The shipped chain: `formalIsogenySeries_add` (now proven) fills `h_iv14` of `addPullback_x_pair_sum_reduces_of_iv14_witness` (:1298) — but the TARGET :1350 needs the ord-negativity, whose shipped derivation is `orderTop_localExpand_z_sum_pos_of_iv14_identity` (FIS:1844: h_iv14 + poles ⟹ 0 < orderTop (localExpand z_sum)) + the back-conversion `ordAtInfty_x_neg_of_equation_of_neg_div_pos` (FIS:1375). Read :1376/:1456's existing wiring (`addPullback_x_pair_sum_reduces_to_O` derives the triple FROM the :1350 sorry today — INVERT: prove :1350 from the iv14 witness route, then :1376/:1456 stay as-are).
2. Hypothesis delta: :1350 has `h_x_ne` (chord) — h_ni follows (x differ ⟹ AddNonInversePair via `AddNonInversePair_of_x_ne` AdditionPullback:681). Base field: Genuine is over finite K — fine (B5 is field-general).
3. Expect ~20-40 LOC. Then grep Genuine for further consumers of the closed sorry and confirm the file's sorry count hits 0; axiom-audit `genuineIsogSmulSubV_universal_unconditional`-side consumers if they now go clean (report, don't chase).

#### Mathlib lemmas — n/a (project wiring).
#### Sources — [Sil] IV.1.4-consequence; the project chain (FIS:1844 docstring cites it).
#### Generality — as stated at :1350.

---

### [FG-C2] `formalIsogenySeries_FGL_additivity` (:51) via instantiation
- **Status**: done (2026-06-11) | **File**: `HasseWeil/GapQfKernel.lean` (+ import ChordExpansion; cycle-check: ChordExpansion must not import GapQfKernel — it doesn't) | **Depends on**: FG-B5 | **Parallel**: with C1 | **Type**: theorem (close the :51 sorry)
- **Progress**: **DONE — `formalIsogenySeries_FGL_additivity` PROVEN, axiom-clean; GapQfKernel census 4 → 3 (`:651`/`:663` III.1.5 pair + `:1303` P remain); targeted + ROOT builds GREEN.** Route exactly per ticket: B5 at `([k],[1])` (h_α/h_β via `ordAtInfty_mulByInt_x_neg` + `mulByInt_pullback_x`), coordinate identification, `← mulByInt_pullback_localParam` + `localExpand_pullback_localParam`, `ofPowerSeries_injective`. **DEVIATIONS/LANDMINES**: (a) the ticket's in-file `zsmul_genericPoint_eq`-+-`add_of_X_ne` dance CANNOT run inside GapQfKernel — `rw [add_zsmul]` fails ("pattern not found", display-identical) and even term-mode `add_zsmul (genericPoint W) _ _` whnf-TIMEOUTS: the `(W_KE W).toAffine.Point` zsmul/instances diamond under GapQfKernel's import set (the known MulByIntAddRecurrence module-docstring diamond). FIX: do ALL Point-group reasoning in the canonical-instance files — NEW `addX_addY_mulByInt_genericPoint_eq_succ` (chord, `[m] ⊞ P` order, secant-spelled) + `addX_addY_mulByInt_one_self_eq_two` (tangent, `slope_of_Y_ne`-quotient-spelled) in `EC/GenericPointZsmul.lean` (mirrors of the existing :785/:391 with the zsmul-split `rw [← h_m, ← h_m1, add_zsmul, one_zsmul]`), then NEW `addPullback_xy_pair_mulByInt_one_eq_succ (m) (hm : m ≠ 0) (hm1 : m+1 ≠ 0)` + `addNonInversePair_mulByInt_one` in `EC/MulByIntAddRecurrence.lean` (unfold pair-defs, fold pullbacks, `slope_of_X_ne`/`slope_of_Y_ne` eliminate `slope` — the `DecidableEq K(E)` diamond — then exact the GenericPointZsmul helpers; internal `m = 1`/`m ≠ 1` split, `m = −1` killed by `hm1`). GapQfKernel consumes both as terms — zero Point-instance contact. (b) `mulByInt_y_ne_zero` + `mulByInt_pullback_localParam` MOVED up the file (were below :51, "unknown identifier"). (c) GapQfKernel imports += ChordExpansion + EC.MulByIntAddRecurrence (cycle-checked). (d) In `addNonInversePair_mulByInt_one`'s tangent branch the rw-chain must NOT include both `hpmy` and `hp1y` (after `rcases … with rfl` they coincide; second rw finds nothing). **Audit (verbatim)**: `formalIsogenySeries_FGL_additivity`, `coeff_one_formalIsogenySeries_mulByInt_eq`, `coeff_one_formalIsogenySeries_mulByInt_of_neg`, `addPullback_xy_pair_mulByInt_one_eq_succ`, `addNonInversePair_mulByInt_one`, both GenericPointZsmul helpers — ALL `[propext, Classical.choice, Quot.sound]`. `omegaPullbackCoeff_mulByInt_via_formalGroup` + `_p_eq_zero_via_formalGroup` = `[propext, sorryAx, Classical.choice, Quot.sound]` — the ticket's "expect ALL clean" was over-optimistic: they consume `pullback_invariantDiff_coeff_zero` (P, :1303, FG-C4) and `omegaPullbackCoeff_mem_F` (III.1.5 pair :651/:663, FG-D1); L-F1 is no longer among their blockers.

#### Statement
Existing GapQfKernel:43-51 (quoted in the audit) — fill the sorry.

#### Proof sketch
1. Apply `formalIsogenySeries_add` at `(α, β) = ([k], [1])` (k ≥ 1). Hypotheses: h_α (`ordAtInfty_mulByInt_x_neg`, k ≠ 0 ✓), h_β (`[1]^*x = x_gen` — `mulByInt_one_eq_id`/`mulByInt_pullback_x` at 1 — ord −2), h_ni: for k ≥ 2 via x-mismatch `mulByInt_x_ne_mulByInt_x` (needs k ≠ ±1 ✓ since k ≥ 2); for k = 1 via the y-leg (`AddNonInversePair_of_y_ne` + `mulByInt_y_one_ne_negY` GapQfKernel-side :313 — grep exact home).
2. Identify the LHS chord coordinates with [k+1]'s: `addPullback_x_pair [k] [1] = mulByInt_x (k+1)` and y-analogue. Route: `zsmul_genericPoint_eq` (EC/GenericPointZsmul:409: `n • genericPoint = .some (mulByInt_x n) (mulByInt_y n)` unconditional) at k, 1, k+1 + mathlib `Affine.Point.add_of_X_ne` (k ≥ 2) / `add_self_of_Y_ne` (k = 1) + `Point.some.injEq` — the pattern displayed at `zsmul_genericPoint_add_one_of_witness` (GenericPointZsmul:368-387). NOTE import: GapQfKernel must see GenericPointZsmul — check; if missing, the import is cycle-safe (audit C9: GenericPointZsmul's closure tops out at OmegaPullbackCoeff).
3. Descend Laurent → PowerSeries: LHS-of-B5 = `localExpand([k+1]^*t)`; with orderTop > 0 (shipped FIS:1765 + ordAtInfty_mulByInt_x_neg at k+1) reconstruct `= ofPS (formalIsogenySeries [k+1])`; `ofPowerSeries_injective` finishes (RHS is already ofPS-of-the-subst).
4. Then verify (`#print axioms`) the IV.2.3a chain goes clean: `coeff_one_formalIsogenySeries_mulByInt_eq`, `_of_neg`, and the TOP corollary in the file — record results.

#### Mathlib lemmas
`Affine.Point.add_of_X_ne`, `Affine.Point.add_self_of_Y_ne` (grep exact mathlib names in the project's pin), `HahnSeries.ofPowerSeries_injective`.

#### Sources
[Sil] IV.2.2.4 + IV.2.3(a) p. 121-122 (the [m] recursion is literally F([m], [1])); plan §Reuse-1.

#### Generality
k : ℕ, 1 ≤ k as stated.

---

### [FG-C3] IV.2.3a chain audit + doc sweep
- **Status**: done (2026-06-11) | **File**: `GapQfKernel.lean` docs + board | **Depends on**: FG-C2 | **Type**: audit/doc
- `#print axioms` on the IV.2.3a family; update stale docstrings (the "proven-modulo-:51" notes); update `.mathlib-quality/triage/remaining-sorries.md` entries for closed items; one-line board refresh.
- **Progress**: **DONE.** Audit results recorded verbatim in the C1/C2 Progress notes above; sacred `hasse_bound_unconditional` re-verified `[propext, Classical.choice, Quot.sound]`. Docs updated: GapQfKernel module header (L-F1 PROVEN; TOP's remaining blockers = III.1.5 pair + P, no longer L-F1), the two "gated on the BRIDGE-003 leaf" docstrings, Genuine.lean's two stale "still on `sorry`" narratives (module note + `addPullback_x_pair_ord_neg_of_summands_reduce`), `triage/remaining-sorries.md` (header census note 6-in-4-files; item 10 + GapQfKernel `:49` → CLOSED with routes; FIS BRIDGE-003 design-verdict → PROVEN). Repo census 8 → 6 (`FIS:364`, `GapQfKernel:651/:663/:1303`, `OmegaPullbackCoeff:480`, `PencilComapWitnesses:1943`). ROOT `lake build HasseWeil` GREEN.

---

### [FG-C4] P — `pullback_invariantDiff_coeff_zero` (:1244)
- **Status**: done (2026-06-13) | **File**: `HasseWeil/GapQfKernel.lean` | **Depends on**: FG-B1, FG-B2 (NOT B5) | **Parallel**: with B4/B5 if a second worker exists | **Type**: theorem (close the sorry)
- **Progress**: DONE, axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx). `pullback_invariantDiff_coeff_zero` now at GapQfKernel:1567. Route per the sketch: char-2/char≠2 split mirroring the proven N (`invariantDiff_localExpand_coeff_zero`); the substituted univariate implicit-diff identity (no chain rule, no dividing by `f′` — covers inseparable α); the abstract-CommRing `pullback_diff_rearrange` helper + a T²-cleared LaurentSeries `linear_combination` assembly; B4a's kit de-privatized in ChordExpansion (7-line visibility edit) for reuse. **NOTE**: the proof was completed by the prior worker but its run was cut off (token limit) during the report phase; a transient stale-dependency `.olean` state showed 5 phantom errors on first build — a clean rebuild of the dependency chain elaborates GREEN. Verified: root `lake build HasseWeil` GREEN (8387), GapQfKernel census 3 → 2 (only the III.1.5 pair :651/:663 remain), P + sacred `hasse_bound_unconditional` both axiom-clean. The consumers `omegaPullbackCoeff_mulByInt_via_formalGroup`/`_p_eq_zero_via_formalGroup` still carry sorryAx via mem_F (III.1.5 pair, FG-D1) — P is no longer their blocker.

#### Statement
Existing GapQfKernel:1239-1244 (quoted in audit B4) — fill the sorry.

#### Proof sketch
Silverman IV.4.3's two-line proof, concretized at coeff 0 (with N = the proven :1110 as the normalization input):
1. From FG-B2: `localExpand(α^*x) = ofPS f_α / ofPS (w∘f_α)` hence `LaurentSeries.derivative (localExpand (α^*x)) = ` (quotient rule — the file's own `laurent_derivative` toolkit :302-430) an explicit expression in f_α, w∘f_α and their derivatives; chain rule on `w∘f_α`: `derivative (subst f_α w) = (subst f_α (derivative w)) * derivative f_α` (mathlib `PowerSeries.derivative_subst`? — VERIFY; if absent, prove for our case via `coeff_subst` + Leibniz, or reuse `FormalGroup/PDeriv.pderiv_subst_fin2` specialized).
2. Similarly `localExpand(alpha_star_u)` — alpha_star_u = α^*(2y + a₁x + a₃) (grep its def): expand via B2 (`= −2(w∘f)⁻¹ + a₁ f/(w∘f) + a₃` …).
3. The ratio `(u_α)⁻¹·d(x_α)` then equals `(ω-series ∘ f_α) · f_α′` formally: the cleanest organization is the file's N-proof pattern — express `(localExpand u)⁻¹·D(localExpand x)` for the GENERIC point as a known series G (this is what N computed: coeff 0 G = 1, and G = the normalized ω-series by construction), then show the α-pulled version = (G ∘ f_α)·f_α′ via steps 1-2, then `coeff 0 ((G∘f)·f′) = (coeff 0 G)·(coeff 1 f) = coeff 1 f` — the last step: coeff 0 of a product where G∘f has order ≥ 0 with constant term `coeff 0 G` (constantCoeff_subst) and f′ has coeff 0 = coeff 1 f.
4. Keep everything at the coeff-0/order level (the full series identity `(u_α)⁻¹ d(x_α) = (G∘f)·f′` IS the natural intermediate — state it; it is the concrete IV.4.3 and will serve future work).
5. Char-free: N's char-2 swap trick (the y-derivative form via `formalXY_weierstrass_derivative` :1039) is available if the −2-leading-coefficient form degenerates — mirror N's branch structure.
6. Then close BRIDGE-001's consumer expectations: `omegaPullbackCoeff_F_value_eq_coeff_one` (:1253) already consumes N + P — verify it (and `_via_localization`) compile through; BRIDGE-001 itself still awaits mem_F (Phase D) — update its docstring to say so precisely.

#### Mathlib lemmas
`PowerSeries.derivative` API; possibly `PowerSeries.derivative_subst`-shaped (verify; fallback: project PDeriv); `HahnSeries` coeff/order toolkit already in-file.

#### Sources
[Sil] IV.4.3 p. 126 (PDF 144), proof quoted in the extraction ("ω_G∘f is an invariant differential … comparing coefficients of T gives a = f′(0)"); IV.4.2's normalization (= N, proven).

#### Generality
As stated (h_orderTop guard from the restatement strike). No new hypotheses.

---

### [FG-D1] a_α has no finite poles → :592 (`omegaPullbackCoeff_isIntegral_polynomialX`)
- **Status**: open | **File**: `HasseWeil/GapQfKernel.lean` (+ possibly a helper in `EC/DifferentialOrd.lean`) | **Depends on**: none of A/B (independent); sequence after C4 | **Type**: theorem (RISKIEST; REVIEW-PENDING allowed)

#### Statement
Existing GapQfKernel:589-592 — fill or honestly reduce.

#### Proof sketch (the III.1.5 route, project-adapted)
1. a_α := omegaPullbackCoeff W α satisfies `Dω(α^*x) = α^*u · a_α` (`Dω_isog_pullback_x_gen` DifferentialOrd:393) — so a_α = Dω(α^*x)/α^*u away from zeros of α^*u.
2. At a smooth point P where α^*x is REGULAR: `ord_P(Dω(α^*x)) ≥ 0` (`ord_P_Dω_nonneg` :258) and if moreover α^*u(P) ≠ 0, ord_P(a_α) ≥ 0 directly. The two failure sets: (i) poles of α^*x (affine kernel points of α-as-map), (ii) zeros of α^*u (preimages of 2-torsion).
3. (ii) zeros of α^*u with α^*x regular: a_α = Dω(α^*x)/α^*u — mirror Silverman III.1.5's affine dichotomy AT THE IMAGE POINT pulled back: at such P, `α^*(x − x₀)` (x₀ := the image's x-value) has ord ≥ 2-shaped behavior and `Dω` drops one (`one_le_ord_P_Dω_of_two_le` :308 + `ord_P_isog_pullback_x_sub_const_le_one` :407 give the two-sided control); the III.1.5 ledger `ord(ω) = ord(x−x₀) − ord(F_y) − 1 = 0` becomes `ord_P(Dω(α^*(x−x₀))) ≥ ord_P(α^*u)` — assemble from the shipped DifferentialOrd kit (this is what the kit was BUILT for; if a piece is missing state it as a sub-lemma in DifferentialOrd's idiom).
4. (i) kernel-point poles: both Dω(α^*x) and α^*u have poles; the ratio is fine because near such P, α^*(1/x) is regular vanishing: rewrite a_α via the INVERTED generator: `Dω(α^*(x⁻¹)) = −(α^*x)⁻²·Dω(α^*x)`-shaped (Dω_inv :110-ish exists) ⟹ `a_α = −(α^*x)²·Dω(α^*x⁻¹)/α^*u`-rearrangement… honest sub-analysis; alternatively use the y-generator form (`Dω_isog_pullback_y_gen` :441) where x-poles trade for y-poles of different parity and the two presentations cover all P (Silverman's dx/F_y vs dy/F_x dichotomy III.1.5!). The PLANNED shape: prove `ord_P(a_α) ≥ 0` for all smooth P by the two-presentation cover: P is non-2-torsion-image (use dx/F_y form) or non-ramified-in-x (use dy/F_x form) — III.1.5's proof shows the two cases cover (F_x, F_y don't vanish together at smooth points; pull back).
5. From `∀ P smooth, ord_P(a_α) ≥ 0` + a_α ∈ KE conclude integrality over F[x]: the project's closer is `const_of_isIntegral_polynomialX_of_ordAtInfty` (Curves/Infinity:1446) which CONSUMES :592's statement — so :592 itself wants `IsIntegral (Polynomial F) a_α` from no-finite-poles: grep the project for the "no finite poles ⟹ integral over F[x]" engine (the integral-closure machinery in Curves/IntegralClosure.lean / NormValuation — the Hasse work certainly has a form of it; cite, don't rebuild). If the engine demands "regular at all places over all of Spec F[x]" exactly, match shapes.
6. **Stop-loss**: if the kernel-point case (4) resists after honest effort, RESTATE the deliverable as the conditional `omegaPullbackCoeff_isIntegral_of_regular`-shaped lemma + REVIEW-PENDING the unconditional form with a precise question for /expert-review (the brief shape: "pullback of holomorphic differential is holomorphic — which minimal local input closes the kernel-point case in a function-field-only framework?").

#### Mathlib lemmas — project DifferentialOrd kit + integral-closure engine (grep).
#### Sources — [Sil] III.1.5 p. 48 (PDF 66), FULL two-case proof quoted in the extraction; III.5's "φ^*ω_E is holomorphic" usage context.
#### Generality — any isogeny α (no separability!); the statement is hypothesis-free.

---

### [FG-D2] a_α regular at infinity → :604 (`omegaPullbackCoeff_ordAtInfty_nonneg`)
- **Status**: open | **File**: `HasseWeil/GapQfKernel.lean` | **Depends on**: FG-D1 (shares machinery) | **Type**: theorem (REVIEW-PENDING allowed)

#### Proof sketch
1. At O: a_α = Dω(α^*x)/α^*u with both sides' ord_∞ computable: ord_∞(α^*x) = e·(−2), ord_∞(α^*u) = e·(−3) (u has ord_∞ = −3; pullback scaling — for the BARE `Isogeny` the scaling law must come from the t-adic side: `orderTop_localExpand_eq_ordAtInfty` (FIS:1662) + B1/B2's expansions make ord_∞ of pullbacks COMPUTABLE through order-of-subst (project `PowerSeries.order_subst` equality!) — this is the clean route: ord_∞(α^*g) = (order f_α)·ord_∞(g) for the generators via the B-phase expansions. If Phase B landed first, USE IT (D2 then depends on B2); state the generator-level scaling lemma explicitly.)
2. Dω at ∞: `Dω(α^*x)` relates to the derivative side — from C4's series identity `(u_α)⁻¹·D(x_α) = (G∘f_α)·f_α′` (if C4 landed): a_α's expansion = that series, whose orderTop ≥ 0 by inspection (G∘f has orderTop ≥ 0, f′ orderTop ≥ 0) — **then :604 is a COROLLARY of C4's intermediate + R5b transport**: `ordAtInfty a_α = orderTop (localExpand a_α) ≥ 0`. CHECK FIRST whether C4's intermediate identity gives exactly `localExpand a_α = (G∘f_α)·f_α′` — it does modulo `omegaPullbackCoeff_spec` (a_α is CONSTANT-as-coefficient? NO — a_α ∈ KE is a function… read `omegaPullbackCoeff`'s def: it's the Kähler coefficient, an element of KE; its localExpand is a Laurent series). If yes, D2 is ~30 LOC after C4 and INDEPENDENT of D1. DO D2 BEFORE D1 in that case and resequence.
3. Else: direct t-uniformizer computation mirroring [Sil] III.1.5-at-O (the extraction's §4.5 display).

#### Sources — [Sil] III.1.5 at-O computation (extraction §4.5); IV.4.3 reading of a_α as (ω∘f)·f′/ω.
#### Generality — hypothesis-free; if the C4-corollary route needs h_orderTop (genuineness), CHECK whether :604's universal form is even true for junk α (α^*x constant ⟹ omegaPullbackCoeff = 0? compute: Dω(const) = 0 ⟹ a_α = 0 ⟹ ord ≥ 0 ✓ fine — junk-α gives a_α = 0, regular; handle by case-split on genuineness).

---

### [FG-D3] mem_F + BRIDGE-001 closure + chapter audit
- **Status**: open | **File**: `GapQfKernel.lean` / `FormalIsogenySeries.lean` docs | **Depends on**: FG-D1, FG-D2, FG-C4 | **Type**: assembly
- `omegaPullbackCoeff_mem_F` (:616-624) compiles through D1+D2; `_via_localization` (:1291) + the moved BRIDGE-001 close (`exact`-shaped per its docstring); TOP corollary; `#print axioms` the whole chain; doc + board + triage sweep.

---

### [CLEANUP-FG-FINAL] /cleanup-all
- **Status**: open | **Depends on**: everything | **Type**: cleanup
