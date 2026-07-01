# Pass G — Post-reviewer multi-pass audit (2026-05-17)

For each open lemma, check against the reviewer's findings:
* (R3) Hypothesis correctness — prime vs all-coprime (and similar prose hazards).
* (R8) Proof approach validity — appeals to invalid arguments (e.g., normality of Γ(N) under non-SL conjugation).
* (R14) Conductor bookkeeping — descent hypothesis on $p$ should be "$p \mid N/\mathrm{cond}(\chi)$", not "$p \mid N$".
* Hidden cyclic dependencies and Lean-side blockers.

Verdict legend: ✓ tractable / 🟡 needs note / 🔴 blocker.

---

## #1 `int_exists_coprime_adjust`

**Statement.** Given $c, d, N \in \mathbb{Z}$, $d \neq 0$, $\gcd(\gcd(c,d), |N|) = 1$: $\exists\, t \in \mathbb{Z}$ with $\gcd(c+tN, d) = 1$.

* R3 hypothesis: ✓ (correct; not a SMO-level statement).
* R8 proof approach: induction on $d.\mathrm{natAbs}.\mathrm{primeFactors}$ as a Finset. No invalid appeals.
* R14 conductor: N/A (no χ).
* Lean-side: standard ZMod / Bezout. No matrix-vecCons issue.

**Verdict.** ✓ tractable, ~100 LOC.

---

## #2 `SL2Z_to_SL2_ZMod_surjective`

**Statement.** $\mathrm{SL}_2(\mathbb{Z}) \twoheadrightarrow \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$.

* R3 hypothesis: ✓.
* R8 proof approach: 4-step recipe — lift bottom row, coprime-adjust via #1, Bezout for top row, then adjust top row to match modulo $N$.
* 🟡 **Hidden blocker (Pass G finding)**: the top-row adjustment in step (4) is hand-wavy in the original audit. After Bezout produces $(a_0, b_0)$ with $a_0 d - b_0(c+tN) = 1$, the adjustment $(a_0, b_0) \mapsto (a_0 + \alpha c + \beta d, b_0 + \alpha d - \beta(c+tN))$ for some $\alpha, \beta \in \mathbb{Z}$ preserves determinant 1 (by direct verification: the matrix obtained from $(a_0 + \alpha c, b_0 + \alpha d)$ adds $\alpha$ times row-2 to row-1, det-preserving). To match $(\bar{a}, \bar{b})$ mod $N$, need $\alpha c + \beta d \equiv \bar{a} - a_0 \pmod N$ AND $\alpha d - \beta (c+tN) \equiv \bar{b} - b_0 \pmod N$. This is a 2×2 system $\begin{pmatrix} c & d \\ d & -(c+tN) \end{pmatrix} \begin{pmatrix} \alpha \\ \beta \end{pmatrix} \equiv \begin{pmatrix} \bar{a} - a_0 \\ \bar{b} - b_0 \end{pmatrix} \pmod N$; solvable when the determinant $-c(c+tN) - d^2 \neq 0$ mod $N$ — which is **not automatic**.
* **Fix**: Use the simpler one-parameter adjustment $(a_0, b_0) \mapsto (a_0 + \alpha c, b_0 + \alpha d)$ (just row-2 added $\alpha$ times to row-1). Then $\alpha c \equiv \bar{a} - a_0 \pmod N$ is solvable iff $\gcd(c, N) \mid \bar{a} - a_0$. Since $\bar{a} d - \bar{b}(c+tN) \equiv 1 \pmod N$ and $a_0 d - b_0 (c+tN) = 1$, subtracting gives $(\bar{a} - a_0) d \equiv (\bar{b} - b_0)(c+tN) \pmod N$. With $\gcd(c+tN, d) = 1$ (from #1) and $\gcd(d, N)$ possibly nontrivial, the divisibility $\gcd(c, N) \mid (\bar{a} - a_0)$ does NOT immediately follow.
* **Better fix**: Lift the **column** instead — adjust $(a_0, b_0)$ such that ONE entry matches, say $a_0 \equiv \bar{a} \pmod N$ via $\alpha c$, then $b_0$ adjusts automatically because the bottom row plus det-1 determines $b$ mod $N$.

**Verdict.** 🟡 **Pass-G finding: tighten the top-row adjustment recipe before attacking.** Estimated LOC revised to 180–220 (was 160). Add a sub-helper `sl2_top_row_adjust_single_param` to capture the working recipe.

---

## #3 `descendExtraGamma_exists` (T5a-0)

**Statement.** $\tilde{\gamma}_p \in \mathrm{SL}_2(\mathbb{Z})$ with $\tilde{\gamma}_p \equiv [0, -1; 1, 0] \pmod p$ and $\tilde{\gamma}_p \equiv I \pmod{N/p}$.

* R3 hypothesis: ✓.
* R8 proof approach: build $\bar{M} \in \mathrm{SL}_2(\mathbb{Z}/N\mathbb{Z})$ via CRT-matrix-entry-wise from the two target matrices, then apply #2.
* R14 conductor: ✓ no χ.
* Lean-side: cast through `Matrix _ _ (ZMod (p * N/p))` to `Matrix _ _ (ZMod N)` via `Nat.mul_div_cancel'`. ▸ rewriting may have motive issues; needs care.

**Verdict.** ✓ tractable once #2 is done.

---

## #4a `descend_upper_tri_raw_matrix_identity` (NEW)

**Statement (reviewer-provided).**
```
!![1, v; 0, (p : ℤ)] * !![A, B; C, D]
  = !![A + v*C, a01; (p : ℤ)*C, D - C*v'] * !![1, v'; 0, (p : ℤ)]
```
given $p \mid C$ and $p \cdot a_{01} = B + v D - (A + v C) v'$.

* R3/R8/R14: N/A (raw integer lemma).
* Proof: `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring`. Entry (0,1) uses the $a_{01}$ hypothesis via `linear_combination`.

**Verdict.** ✓ tractable, ~20 LOC. **First target.**

---

## #4 `descendCosetList_action_upper_tri_clean` (T5a-3a-clean)

**Statement.** $p^2 \mid N$ case of M5a's upper-tri orbit, with canonical Möbius $m'$.

* R3 hypothesis: ✓ canonical $m'$ pinned by $a m' \equiv b + m d \pmod p$.
* R8 proof approach: use #4a for the raw matrix identity, then map to $\mathrm{GL}_2(\mathbb{R})$.
* R14 conductor: N/A at this layer.
* Lean-side: ✓ the matrix-vecCons blocker is bypassed by going through #4a.

**Verdict.** ✓ tractable, ~80 LOC once #4a is in place.

---

## #5 `descendCosetList_action_upper_tri_extra` (T5a-3a-extra, $p^2 \nmid N$ case)

**Statement.** $p^2 \nmid N$ case with case-split on extra-rep target.

* R3 hypothesis: ✓ canonical target.
* R8 proof approach: case on whether $A := A + m C \pmod p$ is invertible mod p (where $C = \gamma'_{10}$). If yes: target is in $\mathrm{Fin}\, p$ (upper-tri), same Möbius as #4. If no: target is the extra rep.
* 🟡 **Hidden blocker (Pass G finding)**: the "extra→extra" sub-case computes $\alpha = [1, m; 0, p] \cdot \gamma' \cdot ([1, 0; 0, p] \cdot \tilde{\gamma}_p)^{-1}$. Inverting requires $\tilde{\gamma}_p^{-1}$ (proven as `multipass_descendExtraGamma_inverse`) AND $[1, 0; 0, p]^{-1} = [1, 0; 0, 1/p]$, which is NOT in $\mathrm{SL}_2(\mathbb{Z})$. The $\alpha$ matrix is integer only because $p$ divides the right entries — entrywise computation needed (analogous to R8's correction for T6b).
* R14: N/A.
* Lean-side: like #4, the matrix-vecCons issue applies. **Add a parallel raw matrix identity** `descend_upper_tri_extra_raw_matrix_identity` for the extra-rep target.

**Verdict.** 🟡 **Pass-G finding: add a sibling raw matrix identity (#5a) before attacking #5.** Estimated LOC 200+ (was 150).

---

## #6 `descendCosetList_action` (T5a-3, M5a combinator)

**Statement.** Bundles upper-tri + extra-rep into full M5a witness with $\sigma$ as a permutation.

* R3: ✓.
* R8 proof approach: per-v case-split using #4 or #5; collect (target_v, α_v) pairs; build $\sigma : \mathrm{Fin}\,(C_{N,p}) \to \mathrm{Fin}\,(C_{N,p})$; prove injectivity via `descendCosetList_moebius_inj` (proven).
* 🟡 **Hidden blocker (Pass G finding, existential-vs-canonical)**: $\sigma$ must be a `Equiv.Perm`, not just a function. Building it requires both $\sigma$-injectivity (which we have for the Möbius part) AND coverage of the target set. In the $p^2 \nmid N$ case, the extra rep can be either a fixed point or part of a transposition; needs the full case analysis encoded.
* R14: N/A.

**Verdict.** ✓ tractable; estimate 100 LOC for the σ construction + diamond verification.

---

## #7' `miyake_hecke_descend_char` (NEW, character-space M5 bundle, SMO-critical)

**Statement (new).** $\Phi_{p,\chi}: M_k(N, \chi) \to M_k(N/p, \chi_0)$ as $\mathbb{C}$-linear map, under hypothesis $\chi = \chi_0 \circ \mathrm{unitsMap}_{N \to N/p}$ (equivalently $\mathrm{cond}(\chi) \mid (N/p)$, i.e., $p \mid N/\mathrm{cond}(\chi)$).

* R3: hypothesis correct.
* R14 conductor: ✓ the "$\chi$ factors through $\mathrm{unitsMap}$" hypothesis IS the conductor condition. They're equivalent: $\chi$ factors iff $\chi$ vanishes on $\ker(\mathrm{unitsMap})$ iff $\mathrm{cond}(\chi) \mid (N/p)$.
* R8 proof approach: bundle the function-level slash sum from M5a (M5c gives cusp pres, M5d gives χ-equivariance, M5b gives the q-shift).
* 🟡 **Hidden blocker (Pass G finding)**: the codomain is $M_k(N/p, \chi_0)$, which requires the slash sum to be (a) Γ_1(N/p)-invariant, (b) χ_0-equivariant under Γ_0(N/p). M5d gives (b) directly. (a) follows from (b) applied at $\gamma \in \Gamma_1(N/p)$ where $\chi_0(\gamma) = 1$.
* Lean-side: needs `LinearMap.mk` from the function. The Γ_1(N/p)-invariance proof goes through M5d at a Γ_1 element.

**Verdict.** ✓ tractable, ~150 LOC.

---

## #7b `non_factoring_slash_sum_vanishes` (NEW helper)

**Statement.** For $\chi$ not factoring through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$ (i.e., $\mathrm{cond}(\chi) \nmid (N/p)$), the descent slash sum vanishes on $M_k(N, \chi)$.

* R3/R8: ✓ standard.
* R14 conductor: ✓ — this IS the conductor-aware vanishing.
* Math: pick $a \in \ker(\mathrm{unitsMap})$ with $\chi(a) \neq 1$ (exists since $\chi$ doesn't factor). By `Gamma0MapUnits_surjective`, $\exists\, \gamma \in \Gamma_0(N)$ with $\mathrm{Gamma0MapUnits}\,\gamma = a$. Apply M5d with γ ∈ Γ_0(N) ∩ Γ_1(N/p)?
* 🔴 **Hidden blocker (Pass G finding)**: M5d's hypothesis takes γ ∈ Γ_0(N/p), not Γ_0(N). For the cancellation, we need γ ∈ Γ_0(N) (so $\chi(\gamma)$ is meaningful) AND γ ∈ Γ_1(N/p) (so the slash factor on the LHS is identity, since χ_0(γ) = 1). The intersection $\Gamma_0(N) \cap \Gamma_1(N/p)$ is non-trivial; via the Gamma0MapUnits map at level $N$, the constraint becomes: pick γ ∈ Γ_0(N) with Gamma0MapUnits γ ∈ ker(unitsMap N → N/p) AND χ(Gamma0MapUnits γ) ≠ 1.
* The Gamma0MapUnits surjectivity (project lemma) onto $(\mathbb{Z}/N\mathbb{Z})^\times$ guarantees we can hit any element of ker(unitsMap) ⊂ $(\mathbb{Z}/N\mathbb{Z})^\times$. Since $\chi$ doesn't factor, ∃ $a \in \ker(\mathrm{unitsMap})$ with $\chi(a) \neq 1$.
* Combining: $f \mid \mathrm{mapGL}\,\gamma = \chi(a)\,f$ AND (slash sum) $\mid \mathrm{mapGL}\,\gamma$ = $\chi_0(\mathrm{Gamma0MapUnits}_{N/p}\,\gamma) \cdot $ (slash sum) BUT γ ∈ Γ_1(N/p) makes $\mathrm{Gamma0MapUnits}_{N/p}\,\gamma = 1$, so slash sum is fixed by γ. Yet also (slash sum) ∣ γ = χ(a) (slash sum) (linearity transported through the action). $(\chi(a) - 1) \cdot$ slash sum $= 0$ with $\chi(a) \neq 1$ gives slash sum $= 0$.
* **The Lean version**: need to lift γ to mapGL ℝ γ, then apply M5d. M5d's signature requires γ ∈ Γ_0(N/p); but we have γ ∈ Γ_0(N) which embeds into Γ_0(N/p) (since $N \mid c$ → $N/p \mid c$ when $p \mid N$). ✓ embedding exists.

**Verdict.** ✓ tractable, ~80 LOC. **The downgrade from 🔴 to ✓ is via the Γ_0(N) ⊂ Γ_0(N/p) embedding.** Important sub-lemma.

---

## #7 `miyake_hecke_descend` (full-space M5 bundle, NO LONGER DEFERRED)

**Statement.** $\Phi_p : M_k(\Gamma_1(N)) \to M_k(\Gamma_1(N/p))$ derived from #7' + #7b via $\bigoplus_\chi$ decomposition.

* R3/R8/R14: ✓ inherited from #7' and #7b.
* Proof: For $f \in M_k(\Gamma_1(N))$, use the proven `ModularForm_Gamma1_charSpace_linearEquiv` to write $f = \sum_\chi f_\chi$. Define $\Phi_p(f) := \sum_{\chi \text{ factors}} \Phi_{p,\chi}(f_\chi)$. The codomain χ' for each factoring χ is $\chi \circ \mathrm{unitsMap}^{-1}$ (well-defined on the image); the codomain forms $\Phi_{p,\chi}(f_\chi)$ live in different character spaces of $M_k(N/p)$, summing into $M_k(\Gamma_1(N/p))$.
* 🟡 **Hidden blocker (Pass G finding)**: the existential `∃ Φ, c, ...` form of the current M5 bundle has the q-shift hypothesis embedded. With character-space + non-factoring vanishing in place, the q-shift holds (by M5b applied to V_p g for any g; the χ for V_p g is the unique factor through unitsMap). The c is $p / C_{N,p}$.
* Lean-side: `DirectSum.toModule` or `LinearMap.lsum`-based construction. ~120 LOC.

**Verdict.** ✓ tractable. **No deferral.**

---

## #8 `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv)

**Statement.** Rep choice $\tilde{\gamma}_p$ doesn't affect $\chi$-eigenform slash sum (for two valid choices satisfying the CRT congruences).

* R3 hypothesis: ✓.
* R8 proof approach: **reviewer-corrected** — use explicit entrywise computation, not normality of Γ(N).
* R14 conductor: ✓ no direct issue (the slash sum is in a χ-eigenform context).
* Math (refreshed): for γ_1, γ_2 ∈ Γ_0(N/p) both ≡ [0,-1;1,0] mod p and ≡ I mod N/p, the difference g := γ_1⁻¹ γ_2 ≡ I mod N (by CRT, since gcd(p, N/p) = 1 in the $p^2 \nmid N$ case). So g ∈ Γ(N). The conjugation β = [1,0;0,p] · mapGL g · [1,0;0,p]⁻¹ is in mapGL of Γ_1(N) by entrywise check.
* 🟡 **Pass-G finding**: the rep-invariance is conditional on **both γ_i satisfying the stronger congruence "≡ I mod (lN)/p"** — but the natural `descendExtraGamma_spec` only gives ≡ I mod (N/p). To handle level lN, the spec needs to be invoked at level lN to get ≡ I mod (lN/p), which IS stronger. The Lean statement of T6b-coset-inv needs to be parameterised correctly: γ_1 ≡ I mod (lN/p) at level lN, γ_2 ≡ I mod (N/p) at level N — and both satisfy the lN-level (stronger) congruence by choice.

**Verdict.** 🟡 **Pass-G finding: clarify the hypothesis layering — both γ_i must satisfy the stronger congruence**. Estimate 120 LOC.

---

## #9 `descendCosetList_slash_sum_commute` (T6b-commute)

**Statement.** Function-level slash sum commutation across levels.

* R3/R8: ✓.
* R14: ✓ (no χ at this layer).
* Hidden blocker: slash multiplicativity + reindexing. Tedious but tractable.

**Verdict.** ✓ tractable, ~150 LOC.

---

## #10 `miyake_4_6_6_level_commute_delta` (M6(2))

**Statement.** $\Phi_p \circ V_l = V_l \circ \Phi_p^{(N/p)}$ for $(l, p) = 1$, $l \mid N/p$.

* R3 hypothesis: ✓.
* R8 proof approach: use #9 + `descendCosetList_level_agree` (proven) + `multipass_mul_mod_p_perm_exists` (proven).
* 🟡 **R14 Pass-G finding**: the hypothesis is on $l \mid N/p$ and $\chi$ at level $N$. The descent target character $\chi_0$ at level $N/p$ exists when $\chi$ factors through unitsMap. The $V_l$ side maps $M_k(N/p, \chi_0)$ to $M_k(lN/p, \chi_0')$ (with $\chi_0'$ at the higher level). The descent target on the lN side requires $\chi$ to factor through `unitsMap` at level $lN \to lN/p$ — which is automatically satisfied if it factors at $N \to N/p$ AND $(l, p) = 1$. ✓ but verify.
* Lean-side: function-level identity, lots of slash bookkeeping.

**Verdict.** ✓ tractable, ~200 LOC.

---

## #11 `miyake_4_6_7_squarefree_decomp` (M7-decomp)

**Statement.** For $f \in S_k(N, \chi)$ with coprime-vanishing on $l > 1$ squarefree: $\exists\, g_q \in S_k(Nl^2, \chi')$ with $f(z) = \sum_{q \mid l} g_q(qz)$ (q-expansion form).

* R3 hypothesis: ✓.
* R8 proof approach: induction on $\omega(l)$, using single-prime A.L3.miyake.4_6_5 + project's 4.6.4.
* 🟡 **R14 Pass-G finding**: the level lift to $Nl^2$ uses a character lift $\chi \to \chi'$. The character $\chi'$ at level $Nl^2$ is $\chi$ composed with `unitsMap`: $(\mathbb{Z}/Nl^2\mathbb{Z})^\times \to (\mathbb{Z}/N\mathbb{Z})^\times$. This requires $N \mid Nl^2$ (trivially true). ✓
* 🟡 **Sub-blocker**: the coprime-vanishing hypothesis needs Fourier coefficients $a_n(f) = 0$ for all $n$ coprime to $l$ (not just prime $n$ — reviewer R3 again). The current Lean statement uses `Nat.Coprime n l`, which is the correct all-coprime form. ✓
* Lean-side: induction on prime factors; finite-set machinery.

**Verdict.** ✓ tractable, ~300 LOC (induction is bulky).

---

## #12 `miyake_V_p_descend_identity` + `miyake_4_6_8_inductive_step` (M8)

**Statement.** Multi-prime case of Miyake 4.6.8, by induction on $\omega(N)$.

* R3 hypothesis: ✓ all-coprime form (matches reviewer's correct route).
* R8 proof approach: combine #7' + #10 + #11 + project's 4.6.4 + induction.
* 🔴 **R14 Pass-G finding**: the induction peels primes dividing $N/\mathrm{cond}(\chi)$, not arbitrary $p \mid N$. If $\mathrm{cond}(\chi) = N$ (so $\chi$ is primitive), no prime can be peeled — the form is already at conductor level, and the Main Lemma must use a different argument (or the only $f$ satisfying coprime-vanishing in that case is $f = 0$ directly from the coprime decomposition + 4.6.4 being inapplicable). **Check whether the current Lean statement of M8 correctly conditions on $\mathrm{cond}(\chi) < N$.**

**Verdict.** 🔴 **Pass-G blocker: requires R14 audit of M8 statement before attempting**. Estimate revised to 250-400 LOC + may need re-statement.

---

## #A1 `audit-conductor-bookkeeping` (NEW LOW-priority)

**Action.** Re-read M5/M6/M7/M8 statements; verify descent hypothesis is "$\chi$ factors through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$" (or equivalently "$p \mid N/\mathrm{cond}(\chi)$"), not "$p \mid N$".

**Status.** Quick textual audit; estimate 30 min.

---

## Pass G summary

* **3 lemmas need restatement / clarification** before attack:
  * #2 `SL2Z_to_SL2_ZMod_surjective`: tighten top-row adjustment recipe (single-parameter, not 2D system).
  * #8 `T6b-coset-inv`: clarify the "both γ_i at stronger congruence" hypothesis layering.
  * #12 M8 inductive step: condition on $\mathrm{cond}(\chi) < N$ explicitly.

* **2 new sibling lemmas surfaced**:
  * #5a `descend_upper_tri_extra_raw_matrix_identity` (parallel to #4a, for the extra-rep target).
  * `sl2_top_row_adjust_single_param` (sub-helper for #2).

* **1 new helper validated as ✓** (was potentially 🔴):
  * #7b `non_factoring_slash_sum_vanishes` (via Γ_0(N) ⊂ Γ_0(N/p) embedding).

* **Revised LOC estimates** (vs. original audit):
  * #2: 160 → 200
  * #5: 150 → 200+
  * #6: 100 (unchanged)
  * #7: 100 → 120 (with non_factoring helper)
  * #11: 250 → 300
  * #12: 250 → 250-400 (depends on conductor refactor)

* **Net effect**: 3 statement refinements, 2 new helpers spawned, 1 conditional verdict on M8. **No genuine new mathematical blockers** — Pass G is a refinement, not a refactor.

* **Execution order (updated)**:
  1. #4a raw matrix identity (HIGH, ~20 LOC).
  2. #4 T5a-3a-clean using #4a (HIGH, ~80 LOC).
  3. #5a raw matrix identity for extra rep (HIGH, ~30 LOC).
  4. #5 T5a-3a-extra using #5a (HIGH, ~150 LOC).
  5. `sl2_top_row_adjust_single_param` sub-helper (~50 LOC).
  6. #1 `int_exists_coprime_adjust` (~100 LOC).
  7. #2 `SL2Z_to_SL2_ZMod_surjective` (~200 LOC).
  8. #3 `descendExtraGamma_exists` (~40 LOC after #2).
  9. #6 M5a combinator (~100 LOC).
  10. #7b `non_factoring_slash_sum_vanishes` (~80 LOC).
  11. #7' character-space M5 bundle (~150 LOC).
  12. #7 full-space M5 bundle via decomposition (~120 LOC).
  13. #A1 conductor audit (~30 min).
  14. #8 T6b-coset-inv (~120 LOC).
  15. #9 T6b-commute (~150 LOC).
  16. #10 M6(2) (~200 LOC).
  17. #11 M7-decomp (~300 LOC).
  18. #12 M8 inductive step (~250-400 LOC).

Total: ~2200 LOC remaining across 16 distinct sub-lemmas (was previously estimated at ~12 sorries × 100 LOC = ~1200 LOC, so Pass G almost doubles the estimate).
