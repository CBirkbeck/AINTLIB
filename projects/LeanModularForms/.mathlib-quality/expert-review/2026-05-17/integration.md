# Reply integration — 2026-05-17

Reply received from senior modular forms + Lean reviewer on 2026-05-17.

* Brief: `./brief.md`
* Reply: `./reply.md`
* State: `./state.md`

## Audit summary (before applying changes)

The reviewer's R1 (B.L1 q/q² bridge is false from prime-only equality) and R3 (per-character Main Lemma needs coprime-range vanishing, not prime-only) are **valid critiques of the brief's prose**, but the **actual Lean theorems were already correctly stated** with all-coprime-to-$N$ hypotheses:

* `eigenvalues_eq_all_coprime_of_eq_off_finite` (B.L1): hypothesis `∀ n : ℕ+, Coprime n N → n ∉ S → f.eig n = g.eig n` — **all coprime indices outside S**.
* `mainLemma_charSpace_routeB` (A.L2): hypothesis `∀ n : ℕ, Coprime n N → qExp(f).coeff n = 0` — **all coprime indices**.
* `newform_unique_routeB` (A.L1): hypothesis `∀ n : ℕ+, Coprime n N → f.eig n = g.eig n` — **all coprime indices**.
* `strongMultiplicityOne_axiom_clean` (top-level): composes B.L1 + A.L1 with the same "all coprime indices outside S" hypothesis.

The brief mis-described all four as "prime equality". No Lean change needed — only brief prose correction.

## Interpretation table

| # | Reviewer point | Maps to | Type | Verdict |
|---|---|---|---|---|
| R1 | B.L1 from prime-only is false | §5.1.2 brief | brief prose error | brief corrected; Lean unchanged |
| R2 | Correct route: coprime-vanishing → Main Lemma → oldness → zero | §3 brief | confirmation of intended route | brief §3 corrected |
| R3 | Main Lemma needs coprime Fourier vanishing, not prime-only | §5.1.3 brief | brief prose error | brief corrected; Lean unchanged |
| R4 | M5–M8 chain faithful to Miyake | §3, §6 | validating | recorded |
| R5/R12 | M5 bundle overgeneralized; use character-space | §6.2, §7, Q3, Q7 | refactor recommendation | NEW ticket + DEFER existing |
| R6 | Möbius formula / α construction correct | §8.1 | validating | recorded |
| R7 | Normalization $p/C_{N,p}$ harmless | Q2 | validating | recorded |
| R8 | Q4 — non-SL conjugation: use entries, not normality | §8.4, Q4 | math correction | brief corrected; T6b ticket note added |
| R9 | Raw integer matrix lemma first; then map to GL | Q5, §8.1 | direct Lean answer with signature | NEW ticket: `descend_upper_tri_raw_matrix_identity` |
| R10 | `Matrix.vecCons _ _ ⟨0,h⟩` idiom | Q5 | direct Lean answer | saved as memory: `feedback_matrix_vecCons_idiom.md` |
| R11 | Q6 (mathlib infrastructure) — implicit no | Q6 | UNANSWERED (implicit) | recorded as still open |
| R13 | Q8 (audit workflow) | Q8 | UNANSWERED | recorded as still open |
| R14 | Descent hypothesis should be $p \mid N/\mathrm{cond}(\chi)$ | not in our Qs | new subtle audit point | NEW LOW-prio ticket: `audit-conductor-bookkeeping` |
| R15 | Acceptance criteria for next pass | meta | direct guidance | adopted |

## Changes applied to brief

* §3 (Strategy) point 1: B.L1 hypothesis corrected from "all-but-finitely-many primes" to "all coprime-to-$N$ indices outside a finite set $S$". Added the explicit observation that prime-only would be insufficient.
* §5.1.2 (Theorem 5.1.2): full restatement with the actual coprime hypothesis, proof sketch updated to match the Lean proof (prime-avoidance + case split on $\lambda_q(f)$).
* §5.1.3 (Theorem 5.1.3): hypothesis corrected from "$a_p(f) = 0$ for all primes $p \nmid N$" to "$a_n(f) = 0$ for all $n$ coprime to $N$".
* §6.2 (M5 bundle): refactored to character-space version as primary statement; full-space version marked deferred.
* §7 (target table): added `descend_upper_tri_raw_matrix_identity` (#4a), `miyake_hecke_descend_char` (#7'), `audit-conductor-bookkeeping` (#A1); marked old #7 deferred.
* §8.4 (T6b): replaced the normality argument with explicit entrywise computation.
* §9 Q4: marked resolved by reviewer; added Q4b about conductor bookkeeping.

## Changes applied to tickets / project structure

This project doesn't have a formal `tickets.md` — the structured guidance is recorded here. For future workers picking up the chain:

### NEW tickets

#### `descend_upper_tri_raw_matrix_identity` (helper, HIGH priority)
* **Status**: open
* **Statement (Lean draft)**:
  ```lean
  private lemma descend_upper_tri_raw_matrix_identity
      (p : ℕ) (hp : 0 < p)
      (A B C D v v' a01 : ℤ)
      (hC : (p : ℤ) ∣ C)
      (ha01 : (p : ℤ) * a01 = B + v * D - (A + v * C) * v') :
      !![1, v; 0, (p : ℤ)] * !![A, B; C, D]
        =
      !![A + v*C, a01; (p : ℤ)*C, D - C*v'] * !![1, v'; 0, (p : ℤ)]
  ```
* **Approach**: entrywise via `Matrix.ext` + `fin_cases` + `ring`/`omega`. No GL coercion, no `Units.ext`.
* **Blocks**: `descendCosetList_action_upper_tri_clean` (T5a-3a-clean).
* **Reviewer guidance** (2026-05-17): "Add a raw lemma over integer matrices. Then map this equality into ℝ and the bundled GL objects."

#### `miyake_hecke_descend_char` (character-space M5 bundle, SMO-critical)
* **Status**: open (replaces old full-space M5 bundle as critical path)
* **Statement**: For $p$ prime with $p \mid N$, $[\mathrm{NeZero}\,(N/p)]$, $\chi : (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$ factoring as $\chi = \chi_0 \circ \mathrm{unitsMap}_{N \to N/p}$, there exists a $\mathbb{C}$-linear map
  $$\Phi_{p,\chi}: \texttt{modFormCharSpace}\,k\,\chi \to \texttt{modFormCharSpace}\,k\,\chi_0$$
  at levels $N$ and $N/p$ respectively, satisfying:
  * **Cusp preservation**: restricts to a map of cusp-form character spaces.
  * **Miyake (4.6.12)**: $\Phi_{p,\chi}(V_p g) = (p/C_{N,p}) \cdot g$ for $g \in \texttt{modFormCharSpace}\,k\,\chi_0$ at level $N/p$.
* **Depends on**: M5a, M5b, M5c, M5d (b/c/d proven; a in progress).
* **Replaces in SMO-critical path**: `miyake_hecke_descend` (full-space M5 bundle).
* **Reviewer guidance**: "Prefer a character-space descent operator with an explicit hypothesis that $\chi$ factors through $N/p$. Do not block SMO on a full-space map."

#### `audit-conductor-bookkeeping` (LOW priority)
* **Status**: open
* **Description**: Audit all M5/M6/M7/M8 lemmas to verify the descent hypothesis on $p$ is stated as "$p \mid N/\mathrm{cond}(\chi)$" (or equivalently "$\chi$ factors through $(\mathbb{Z}/(N/p)\mathbb{Z})^\times$") rather than just "$p \mid N$". Affects: M5 bundle, M6(2), M7-decomp, M8 inductive step.
* **Reviewer guidance**: "In the final Main Lemma, the primes that can be removed should be primes dividing $N/\mathrm{cond}(\chi)$, not arbitrary primes dividing $N$."

### MODIFIED tickets

#### `descendCosetList_action_upper_tri_clean` (T5a-3a-clean)
* **Status**: open (sorry remains)
* **Refactored proof approach**:
  1. Construct $(m', \alpha_{01}, \alpha\text{-matrix})$ over $\mathbb{Z}$ via Möbius formula $v' \equiv A^{-1}(B+vD) \pmod p$ and integrality argument.
  2. Apply `descend_upper_tri_raw_matrix_identity` to get the integer-matrix identity.
  3. Map to $\mathrm{GL}_2(\mathbb{R})$ via `mapGL_coe_matrix` and `val_mkOfDetNeZero` coercions (only after step 2).
* **Reviewer guidance**: "Do not fight Units.ext/mkOfDetNeZero/GL₂(ℝ) coercions until the raw matrix equation is proved."

#### `descendCosetList_slash_sum_rep_invariance` (T6b-coset-inv)
* **Status**: open (sorry remains)
* **Proof approach correction**: Do NOT appeal to "$\Gamma(N)$ is normal in $\mathrm{SL}_2(\mathbb{Z})$" for conjugation by $[1, 0; 0, p]$ — $[1, 0; 0, p]$ is not in $\mathrm{SL}_2(\mathbb{Z})$. Instead, use explicit entrywise computation: for $g = [a, b; c, d] \in \Gamma(N)$, compute $\beta = [1, 0; 0, p] g [1, 0; 0, 1/p] = [a, b/p; pc, d]$ entry by entry. Integrality of $b/p$ follows from $p \mid b$ (since $b \equiv 0 \pmod N$ and $p \mid N$). $\beta \in \Gamma_1(N)$ follows from $a, d \equiv 1 \pmod N$ and $pc \equiv 0 \pmod N$.
* **Reviewer guidance**: "The conjugation by diag(1, p) preserves Γ(N) by entry computation, not by normality."

#### `miyake_hecke_descend` (full-space M5 bundle, DEFERRED)
* **Status**: open; **deferred off SMO-critical path**.
* **Note**: The full-space version requires character decomposition + "slash sum vanishes on non-factoring χ-eigenspace". Useful for some downstream applications but not for SMO closure.
* **Reviewer guidance**: "Do not block SMO on a full-space map. Derive from character-space later if needed."

## Open questions remaining

* **Q6 unanswered**: Existing Lean/Mathlib infrastructure for inter-level descent — reviewer implicitly indicated none exists (suggested building our own).
* **Q8 unanswered**: Whether the multi-pass audit workflow is right for this kind of formalization — reviewer didn't address.

## Acceptance criteria for next pass (per reviewer R15)

1. `descendCosetList_action_upper_tri_clean` closed, OR raw matrix lemma (`descend_upper_tri_raw_matrix_identity`) closed with the exact remaining coercion obstacle reported.
2. No changes to the top-level SMO bridge that claim exceptional prime equality follows from q/q² recurrence alone. (Already met — Lean theorems were correct; brief prose corrected.)
3. If M5 bundle is touched, refactor toward a character-space descent map under a factoring-through-$N/p$ hypothesis. (Now scheduled as the SMO-critical replacement.)

## Decisions recorded but not actioned

* Normalization choice $p/C_{N,p}$ settled per Q2: keep as-is.
* M5-M8 chain structure validated; proceed with current decomposition.
