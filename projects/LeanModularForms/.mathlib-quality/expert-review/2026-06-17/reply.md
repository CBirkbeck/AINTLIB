# Reviewer reply — 2026-06-18

## Verdict

**L3 has a clean, non-circular proof from strong multiplicity one (already available).** The missing observation:

> distinct eigensystems —(SMO)⟹ inequivalent outside every finite set of primes ⟹ linearly independent multiplicative functions.

No global Main Lemma, global sieve, Rankin–Selberg, or linear recovery of diamonds required.

## 1. The multiplicative-functions lemma

For multiplicative `F, G : ℕ → ℂ`, call them **equivalent** when their p-components agree for all but finitely many primes: `F(p^a) = G(p^a)` for every `a ≥ 1` and all but finitely many `p`.

> **Lemma (Molteni; Kaczorowski–Molteni–Perelli).** Pairwise non-equivalent multiplicative arithmetic functions are linearly independent over ℂ.

Here "multiplicative" = multiplicative on coprime arguments (NOT completely multiplicative).

**Elementary proof.** Induct on the number `r`. Suppose `∑_{i=1}^r c_i F_i(n) = 0` for every `n` (1), and discard `i` with `c_i = 0`, so all `c_i ≠ 0`. Fix a prime `p` and `a ≥ 1`. For `p ∤ n`, multiplicativity and (1) applied at `p^a n` give `∑_i c_i F_i(p^a) F_i(n) = 0`. Subtract `F_r(p^a)·(1)`:
`∑_{i<r} c_i (F_i(p^a) − F_r(p^a)) F_i(n) = 0` for `p ∤ n` (2).
Define `F_i^{(p)}(n) = F_i(n)` if `p ∤ n`, else `0`. These are still multiplicative, and remain pairwise non-equivalent (only the single p-component changed — non-equivalence = differ at infinitely many primes, robust to removing one). (2) is a relation among `r−1` pairwise non-equivalent multiplicative functions; by induction `c_i(F_i(p^a) − F_r(p^a)) = 0`, so (c_i ≠ 0) `F_i(p^a) = F_r(p^a)` for every `i < r`, every prime `p`, every `a ≥ 1`. Multiplicativity ⟹ `F_i = F_r`, contradicting non-equivalence. ∎

## 2. Application to L3

Extend each prime-to-N eigensystem to `ℕ` by zero: `ẽv_i(n) = ev_i(n)` if `(n,N)=1`, else `0`. Each `ẽv_i` is multiplicative (coprime both-prime-to-N ⟹ Hecke multiplicativity; if one factor shares a prime with N, both sides are 0). The L3 relation `∑ c_i ev_i(n) = 0` (coprime n) becomes `∑ c_i ẽv_i(n) = 0` for ALL n (zero otherwise).

Pairwise non-equivalence: if `ẽv_i ~ ẽv_j` then `ev_i(p) = ev_j(p)` for all but finitely many primes `p ∤ N`. Strong multiplicity one ⟹ the underlying normalized newforms are identical ⟹ eigensystems agree at every `p ∤ N`, contradicting `ev_i ≠ ev_j`. So the `ẽv_i` are pairwise non-equivalent, and the lemma gives L3.

Dependency: **per-character theory + L2 + strong multiplicity one ⟹ L3 ⟹ global Main Lemma.** No use of the global Main Lemma.

**Formal interface to check (SMO_packet):** the SMO theorem must yield `ev_i(p) = ev_j(p) for almost all p ⟹ ev_i = ev_j`. If the existing theorem is typed only for normalized primitive newforms, first attach to each occurring eigensystem its primitive representative via the per-character newform theory (this does NOT require the global Main Lemma).

## 3. Answers to Q1–Q4

- **Q1.** L3 is independently provable; not necessary to derive from "vanishing coprime coeffs ⟹ old." The §8.3 issue (merely-distinct multiplicative functions can be dependent) is real, but actual Hecke eigensystems are pairwise NON-equivalent by SMO, not merely distinct. So Main Lemma and L3 are not interdependent once SMO is available independently.
- **Q2.** Cleanest = the elementary multiplicative-functions argument (a strengthened Artin independence for ordinary, not completely, multiplicative functions). Li's newform theory only supplies primitive representatives + SMO. A Rankin–Selberg proof is valid but much heavier (needs `L(s,π_i×π̃_i)` simple pole at 1, cross-products holomorphic+nonvanishing). No need for a direct recursion-(R) argument.
- **Q3.** Correct that semisimplicity alone does not prove L3 (characters independent on the whole algebra need not stay independent after restriction). BUT the claim `span{T_n : (n,N)=1} ⊊ 𝕋` does NOT follow from the recursion — that identity only shows the diamond is IN the generated algebra, not that it's outside the linear span on this finite-dim space. In fact **L3 ⟺ span{T_n : (n,N)=1} = 𝕋** for the image algebra on `S_k(Γ₁(N))`: spectrally `𝕋 ≅ ℂ^X` (X = finite set of occurring eigensystems), `T_n ↦ (ev(n))_{ev∈X}`, and a functional annihilating all these vectors is exactly an L3 relation. So after L3, every diamond IS a (noncanonical, spectrum-dependent) ℂ-combination of good `T_n` as an operator on this space. L2 alone is not enough; the useful soft input is "distinctness persists after deleting any finite set of primes" = strong multiplicity one.
- **Q4.** Global Main Lemma now worth completing — cost is NOT a character-free sieve rerun, only: (1) the multiplicative-functions lemma; (2) the SMO corollary (distinct eigensystems non-equivalent); (3) zero-extension across primes | N; (4) the existing spectral reduction. Also yields the reusable corollary that the good `T_n` linearly span the acting Hecke algebra.

## References cited by reviewer
- Molteni, Lemma 1 (linear independence of pairwise non-equivalent multiplicative functions), citing Kaczorowski–Molteni–Perelli.
- Strong multiplicity one as determination from local components outside a finite set (e.g. the automorphic SMO literature).
- Li, "Newforms and functional equations" (Γ₁(N) newform theory / primitives).
