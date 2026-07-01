# Reviewer reply (round 2) — 2026-06-18

## Verdict
Belief correct, with a refinement: **(SMO-prime) does NOT follow from (SMO-int). It follows immediately from the AUXILIARY-integer version of the per-character Main Lemma.** (SMO-int) "forgot" the parameter needed to absorb the finite exceptional prime set. Round-1 reduction stays valid once this auxiliary lemma is restored. No Rankin–Selberg.

## The key new lemma (the smallest honest addition)
Let `m_χ` = conductor of `χ`. The needed form of Miyake's sieve:

**(AML) Auxiliary-L Main Lemma.** `F = ∑ a_n(F) q^n ∈ S_k(N,χ)`, `L ≥ 1`, and `a_n(F)=0` whenever `(n,L)=1`. Then `F(z) = ∑_{p | gcd(L, N/m_χ)} F_p(pz)` with `F_p ∈ S_k(N/p, χ)`; in particular `F` is old, and if `gcd(L, N/m_χ)=1` then `F=0`.

Our current per-character Main Lemma is the special case **L = N**. We need arbitrary L. For the application, only the **newspace corollary** is needed:

**(ANV) Auxiliary vanishing in the newspace.** `F ∈ S_k(N,χ)^new` and `a_n(F)=0` for all `(n,L)=1` ⟹ `F=0`.

Proof of (AML) = the same one-character sieve/conductor descent we already use, keeping L arbitrary: (1) one prime p — a form supported on multiples of p is `V_p G`; conductor descent ⟹ `G ∈ S_k(N/p,χ)` or 0; (2) squarefree L — coefficient sieve over `∪ {p|n}`; (3) induct on #prime divisors of L; (4) conductor descent removes all `p ∤ N/m_χ`. **NOT a character-free rerun of the global Main Lemma.**

## Q1 — derivation of (SMO-prime) from (ANV)
`f,g ∈ S_k(N,χ)^new` normalized newforms, `a_p(f)=a_p(g)` for good `p` outside finite `P`. Set `L = rad(N · ∏_{p∈P} p)`. For `q ∤ L`: `q∤N`, `q∉P`, so `a_q(f)=a_q(g)`; same χ ⟹ same recursion `a_{q^{r+2}} = a_q a_{q^{r+1}} − χ(q)q^{k-1} a_{q^r}`; with `a_1=1` ⟹ `a_{q^r}(f)=a_{q^r}(g)` ∀r; multiplicativity ⟹ `a_n(f)=a_n(g)` for all `(n,L)=1`. So `h=f−g` has `a_n(h)=0` for `(n,L)=1`. By (ANV) (`h` is new) ⟹ `h=0` ⟹ `f=g`. The exceptional-prime mechanism: `p∤N/m_χ` ⟹ p-supported contribution vanishes (conductor descent); `p|N/m_χ` ⟹ descends to `S_k(N/p,χ)`, hence old. Both ruled out since `h` is new.

## Q2 — rigidity vs infinitude
Same proof. Formalize **rigidity** (`a_p(f)=a_p(g)` almost all p ⟹ f=g) as the main theorem; the **infinitude contrapositive** (`f≠g ⟹ {p∤N : a_p(f)≠a_p(g)}` infinite) is a one-line corollary — that's the form Molteni non-equivalence consumes.

## Q3 — bounded conductor: NO shortcut
"differ at one controlled prime + recursion ⟹ differ at ∞ many primes" is FALSE: disagreement at `p, p², p³, …` stays in the SINGLE local p-component; Molteni-equivalence ignores finitely many entire prime components. Finite-dimensionality gives only a finite test for **distinctness** (some bound B, every distinct pair differs at a prime ≤ B), NOT non-equivalence. Bounded conductor does not force exceptional primes to divide N.

## Q4 — closure + the interface to audit
Yes, the round-1 chain closes with no Rankin–Selberg: **auxiliary-L sieve ⟹ same-χ (SMO-prime) ⟹ same-χ non-equivalence; Dirichlet+prime-square ⟹ cross-χ non-equivalence; Molteni ⟹ L3; L3 + spectral reduction + per-char Main Lemma ⟹ global Main Lemma.** (AML) is per-character, same sieve — no circularity.

**INTERFACE TO AUDIT:** the (ANV) derivation is for newforms of the **same EXACT level N** and character χ. Sufficient IF the spectral reduction is restricted to the level-N newspace, or otherwise every same-χ pair compared is represented by exact-level-N newforms. **If the eigensystems include primitive representatives of different conductors M_1, M_2 | N**, the fixed-level version is NOT enough — need either (a) an earlier reduction eliminating mixed-conductor pairs, or (b) the **varying-level** strong multiplicity one (also proves M_1=M_2). The varying-level proof still avoids Rankin–Selberg but uses Euler products + functional equations (Li 1975) — analytically heavier than the same-level auxiliary-sieve proof.

## Recommendation
Export **(ANV)** (auxiliary-L newspace vanishing) — smallest honest addition. Then (SMO-prime) = short recursion+multiplicativity + one (ANV) application, and the round-1 Molteni route closes. Audit Q4: ensure same-χ comparisons are exact-level-N (else add varying-level SMO).
