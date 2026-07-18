# Expert-review session state

- Generated: 2026-05-11T00:00:00Z
- Audience: Frontier LLM (ChatGPT / Claude / Gemini)
- Goal of brief: Mixed — strategic soundness of the 5-epic plan; specific blocker T205-d; definitions/framing soundness; POST-1 general-χ ring hom obstruction
- Scope: Whole SMO pipeline (Epics A–E)
- Notation: Diamond–Shurman / Miyake conventions (slash with (det α)^(k-1), DS Prop 5.2.1 explicit T_p formula)
- Length: 9,000 words / ~14 pages
- Reply received: true (date: 2026-05-11)
- Reply integrated: true (date: 2026-05-11)

## Questions in the brief (verbatim from §9)

| # | Question |
|---|----------|
| Q1 | Is our Γ₀(N)-pivot structurally optimal? Was the abandonment of the direct Γ₁(N) abstract Hecke ring (blocked because adjugate swaps diag(1,p) ↔ diag(p,1), which are distinct Γ₁(N)-double cosets when p ≢ 1 (mod N)) the right structural choice for formalization? Is there a unified framework that avoids the character split? |
| Q2 | Should the general-χ ring homomorphism (POST-1) be unblocked, or can we permanently skip it? The abstract `heckeSlash_gen D f` (via Classical.choice Quot.out reps) does not equal the explicit T_p for general χ; we use the explicit operator throughout the character-space setting. Is the bifurcation (abstract for χ=1, explicit for general χ) right, or should we redefine the abstract action with built-in diamond twist? |
| Q3 | Is the combinatorial bijection in T205-d the right framing? We're stuck on σ-reindex on SL₂(ℤ)/Γ₁(N) absorbing γ₀, combined with matrix identity T_p_lower·T_p_upper(b) = p·shift(b) ∈ Γ₁(N). Should we (a) bypass via abstract slash adjugate + Hecke trace, (b) use the L-function functional equation (Phase 7) for a one-line proof, or (c) keep current path but find a slicker presentation? |
| Q4 | Is splitting Phase 8 into POST-6a/b/c/d/e (Miyake 4.6.3–4.6.8) correct given the ~12 KLOC of existing code that follows a support-based / Atkin–Lehner organization (via `IsSupportedOnDvd` / `qSupportedOnDvdSubmodule`) rather than Miyake's classical sub-decomposition? The support-based path has one open reverse-direction lemma (`isSupportedOnDvd_iff_in_levelRaise_image`) that Miyake's route avoids. Reorganize or accept? |
| Q5 | Critical-path realism: are we right to treat T205-d as the *single* critical blocker? Or are we underestimating POST-3 (L-functions, ~500 LOC from minimal foundations) — should we be running POST-3 with higher priority now? |
| Q6 | For T207 (simultaneous eigenform basis): use Mathlib's `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute` API (quick, obscures normality) vs. a from-scratch induction proof (3× longer, transparent role of normality + Gram-Schmidt). Which is preferable? |
| Q7 | Generality: are our definitions modular enough that the formalization could be extended to GL_n automorphic forms, Hilbert modular forms over totally real fields, or Maass forms with minor rework, or have we baked in GL_2-specific assumptions? |

## Ticket-board snapshot at brief time

26 tickets done; ~5 conditionally-closed (pending Phase 5); ~6 open; ~3 blocked.

**Done (Epics A, B, C, partial D):**
- Hecke pair (Γ₀(N), Δ₀(N))
- Shimura 3.20 n=2 (polynomial ring isomorphism R_p^(2) ≅ ℤ[X₁,X₂])
- Shimura 3.24 multiplication law (T(p)·T(1,p^k), T(p^r)·T(p^s))
- Shimura 3.35 level-N multiplication law (good primes)
- T_n commutativity on M_k(Γ₁(N))
- heckeRingHom (trivial χ) — full ring hom 𝕋_N → End(M_k(Γ₁(N), 1))
- Shimura Prop 3.34 good-prime case (nebentypus preserved by adjugate conjugation)
- χ-equivariance of T_p (Theorem 5.13)
- Petersson level-N inner product (positive-definite, Hermitian)
- Diamond operator unitarity ⟨⟨d⟩f, ⟨d⟩g⟩_N = ⟨f,g⟩_N
- peterssonInner_slash_adjoint (DS Prop 5.5.2(a))
- petN_slash_adjoint_GL2 (level-N version)
- Triple-product identity T_p_lower = γ₁⁻¹·T_p_upper(0)·γ₀
- heckeT_n_adjoint and heckeT_n_normal (conditional on T205-d)
- newform_unique (Atkin–Lehner uniqueness, DS 5.8.2 / Miyake 4.6.11)
- Hecke's Lemma (Miyake 4.6.3) via Smith decomposition
- Conductor Theorem (Miyake 4.6.4) — level descent or vanishing
- Coprime sieving (Miyake 4.6.5) — Möbius inversion
- Miyake 4.6.7 radical reduction

**Open (critical path):**
- T205-d / `petN_heckeT_p_diamond_shift_core` — the combinatorial bijection blocker
- T207 / `exists_simultaneous_eigenform_basis` — spectral theorem
- POST-4 / `mainLemma` — vanishing-coprime ⇒ oldform
- POST-3 / L-functions — Euler product, analytic continuation, non-vanishing
- POST-5 / `exists_nonzero_prime_eigenvalue` — blocked on POST-3
- POST-7 / `strongMultiplicityOne` — stated; sorry'd; blocked on T207, POST-4, POST-5

**Blocked:**
- POST-1 / general-χ abstract ring hom — Quot.out structural issue
- POST-2 / heckeT_p_all_comm_distinct refactor — gated on POST-1
- Reverse support-decomposition (`isSupportedOnDvd_iff_in_levelRaise_image`) — needs trace operator

## Stuck points (from §8 of brief)

1. T205-d: aggregate combinatorial bijection on SL₂(ℤ)/Γ₁(N) absorbing γ₀, with finite-index FD-transport lemma as residual
2. POST-1 general-χ ring hom: Classical.choice Quot.out reps propagate χ-factors that the explicit operator absorbs into the diamond twist — abstract and explicit operators disagree for χ≠1
3. Γ₀(N)-pivot history: was the abandonment of direct Γ₁(N) abstract Hecke ring (because adj swaps D(1,p)↔D(p,1)) the right call?
4. Phase 8 sub-ticket decomposition: support-based organization (with one open reverse-direction lemma) vs. Miyake's classical squarefree induction

## Reference list (from §2.2 of brief)

- [DS] Diamond–Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005
- [Miy] Miyake, *Modular Forms*, Springer 2006 (2nd printing)
- [Shi] Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, PUP 1971
- [AL] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970), 134–160
- [Hec] Hecke, "Über die Bestimmung Dirichletscher Reihen...", Math. Ann. 112 (1936), 664–699
- Rankin, *Modular Forms and Functions* (1977) — Rankin–Selberg bounds
