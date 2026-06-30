# Expert-review session state

- Generated: 2026-06-17
- Audience: senior modular-forms / Hecke-theory expert (general)
- Goal of brief: specific blocker — is L3 (linear independence of distinct Hecke eigensystems, relation imposed only at coprime arguments) provable without the Main Lemma, or is it inter-reducible with it?
- Scope: L3 blocker + broader Atkin–Lehner Main-Lemma / LMFDB-labels context
- Reply received: true (2026-06-18)
- Reply integrated: true (2026-06-18); round 2 follow-up sent

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Is L3 — ℂ-linear independence of finitely many distinct prime-to-level Hecke eigensystems, with the relation imposed only at arguments coprime to N — provable without assuming "a cusp form with vanishing prime-to-level coefficients is old" (the Main Lemma)? Or is it genuinely inter-reducible with it? |
| Q2 | If provable independently, what is the cleanest argument? Via (a) multiplicity-one / newform theory [Li75] not secretly using the Main Lemma, (b) an L-function / Rankin–Selberg nonvanishing argument at the level of Dirichlet coefficients, or (c) a direct argument with the recursion (R) showing the prime-to-level operators already span 𝕋? Reference ideal. |
| Q3 | Is the obstruction exactly "{T_n : (n,N)=1} do not linearly span the Hecke algebra (diamonds escape via (R))", so semisimplicity alone cannot give L3 — and is there nonetheless a soft reason (the eigensystem determining the full eigensystem via (R), L2) forcing the restricted characters to stay independent? |
| Q4 | Strategic: given the global Main Lemma has no downstream consumers (everything uses the per-character version) and the honest fallback is a full character-free re-run of the Miyake §4.6 sieve, is the global statement worth the cost, or is the per-character Main Lemma the natural stopping point? |

## Ticket-board snapshot at brief time

Relevant dev ticket: `mainLemma` (Atkin–Lehner Main Lemma, DS 5.7.1).
- Per-character Main Lemma (`mainLemma_charSpace_routeB`): PROVEN, axiom-clean (Miyake §4.6 sieve / conductor descent).
- Strong multiplicity one (`strongMultiplicityOne_axiom_clean`): PROVEN, axiom-clean.
- Global Γ₁(N) Main Lemma (`mainLemma`): proven modulo exactly one sorry — L3 (`eigensystems_linearIndependent`). The import-DAG file split, the eigenvalue↔coefficient identity (L1), the eigensystem⇒nebentypus lemma (L2), and the full spectral assembly (with zero-component filtering) are all proven.
- LMFDB labels (separate deliverable, does NOT depend on the global Main Lemma): canonical label map + canonicity axiom-clean, modulo 2 deep-NT sorries (Hecke eigenvalues are algebraic integers; coefficient field is a number field).

## Stuck points (from §8 of brief)

- 8.1 Spectral/Dedekind proof stalls: characters independent on all of 𝕋, but the relation lives only on span{T_n} ⊊ 𝕋 (diamonds escape via recursion (R)); recovering χ(p) is quadratic, not linear.
- 8.2 The "normalize + form Ψ = Σ c_i f_i, vanishing coprime coeffs ⇒ Ψ old ⇒ 0" proof is circular (invokes the Main Lemma).
- 8.3 Dedekind monoid-hom form needs complete multiplicativity (false; merely-multiplicative counterexample given); form-orthogonality gives form- not function-independence; recursion route reintroduces the Main Lemma / quadratic terms.
- 8.4 Apparent dichotomy: every route either needs operators outside span{T_n} or invokes the Main Lemma ⇒ L3 looks inter-reducible with the global Main Lemma. Only clearly non-circular route: re-run Miyake §4.6 sieve globally with ⟨d⟩ replacing χ(d) (~3000–5000 LOC).

## Reference list (from §2.2 of brief)

- [DS05] Diamond–Shurman, A First Course in Modular Forms, GTM 228, Springer 2005.
- [Miyake] Miyake, Modular Forms, Springer Monographs, 2006 (§4.6).
- [AL70] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970), 134–160.
- [Li75] W.-C. W. Li, "Newforms and functional equations", Math. Ann. 212 (1975), 285–315.
