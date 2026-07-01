# Expert-review session state

- Generated: 2026-06-19
- Audience: senior modular-forms / arithmetic-geometry expert
- Goal of brief: specific blocker — is the deep input (q-expansion principle / integral model of X₁(N)) genuinely required to prove (A) Hecke eigenvalues a_n(f) are algebraic integers and (B) K_f = ℚ(a_n) is a number field, or is there an elementary / lighter-weight route?
- Scope: Group A only — the two isolated deep inputs in the newform-label development (`coeffSeq_isIntegral`, `instFiniteDimensionalCoeffField`). Everything else downstream is rigorous modulo these two.
- Reply received: true (2026-06-20)
- Reply integrated: true (2026-06-20)

## Questions in the brief

| # | Question (verbatim from §6 of the brief) |
|---|------------------------------------------|
| Q1 | (central) Is some form of the q-expansion principle / full-rank integral (or rational) structure on S_k(Γ₁(N)) genuinely necessary, or is there an elementary route we are missing? In particular, is there a proof of (A) — each a_n(f) an algebraic integer — that does NOT pass through an integral structure on the whole space (e.g. directly from integral relations satisfied by the Hecke operators, from a bound, or from the abstract double-coset Hecke ring)? |
| Q2 | (lightest route to full rank) If full rank is unavoidable, which route — geometric integral model vs. cohomological Eichler–Shimura/Manin modular-symbol integral structure — has the lightest prerequisites for a formal development, and is there a third more elementary route (explicit rational spanning set: Eisenstein products, theta series, η-quotients) for general N? |
| Q3 | (decoupling A and B) Is the number-field statement (B) obtainable more cheaply than integrality (A)? (B) only needs a finite-dimensional rational Hecke algebra on a rational form of S_k. Is "T_n defined over ℚ" strictly easier than the integral statement, and does that route also yield (A) or are they separate inputs? |
| Q4 | (restricting the space) Can the integral/rational structure be built only on a Hecke-stable subspace containing f (the new subspace, or the 𝕋-span of f), rather than all of S_k(Γ₁(N)) — and would that be meaningfully easier? |
| Q5 | (cleanest honest formalisation) Given a foundation with finite-dimensionality of S_k/ℂ, the explicit T_n coefficient formula, the diamond action, newform theory, strong multiplicity one — but no geometric/cohomological integral model — what is the cleanest single classical input to isolate and build (A)+(B) on? Is "S_k(Γ₁(N),ℤ) is a full-rank Hecke-stable lattice" the right atomic statement? |
| Q6 | (weight/level caveats) Do (A)/(B) or the cleanest route require hypotheses to be careful about (k ≥ 2; k = 1; small N; trivial vs non-trivial nebentypus)? We aim for all k ≥ 2, all N ≥ 1. |

## Ticket-board snapshot at brief time

Remaining `sorry`s in the formalisation (4 total, two independent groups):
- **Group A (this brief)** — `coeffSeq_isIntegral` (a_n algebraic integer), `instFiniteDimensionalCoeffField` ([K_f:ℚ]<∞). Both reduce to one input (QEP) = a Hecke-stable full-rank ℤ-lattice in S_k(Γ₁N); the T_n-stability half is provable, the full-rank half is the q-expansion principle. Plan doc: `.mathlib-quality/plan-coefficient-field-arithmetic.md`.
- **Group B (out of scope here)** — `T_gen_generates_R_p`, `evalHom_injective` (Shimura Thm 3.20, R_p^{(n)} ≅ ℤ[X₁..Xₙ], general n). Tractable mechanics, separate ticket chain (`plan-finish-remaining-sorries.md`, Track 2).

Just-completed (axiom-clean): the global Atkin–Lehner Main Lemma (L3 cross-character separation), via the hybrid independence core. Strong multiplicity one, newform theory in place.

## Stuck points (from §5 of brief)

1. Full rank of the candidate integral structure L = {f : a_n(f) ∈ ℤ}: that L (or its ℚ-analogue) spans S_k(Γ₁N) — i.e. S_k has a basis of integer/rational-q-expansion forms. T_n-stability of L is provable; full rank is the q-expansion principle.
2. The two heavy routes (geometric integral model [Katz, Deligne–Rapoport]; cohomological Eichler–Shimura/Manin) both large to formalise.
3. The Galois-descent ℚ-structure shortcut is circular (σ·f a cusp form already needs the rational structure).

## Reference list (from §2.2 of brief)

- [Shimura 1971] Intro Arith Theory of Automorphic Functions, Thm 3.48–3.52.
- [DS 2005] Diamond–Shurman, A First Course in Modular Forms, GTM 228.
- [Miyake 2006] Modular Forms, §4.5–4.6.
- [Katz 1973] p-adic properties of modular schemes and modular forms, LNM 350.
- [Deligne–Rapoport 1973] Les schémas de modules de courbes elliptiques, LNM 350.
- [Eichler–Shimura] H^1(Γ₁(N), Sym^{k-2}) integral structure.
- [Manin 1972] Parabolic points and zeta functions of modular curves (modular symbols).
