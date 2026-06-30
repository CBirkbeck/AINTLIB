# Reply integration — 2026-06-18

Reviewer reply: ./reply.md  (verdict: L3 provable non-circularly via Molteni multiplicative-functions lemma + SMO non-equivalence)

## Implementation outcome (after a feasibility+implementation pass)

The reviewer's proof is mathematically correct and non-circular, BUT formalization hit a precise interface gap the reviewer himself flagged ("SMO_packet"):

- **Molteni lemma** (pairwise non-equivalent multiplicative functions are independent): fine to prove; needs each pair to differ at INFINITELY many primes (the induction's "delete one prime" step is robust only under that).
- **Cross-character non-equivalence**: FREE. Distinct nebentypus ⇒ distinct characters ⇒ (Dirichlet, mathlib `Nat.infinite_setOf_prime_and_eq_mod`) differ at infinitely many primes via the prime-square relation.
- **Same-character non-equivalence** (two distinct same-χ eigensystems differ at infinitely many primes): this is the reviewer's "SMO_packet" = strong multiplicity one at the PRIME level (agree at almost all primes ⇒ equal). **Our codebase SMO (`strongMultiplicityOne_axiom_clean`) is INTEGER-level** (agree at all coprime n outside a FINITE integer set ⇒ equal). Integer-level does NOT give prime-level: finitely many bad primes ⇒ infinitely many bad integers (their multiples), so the finite-S theorem cannot be invoked; and within a fixed χ the recursion makes the bad-prime data un-recoverable linearly.
- **Same-character-only L3** is in fact closable WITHOUT infinitude, via a recursion-based minimal-support induction (χ(p) constant ⇒ the prime-square recursion lets the Dedekind shift act at all coprime arguments). But it **cannot cross characters** (varying χ_i(p) breaks the cancellation), and the cross-character coefficient separation is provably blocked (the χ-twisted relation `∑ c_i χ_i(p) ev_i(n)` is not derivable from the untwisted relation — collapses to a tautology).

## Net: refined gap

Global (multi-character) L3 — hence the global Main Lemma — reduces to ONE classical statement absent from the codebase and mathlib:

> **(SMO-prime)** Two distinct same-nebentypus normalized newforms differ in eigenvalue at infinitely many primes (equivalently: agree at almost all primes ⇒ equal).

This is classical strong multiplicity one at prime level (Atkin–Lehner–Li, or via GL(2) Rankin–Selberg). Whether it is (a) derivable from our integer-level SMO + the already-proven per-character newform theory (Li-style, no Rankin–Selberg) or (b) genuinely needs Rankin–Selberg is the open question for a follow-up round.

## Proposed follow-up question for the reviewer (round 2)

Our "strong multiplicity one" is integer-level: for two normalized newforms of level N and the same nebentypus χ, agreeing in Tₙ-eigenvalue at all n coprime to N OUTSIDE A FINITE SET OF INTEGERS ⇒ the forms are equal. The Molteni route needs the PRIME-level form (differ at infinitely many primes / agree at almost all primes ⇒ equal). (1) Is prime-level SMO derivable from this integer-level SMO together with the per-character newform/conductor theory (and the proven per-character Main Lemma), WITHOUT importing GL(2) Rankin–Selberg? (2) If yes, the cleanest chain. (3) If it genuinely needs Rankin–Selberg nonvanishing, confirm — that settles the cost of the global Main Lemma.

## State

- Reply received: true (2026-06-18). Reply integrated: true.
- No ticket edits; the L3 sorry remains, now with the gap precisely characterized as (SMO-prime).
- Same-character-only L3 is closable today (recursion route, ~150–200 LOC) if a partial win is wanted.
