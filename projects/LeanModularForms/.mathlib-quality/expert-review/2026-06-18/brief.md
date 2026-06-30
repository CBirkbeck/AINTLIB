# Review brief (round 2) — deriving prime-level strong multiplicity one

*Prepared 2026-06-18 for the same senior modular-forms reviewer (follow-up to round 1). Self-contained; round-1 context recapped below.*

## 0. Recap of round 1 and where it landed

Round 1 asked whether **L3** — linear independence of finitely many distinct prime-to-`N` Hecke eigensystems `ev_i` (each from a nonzero common eigenform), with the relation `∑_i c_i ev_i(n)=0` imposed only at `n` coprime to `N` — is provable without the Atkin–Lehner Main Lemma. Your answer: **yes**, via
1. the multiplicative-functions lemma (pairwise *non-equivalent* multiplicative functions are ℂ-linearly independent; "equivalent" = agree at all but finitely many primes), and
2. **strong multiplicity one to upgrade "distinct" to "non-equivalent."**

We implemented (1) and the cross-character part of (2): if `χ_i ≠ χ_j` the eigensystems differ at infinitely many primes for free (Dirichlet: infinitely many primes in each coprime residue class, available to us; the prime-square relation `χ(p)=p^{1-k}(ev(p)^2-ev(p^2))` then forces a differing p-component). That leaves exactly the **same-nebentypus** case of your step (2):

> **(SMO-prime).** Two distinct normalized newforms of level `N` and the same nebentypus `χ` differ in `T_p`-eigenvalue at infinitely many primes `p` — equivalently, if `a_p(f)=a_p(g)` for all but finitely many `p`, then `f=g`.

This is the "SMO_packet" you flagged. It is exactly what the Molteni induction needs (its "delete one prime" step is robust only because non-equivalence means *infinitely* many differing primes).

## 1. The precise mismatch with what we have

The strong-multiplicity-one theorem we have formalized is at the **integer** level, not the prime level:

> **(SMO-int).** Let `f, g` be normalized newforms of level `N` and the same nebentypus `χ`. If there is a **finite set of integers** `S` such that `a_n(f)=a_n(g)` for every `n` coprime to `N` with `n ∉ S`, then `f = g`.

(SMO-int) does **not** obviously give (SMO-prime): "agree at all but finitely many *primes* `p ∉ P`" propagates (via the recursion, since `χ` is fixed) to "agree at all `n` coprime to `∏P`," but the residual disagreement is permitted on the **multiples of `∏P` — an infinite set of integers** — so the finite-`S` hypothesis of (SMO-int) is not met. Within a fixed `χ`, the eigenvalue is a function of the prime values, and the bad-prime data is not linearly recoverable from the coprime-coefficient relation.

## 2. What we believe (and want confirmed)

We believe **(SMO-prime) is derivable from (SMO-int) together with the classical per-character newform/conductor theory we already have — Atkin–Lehner–Li style — with NO recourse to GL(2) Rankin–Selberg.** We would like the cleanest such derivation, tailored to the toolbox in §3, so we can formalize it directly. (If, contrary to our belief, it genuinely requires Rankin–Selberg nonvanishing, please say so — but our reading of Li 1975 is that the classical argument is elementary in this sense.)

## 3. Toolbox available to us (all formalized, all independent of the *global* Main Lemma)

- **(SMO-int)** as in §1.
- **Per-character Main Lemma** (Miyake §4.6 / conductor descent): a cusp form in `S_k(N,χ)` with vanishing prime-to-`N` coefficients is old. (Note: this is per-character; it is the one we rely on, and it is independent of the global statement we are ultimately after.)
- **Newform structure / old–new decomposition** per character: `S_k(Γ_1(N)) = ⊕_χ S_k(N,χ)`, the new subspace, and the degeneracy/level-raising maps `f(z) ↦ f(dz)`.
- **Conductor theory**: a dichotomy theorem identifying the conductor of a form / when a form descends to level `N/p` (the engine behind Miyake 4.6.4 in our development).
- **Hecke recursion** `T_{p^{r+2}} = T_p T_{p^{r+1}} − p^{k-1}⟨p⟩ T_{p^r}` (operator level), the prime-square relation, and the eigenvalue↔coefficient identity `a_n(f)=ev_f(n)·a_1(f)` on character spaces.
- **Dirichlet's theorem** (infinitely many primes in each coprime residue class).

## 4. Questions

**Q1 (the main one).** Give the cleanest derivation of **(SMO-prime)** from the §3 toolbox. Concretely: how does one pass from "`a_p(f)=a_p(g)` for all but finitely many primes" to "`f=g`" for same-`χ` level-`N` newforms, using the newform/conductor theory rather than analytic nonvanishing? (E.g.: does one form `h=f−g`, observe `a_p(h)=0` for almost all `p`, and conclude `h=0` by a conductor/old–new argument? If so, what is the exact mechanism that rules out a nonzero `h` with `a_p(h)=0` for almost all `p` but not all — i.e. how are the finitely many exceptional primes closed off?)

**Q2.** Is it cleaner to prove (SMO-prime) as the *contrapositive infinitude statement* ("distinct same-`χ` newforms differ at infinitely many primes") directly — perhaps by a counting/conductor argument — rather than as the rigidity statement "agree at almost all primes ⇒ equal"? Either form suffices for the Molteni step.

**Q3.** A possible shortcut: in our application the `ev_i` arise from a single finite-dimensional space `S_k(Γ_1(N))`, so there are only finitely many of them, of bounded conductor (dividing `N`). Does bounded conductor + same nebentypus make (SMO-prime) easier (e.g. the exceptional-prime set is uniformly controlled by `N`)? Equivalently: does it suffice to prove "distinct same-`χ`, conductor-dividing-`N` newforms differ at *some* prime in a controlled finite range," which together with the recursion already yields infinitely many differing primes?

**Q4.** Sanity check on the reduction: with (SMO-prime) in hand, do you agree the global Main Lemma closes as round-1 prescribed — Molteni independence (non-equivalence from (SMO-prime) same-`χ` + Dirichlet cross-`χ`) ⇒ L3 ⇒ (spectral reduction + per-character Main Lemma) global Main Lemma — with no remaining analytic input?

## 5. Metadata

- Round 2 of an expert review; round-1 brief + reply on file.
- Status: global Main Lemma reduced to the single statement (SMO-prime); same-character-only L3 is independently closable (a recursion-based minimal-support induction) but does not cross characters, so (SMO-prime) is the genuine remaining input.
