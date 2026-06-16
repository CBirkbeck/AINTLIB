# Reviewer reply — 2026-05-16

## Assessment

Route B is viable in its **per-character Main Lemma** part, but the current three-obligation closure plan is overcomplicated and partly mathematically suspect.

The key insight is correct: `newform_unique` only needs the Main Lemma inside the fixed Nebentypus space containing $(f-g)$. There is no need to prove an unconditional Main Lemma by projecting an arbitrary cusp form to character components. The inheritance obstruction for diamond projections is real: diamond operators generally move the cusp $\infty$, so Fourier vanishing at $\infty$ is not automatically inherited by $\chi$-components.

However, obligations **B.L3.1** and especially **B.L3.2** should not be on the SMO critical path unless the project is proving a much stronger analytic theorem. For the finite-exception SMO statement currently described, the analytic "nonzero prime eigenvalue" theorem is unnecessary. If equality is assumed for all $n$ coprime to $N$ outside a finite set $S \subset \mathbb{N}$, then exceptional $n$'s can be handled algebraically using a prime $q \notin S$ and, if necessary, $q^2$. If equality is assumed only at primes outside a finite set of primes, then multiplicativity and the prime-power recurrence already give equality for all $n$ coprime to the product of the exceptional primes, and the **general $L$-version** of Miyake's Main Lemma is the right tool.

So the strongest recommendation is: **do not spend current effort formalizing Hecke's functional equation or Dirichlet trivial-zero non-cancellation for SMO closure.** Focus on A.L3, plus a purely algebraic finite-exception bridge.

There is also a concrete issue in the stated A.L3 sieve formula. The idea is right, but the displayed formula should be reorganized as an inclusion–exclusion over **squarefree** divisors of $\mathrm{rad}(N)$. The projection $P_p := V_p U_p$ keeps coefficients whose index is divisible by $p$. Then

$$1 - \prod_{p \mid N}(1 - P_p) = \sum_{\varnothing \ne T \subseteq \{p : p \mid N\}} (-1)^{|T|+1} \prod_{p \in T} P_p$$

is the operator that keeps exactly the coefficients divisible by at least one prime of $N$. Under the hypothesis that coefficients coprime to $N$ vanish, this operator is the identity on $f$. This is the clean formal route.

## Mathematical idea

For per-character newform uniqueness, set $h = f - g$. Since both $f$ and $g$ lie in $S_k(\Gamma_1(N), \chi)$, so does $h$. Equality of eigenvalues in the relevant range gives vanishing of the Fourier coefficients of $h$ in that range. The per-character Main Lemma then gives $h \in S_k^{\mathrm{old}}(\Gamma_1(N))$. Since $h$ is also in the newspace, $h = 0$.

The Main Lemma input can be obtained algebraically. For each prime $p \mid N$, define $P_p = V_p U_p$, whose $q$-expansion is

$$P_p f = \sum_{p \mid n} a_n(f) q^n.$$

The operators $P_p$ commute with each other at the coefficient level and preserve the character space if the project's bad-prime $U_p$ and same-level $V_p U_p$ diamond-commutation lemmas are available. For nonempty squarefree $d = \prod_{p \in T} p$, define

$$f_d := (-1)^{|T|+1} \left(\prod_{p \in T} P_p\right) f.$$

Then $f_d$ is supported on multiples of $d$, remains in the $\chi$-space, and the inclusion–exclusion identity gives

$$f = \sum_{\varnothing \ne T \subseteq \{p : p \mid N\}} f_{\prod T}$$

whenever $a_n(f) = 0$ for $(n, N) = 1$. This is exactly the same-level divisor decomposition needed by the project's consumer theorem.

For finite exceptional sets of **natural numbers**, no analytic nonvanishing theorem is needed. Fix $n$ coprime to $N$. Choose a prime $q$ such that

$$q \nmid Nn, \quad q, q^2, nq, nq^2 \notin S.$$

If $\lambda_q(f) \ne 0$, multiplicativity gives

$$\lambda_{nq}(f) = \lambda_n(f) \lambda_q(f),$$

and the same for $g$, so cancellation gives $\lambda_n(f) = \lambda_n(g)$. If $\lambda_q(f) = 0$, use the good-prime recurrence

$$\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) q^{k-1} = -\chi(q) q^{k-1} \ne 0.$$

Then apply multiplicativity to $nq^2$ and cancel $\lambda_{q^2}$. This extends equality from "outside $S$" to all $n$ coprime to $N$, entirely algebraically.

## Lean-facing next steps

First, park B.L3.1 and B.L3.2 as non-critical. They may be valuable long-term L-function infrastructure, but they should not be blocking the present SMO route.

Create a ticket for the corrected A.L3 sieve: a per-character same-level divisor decomposition from coprime-to-$N$ Fourier vanishing, theorem should be squarefree-divisor based. Do not define one summand for every divisor of $N$ unless that is already more convenient locally; zero-fill nonsquarefree divisors only if the existing API requires all divisors.

Second, create a purely algebraic finite-exception bridge: equality outside a finite set of coprime indices implies equality at all coprime indices, using $q$ or $q^2$ and the good-prime recurrence. The proof needs an elementary prime-avoidance lemma: choose a prime $q$ outside a finite set of forbidden primes and forbidden numbers. Then split on whether $\lambda_q(f) = 0$. If zero, use the recurrence for $\lambda_{q^2}$ and the fact that $\chi(q) \ne 0$ for $q \nmid N$.

Third, close `newform_unique` using the per-character Main Lemma, not the unconditional Main Lemma. Key proof steps: $h = f - g$ lies in the same cusp-form character space; coefficient/eigenvalue identification gives coprime coefficient vanishing; A.L3 plus the same-level divisor consumer gives $h \in S^{\mathrm{old}}$; newspace disjointness gives $h = 0$.

Finally, assemble SMO from the finite-exception bridge plus `newform_unique_of_charSpace_mainLemma`.

## Risks or missing facts

The main risk is that the project's $P_p = V_p U_p$ operator may not literally be a same-level endomorphism in the needed form. If `heckeT_p_divN` and `modularFormLevelRaise` only compose through a lower-level or higher-level type, the ticket should first create a packaged same-level projection $P_p$ with a theorem about its $q$-expansion and character preservation. This is the correct local API boundary.

The second risk is the bad-prime diamond-commutation claim. For good-prime $T_p$, this is standard. For bad-prime $U_p$, it should still be true by direct double-coset or coefficient/operator computation, but the worker should not cite DS Prop 5.2.4(a) blindly if that proposition is stated only for $p \nmid N$. Make the bad-prime $U_p$-diamond commutation a local lemma if it is not already available.

The third risk is A.L3's formula. The formula in the brief is not quite right as written. Use inclusion–exclusion over nonempty squarefree subsets: $\sum_{\varnothing \ne T} (-1)^{|T|+1} \prod_{p \in T} P_p$, not a direct sum of $P_d f$ over all $d \mid N$ with coefficient $+1$.

The fourth risk is B.L3.2. The proposed trivial-zero Dirichlet contradiction is not reliable as stated. With the correct collapsed Euler product one typically gets a quotient like $L(2w, \chi^2) / L(w, \chi)$ with $w = 2s - k + 1$, and trivial zeros of $L(w, \chi)$ are often accompanied by trivial zeros of $L(2w, \chi^2)$. This can cancel the proposed pole. The trivial-character and quadratic-character cases are especially dangerous. If analytic nonvanishing is needed later, a Rankin–Selberg nonvanishing/pole argument is probably more robust than the proposed trivial-zero quotient argument.

The fifth risk is theorem statement drift. If the intended final SMO hypothesis is equality of eigenvalues for all $n$ outside a finite set, the algebraic finite-exception bridge above is enough. If the intended final theorem only assumes equality at primes outside a finite set of primes, then the right bridge is different: use multiplicativity and the prime-power recurrence to get equality for all $n$ coprime to $N$ and to the exceptional primes, then apply the **general $L$-version** of Miyake's Main Lemma. Do not use the analytic nonzero-prime theorem for this finite-prime version either.

## Manager message to worker

TICKET: RouteB-SMO
STATUS: active
LEAN ISSUE: no
MATH ISSUE: yes — current three-obligation plan includes unnecessary and risky analytic obligations
BLOCKER: per-character Main Lemma / same-level divisor decomposition

The per-character Route B insight is correct. For `newform_unique`, we only need the Main Lemma for $h = f - g$ inside the fixed Nebentypus space $S_k(\Gamma_1(N), \chi)$. Do not try to recover an unconditional Main Lemma by character projection; the Fourier-vanishing inheritance obstruction at $\infty$ is real because diamond operators can move the cusp.

But stop treating B.L3.1 and B.L3.2 as SMO-critical. The analytic Dirichlet-L-function/trivial-zero route is both unnecessary for the finite-exception theorem and risky as stated. In particular, the quotient under the "almost all $a_q = 0$" hypothesis involves doubled arguments such as $L(2w, \chi^2) / L(w, \chi)$, and denominator trivial zeros may be canceled by numerator trivial zeros. Do not assign this as the next SMO-closing work.

Next target should be A.L3, but with a corrected squarefree inclusion–exclusion formulation. Define $P_p := V_p U_p$, where $U_p$ is the bad-prime operator and $V_p$ is level raising, packaged as a same-level coefficient projection satisfying $a_n(P_p f) = a_n(f)$ if $p \mid n$, else $0$. Then prove $P_p$ preserves the $\chi$-space. If bad-prime $U_p$-diamond commutation is not already available, prove that local lemma directly; do not cite a good-prime-only DS lemma.

For nonempty squarefree $d = \prod_{p \in T} p \mid \mathrm{rad}(N)$, define $f_d := (-1)^{|T|+1} \left(\prod_{p \in T} P_p\right) f$. Then prove:

1. each $f_d$ lies in the same cusp-form character space;
2. each $f_d$ has $q$-support on multiples of $d$;
3. $\sum_{\varnothing \ne T \subseteq \{p : p \mid N\}} f_{\prod T} = f$ if $a_n(f) = 0$ for $(n, N) = 1$.

Feed this into the existing same-level divisor decomposition consumer to get $f \in S_k^{\mathrm{old}}$.

In parallel or immediately after A.L3, add the algebraic finite-exception bridge so no analytic nonzero-prime theorem is needed.

Acceptance criteria for the next worker pass:

* A compiling squarefree inclusion–exclusion A.L3 theorem, or one exact missing same-level $P_p = V_p U_p$ projection lemma.
* No new work on Hecke functional equations, Dirichlet trivial zeros, or B.L3.2 until A.L3 and the algebraic finite-exception bridge are closed.
