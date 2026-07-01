# Reviewer reply — 2026-05-17 brief

## Assessment

The Miyake §4.6 chain is now the right mathematical lane, but the brief contains two important statement-level hazards that should be corrected before workers continue.

First, the claimed "B.L1 algebraic q/q² bridge" is only valid for a hypothesis of equality of **all Hecke eigenvalues indexed by natural numbers** outside a finite set. It is **not** valid from equality at all but finitely many primes. If $a_p(f)=a_p(g)$ for all primes outside a finite exceptional set $S$, recurrence at $q^2$ for a good auxiliary prime $q\notin S$ does not determine the missing exceptional eigenvalue $a_r$ at $r\in S$. The classical SMO proof does not recover exceptional prime eigenvalues directly; it shows $h=f-g$ has Fourier support only on integers divisible by the exceptional primes, then applies Miyake's Main Lemma. So the route must be:

prime equality outside $S$
$\Rightarrow a_n(f-g)=0$ for $(n,N\prod_{p\in S}p)=1$
$\Rightarrow$ Miyake 4.6.8
$\Rightarrow f-g\in S^{old}$
$\Rightarrow f-g=0$.

Second, the per-character route is correct and valuable, but the "prime-only" version of the per-character Main Lemma is not correct for a generic cusp form. The Main Lemma input must be vanishing of Fourier coefficients $a_n$ for all $n$ in a coprime range, not merely for prime $n$, unless the form is already known to be an eigenform and multiplicativity has been used to extend prime equality to all coprime integers.

The remaining M5–M8 descent chain is mathematically faithful to Miyake. The inter-level descent operator $\Phi_p$, Miyake 4.6.6 level commutation, squarefree decomposition, and induction are the right targets. But the current M5 bundle is probably overgeneralized: do not force a full map $M_k(\Gamma_1(N))\to M_k(\Gamma_1(N/p))$ unless needed. For the Main Lemma, the useful object is the character-space descent map under the hypothesis that $\chi$ factors through $N/p$, i.e. $p\mid N/\mathrm{cond}(\chi)$. That avoids the awkward "nonfactoring character component vanishes" proof.

## Mathematical idea

For the descent operator, the coset-list action property is the key structural theorem. If $\gamma'\in\Gamma_0(N/p)$, one needs

$$\gamma_v\gamma'=\alpha_v\gamma_{\sigma(v)}$$

with $\alpha_v\in\Gamma_0(N)$, and with the nebentypus of $\alpha_v$ matching the descended nebentypus of $\gamma'$. This proves character preservation of the slash sum on character spaces.

The upper-triangular case is just the standard affine action on $\mathbb P^1(\mathbb F_p)$. With

$$\gamma_v=\begin{pmatrix}1&v\\0&p\end{pmatrix},\qquad \gamma'=\begin{pmatrix}A&B\\C&D\end{pmatrix}$$

and $p^2\mid N$, hence $p\mid C$, set

$$v' \equiv A^{-1}(B+vD)\pmod p.$$

Then

$$\alpha_v=\begin{pmatrix}A+vC & \frac{B+vD-(A+vC)v'}{p}\\pC & D-Cv'\end{pmatrix}$$

has determinant $1$, lower-left entry divisible by $N$, and satisfies

$$\begin{pmatrix}1&v\\0&p\end{pmatrix}\gamma' = \alpha_v\begin{pmatrix}1&v'\\0&p\end{pmatrix}.$$

This is the clean raw matrix identity the Lean proof should target before coercing into $\mathrm{GL}_2(\mathbb R)$.

The extra representative when $p^2\nmid N$ is classical CRT/strong approximation for $\mathrm{SL}_2(\mathbb Z)$: choose $\tilde\gamma_p\equiv S\pmod p$ and $\tilde\gamma_p\equiv I\pmod{N/p}$. This should be proved by a general lemma $\mathrm{SL}_2(\mathbb Z)\to \mathrm{SL}_2(\mathbb Z/N\mathbb Z)$ is surjective, or by a narrowly tailored CRT construction for this one pair of congruences.

The normalization $p/C_{N,p}$ is harmless and arguably better for Lean. If the unnormalised slash sum sends $V_pg$ to $(C_{N,p}/p)g$, then multiplying by $p/C_{N,p}$ makes $\Phi_pV_p=\mathrm{id}$. This changes only scalar conventions, not the induction. Just ensure every later occurrence of Miyake's formulas uses the project's normalized $\Phi_p$.

## Lean-facing next steps

Correct the theorem statements in the route plan first. The top-level SMO proof from "all but finitely many primes" should not claim equality at every exceptional prime by q/q². Instead, define $L$ as the product of the exceptional primes, or $L=N\cdot\prod S$ depending on the local statement, prove coefficient equality/vanishing for all $n$ coprime to $NL$, and feed that into Miyake 4.6.8.

For the descent chain, the cleanest API boundary is a character-space descent operator: input χ that factors through N/p, output a linear map between character spaces. Avoid a full-space $\Phi_p$ unless the project later needs it. If the current code already has a full-space `miyake_hecke_descend` target, consider proving a character-space version first and deriving the full version only after the SMO-critical path is closed.

For the Lean matrix blocker, do not fight $\mathrm{GL}_2(\mathbb R)$ coercions directly. Add a raw lemma over integer or rational matrices:

```lean
private lemma descend_upper_tri_raw_matrix_identity
    (p : ℕ) (hp : 0 < p)
    (A B C D v v' a01 : ℤ)
    (hC : (p : ℤ) ∣ C)
    (hv' : (A * v' - (B + v * D)) % p = 0)
    (ha01 : (p : ℤ) * a01 = B + v * D - (A + v * C) * v') :
    !![1, v; 0, (p : ℤ)] ⬝ !![A, B; C, D]
      =
    !![A + v*C, a01; (p : ℤ)*C, D - C*v'] ⬝ !![1, v'; 0, (p : ℤ)]
```

Then map this equality into $\mathbb R$ and the bundled `GL` objects. Entry proofs should then be `ring`/`omega` after the four entries are normalized.

If the worker must simplify `Matrix.vecCons ... ⟨0,h⟩`, use local index-normalization lemmas rather than relying on global simp:

```lean
have h0 : (⟨0, h⟩ : Fin 2) = 0 := by ext; rfl
rw [h0]
simp
```

and similarly for `⟨1,h⟩`. Even better: prove matrix equalities before the goal creates noncanonical `Fin.mk` indices.

Priority order: close `descendCosetList_action_upper_tri_clean` as a raw matrix lemma first, because it is mathematically understood and the current blocker is only Lean plumbing. Then prove the CRT/strong-approximation lemma for `descendExtraGamma_exists`. Then close the extra-representative action lemma and bundle M5a. After M5a, prove the character-space descent map, not necessarily the full-space map. Then M6, M7, and M8 should become straightforward formal induction and support bookkeeping.

## Risks or missing facts

The largest mathematical risk is the false prime-exception bridge. Equality away from finitely many primes does not algebraically imply equality at the exceptional primes by the q/q² recurrence. The general multi-prime Main Lemma is needed precisely to avoid this.

The second risk is overgeneralizing $\Phi_p$. If the proof only needs character spaces with χ descending to N/p, requiring a full map on all $M_k(\Gamma_1(N))$ introduces an unnecessary and subtle trace-kills-nonfactoring-characters claim. That claim is standard in trace-map language, but it is not the cleanest SMO-critical API.

The third risk is character/conductor bookkeeping. The descent target character $\chi_0$ exists only when χ factors through $N/p$. In the final Main Lemma, the primes that can be removed should be primes dividing $N/\mathrm{cond}(\chi)$, not arbitrary primes dividing $N$.

The fourth risk is the non-SL conjugation in T6b. The statement "$\Gamma(N)$ is normal, so conjugation by $\mathrm{diag}(1,p)$ preserves it" is not valid, because $\mathrm{diag}(1,p)\notin \mathrm{SL}_2(\mathbb Z)$. The entrywise calculation can still be correct because $p\mid N$, so the divided entry is integral and the congruences remain strong enough. The proof should use explicit entries, not normality.

The fifth risk is relying on matrix-literal simplification in bundled GL goals. This is a Lean-structure problem, not mathematics. Raw matrix equalities should be separated from `GL`/`SL` packaging.

## Manager message to worker

TICKET: Miyake-4.6 descent chain
STATUS: active
LEAN ISSUE: yes — current blocker is raw matrix simplification under bundled $\mathrm{GL}_2(\mathbb R)$
MATH ISSUE: yes — route statements need one correction before continuing
BLOCKER: `descendCosetList_action_upper_tri_clean` / M5a raw matrix identity

Important correction: do not use or advertise the "q/q² bridge" as proving equality at all exceptional primes from equality at all but finitely many primes. That implication is false for a prime-only exceptional hypothesis. For textbook SMO, the right route is: equality at good primes gives $a_n(f-g)=0$ for all $n$ whose prime factors avoid $N$ and the finite exceptional prime set; then Miyake 4.6.8 with that exceptional product gives oldness; newness gives zero. Keep the Main Lemma multi-prime chain as the critical path.

Also correct the per-character Main Lemma statement: for a generic cusp form, vanishing at primes alone is not enough. The Main Lemma input is vanishing of all Fourier coefficients in the relevant coprime range. For $h=f-g$, derive that range from eigenform multiplicativity/prime-power recurrence before applying the Main Lemma.

Next proof task: close `descendCosetList_action_upper_tri_clean`, but do it as a raw `Matrix (Fin 2) (Fin 2) ℤ` identity first. Do not fight `Units.ext`/`mkOfDetNeZero`/$\mathrm{GL}_2(\mathbb R)$ coercions until the raw matrix equation is proved.

For the `Matrix.vecCons ... ⟨0,h⟩` blocker, either avoid generating these goals, or normalize indices locally with `have h0 : (⟨0, h⟩ : Fin 2) = 0 := by ext; rfl; rw [h0]; simp`.

After T5a-3a-clean, prove `descendExtraGamma_exists` via the standard surjectivity $\mathrm{SL}_2(\mathbb Z)\to \mathrm{SL}_2(\mathbb Z/N\mathbb Z)$, or a narrowly tailored CRT lift.

For M5 bundle, prefer a character-space descent operator with an explicit hypothesis that χ factors through $N/p$. Do not block SMO on a full-space map.

### Acceptance criteria for the next pass

1. `descendCosetList_action_upper_tri_clean` closed, or a raw matrix lemma with the exact remaining coercion obstacle reported.
2. No changes to the top-level SMO bridge that claim exceptional prime equality follows from q/q² recurrence.
3. If M5 bundle is touched, refactor toward a character-space descent map under a factoring-through-$N/p$ hypothesis.
