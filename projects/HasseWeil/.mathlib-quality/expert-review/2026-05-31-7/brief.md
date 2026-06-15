# Review brief (round 19) — Route 2A is reduced and its foundations are built; three geometric sub-dependencies remain (one of which kills the naive "[ℓ] is finite" device). Where should the remaining effort go?

*Prepared 2026-05-31 for the same senior arithmetic-geometry reviewer as rounds 1–18. Self-contained; no repository access required. Following your round-18 endorsement of Route 2A (the finite-level Weil-pairing route with the separable-factorisation + discriminant refinement), we built the axiom-clean reduction and most of the geometric foundations. In doing so we hit three genuine sub-dependencies; this brief reports them precisely and asks four questions, one strategic.*

---

## 1. Goal

Formalise the Hasse bound for an elliptic curve $E$ over a finite field $\mathbb{F}_q$ (characteristic $p$):
$$\bigl|\,\#E(\mathbb{F}_q) - q - 1\,\bigr| \le 2\sqrt{q}.$$
Writing $\pi \in \operatorname{End}(E)$ for the $q$-power Frobenius and $t := q + 1 - \#E(\mathbb{F}_q)$ for its trace, the entire bound has been reduced (axiom-cleanly, see §5) to the single statement
$$\textbf{(qf\_nonneg)}\qquad 0 \le q r^2 - t\,r s + s^2 \quad\text{for all } (r,s)\in\mathbb{Z}^2,$$
equivalently $t^2 \le 4q$ (the discriminant of the form is $t^2 - 4q$).

## 2. Background and references

### 2.1 Setting and conventions
- $E/\mathbb{F}_q$ smooth Weierstrass curve, $O$ the point at infinity; $\overline{\mathbb F}_q$ a fixed algebraic closure; $K(E)$ the function field; $R = \mathbb{F}_q[x,y]/(W)$ the **affine** coordinate ring (so $\operatorname{Spec} R = E \smallsetminus \{O\}$, and $K(E) = \operatorname{Frac} R$).
- $\pi$ = $q$-power Frobenius endomorphism; on points $\pi(P) = P^{(q)}$. Quadratic relation $\pi^2 - t\pi + q = 0$ in $\operatorname{End}(E)$, with $\deg\pi = q$ and $\deg(1-\pi) = \#E(\mathbb{F}_q)$.
- For a nonzero isogeny $\varphi$, $\deg\varphi = [K(E) : \varphi^* K(E)]$; $\deg_s\varphi$ its separable degree; $\hat\varphi$ its dual, $\hat\varphi\varphi = [\deg\varphi]$.
- $E[\ell] = \ker[\ell]$ the $\ell$-torsion; for $\ell \ne p$, $E[\ell] \cong (\mathbb{Z}/\ell)^2$ over $\overline{\mathbb F}_q$.

### 2.2 References
- **[Silverman]** J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009. Specifically III.5.5 ($m+n\varphi$ separable $\iff p \nmid m$), III.4.10 (separable $\Rightarrow \#$fibre $=\deg$), III.6.1–6.3 (degree as a quadratic form; dual), III.8.1–8.6 (the Weil pairing $e_\ell$, its properties, and $\det = \deg$), V.1.1/V.2.3.1 (Hasse, finite-field proof).
- Round 17–18 of this correspondence (your endorsements of, respectively, the finite-level pairing route and Route 2A).

### 2.3 State of the art
The Hasse bound is classical; the point of interest is a *constructive, characteristic-uniform* formalisation. mathlib has no Weil pairing on elliptic curves, no $\det=\deg$ representation theorem, and no elliptic-curve torsion-cardinality theorem; all of this is being built here.

## 3. Strategy (Route 2A, as endorsed round 18)

The classical "degree is a positive-definite quadratic form" (Silverman III.6.3) gives **(qf\_nonneg)** immediately from $\deg(r\pi - s) = q r^2 - t r s + s^2 \ge 0$, but its proof uses dual **additivity** $\widehat{(\varphi+\psi)} = \hat\varphi + \hat\psi$ (III.6.2c), which stalls in characteristic $p$ (Route 1). Route 2A avoids additivity:

1. For each prime $\ell \ne p$, $\operatorname{End}(E)$ acts on $E[\ell]\cong(\mathbb{Z}/\ell)^2$, giving $\rho_\ell : \operatorname{End}(E) \to M_2(\mathbb{Z}/\ell)$.
2. **(Silverman III.8.6)** $\det \rho_\ell(\varphi) \equiv \deg\varphi \pmod \ell$ for every $\varphi$. The proof uses only the **scaling identity** $e_\ell(\varphi v_1, \varphi v_2) = e_\ell(v_1, v_2)^{\deg\varphi}$, which follows from single-isogeny facts ($\hat\varphi\varphi=[\deg\varphi]$, the adjoint III.8.2, $\hat{\hat\varphi}=\varphi$) — **no additivity**.
3. Apply to $\varphi = r\pi - s$: with $M := \rho_\ell(\pi)$, one gets $\det M \equiv q$, $\operatorname{tr} M \equiv t$ (the latter via $\det(1-M) \equiv \deg(1-\pi) = \#E$ and $\operatorname{tr} = 1 + \det M - \det(1-M)$), so the $2\times2$ identity gives $\det(rM - sI) = q r^2 - t r s + s^2$. Hence $\deg(r\pi-s) \equiv q r^2 - t r s + s^2 \pmod\ell$ for **all** $\ell \ne p$, forcing equality in $\mathbb{Z}$.
4. The sign ($\deg \ge 0$) is free, so **(qf\_nonneg)** holds whenever $r\pi - s$ is a genuine isogeny. For $p \mid s$ the discriminant trick (Silverman, p.\ coprime denominators: nonnegativity on $\{p\nmid s\}$ already forces $t^2 \le 4q$, hence nonnegativity everywhere) closes the remaining cases — so only **separable** $r\pi-s$ (i.e. $p \nmid s$, by III.5.5) is ever needed.

## 4. Definitions (self-contained)

**Definition 4.1 (the Frobenius matrix datum).** For $\varphi \in \operatorname{End}(E)$ and $\ell \ne p$, a matrix $M \in M_2(\mathbb{Z}/\ell)$ is a *symplectic-scaling datum for $\varphi$* if $M^{\mathsf T} J M = (\deg\varphi)\, J$ where $J = \left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. For such $M$, $\det M = \deg\varphi$ in $\mathbb{Z}/\ell$ (the abstract content of III.8.6).

**Definition 4.2 (the Weil pairing, III.8.1).** For $T \in E[\ell]$ pick $f_T \in K(E)$ with $\operatorname{div} f_T = \ell(T) - \ell(O)$ (exists: degree $0$, sums to $O$, Abel–Jacobi) and $g_T$ with $\operatorname{div} g_T = [\ell]^*(T) - [\ell]^*(O) = \sum_{R\in E[\ell]} (T' + R) - \sum_{R\in E[\ell]}(R)$ (where $\ell T' = T$), normalised so $f_T \circ [\ell] = g_T^{\,\ell}$. Then for any $X$ with $g_T(X) \ne 0,\infty$,
$$e_\ell(S, T) := \frac{g_T(X + S)}{g_T(X)} \in \mu_\ell,$$
a constant independent of $X$ (because translating $X$ by $S \in E[\ell]$ permutes the fibre divisor $\operatorname{div} g_T$, so the ratio has trivial divisor on a complete curve, hence is a constant root of unity).

**Definition 4.3 (the geometric divisor pullback).** For a nonzero isogeny $\varphi$ and $Q \in E$, $\varphi^*(Q) := \sum_{\varphi P = Q} e_\varphi(P)\,(P)$; for **separable** $\varphi$ this is multiplicity-free ($e_\varphi = 1$), the étale fibre sum.

## 5. Established results (axiom-clean; built since round 18)

All of the following compile with no `sorry` and on mathlib's standard axioms only.

**Theorem 5.1 (the reduction — Hasse $\Leftarrow$ scaling data).** Suppose that for every $(r,s)$ with $p \nmid s$ and every prime $\ell \ne p$ there exist symplectic-scaling data over $\mathbb{Z}/\ell$ for $\pi$, for $1-\pi$, and for $r\pi - s$, realising $\deg = q$, $\#E$, and $qr^2 - trs + s^2$ respectively. Then **(qf\_nonneg)** holds, hence the Hasse bound.
*Sketch.* The three scalings give $\det M = q$, $\det(1-M) = \#E$ (so $\operatorname{tr} M = t$), $\det(rM - sI) = qr^2-trs+s^2$ in $\mathbb{Z}/\ell$; but $\det(rM-sI)$ also $=\deg(r\pi-s)$, an integer; congruence mod all $\ell\ne p$ forces the integer equality; nonnegativity is free; the discriminant trick extends from $\{p\nmid s\}$ to all $(r,s)$. ∎ This is the abstract heart of III.8.6 + V.2.3.1, fully formalised.

**Theorem 5.2 (degree = quadratic form, mod $\ell$, abstract).** A symplectic-scaling datum $M$ for $\varphi$ has $\det M = \deg\varphi$ in $\mathbb{Z}/\ell$ (both the matrix and the module/alternating-form versions of III.8.6 are formalised).

**Theorem 5.3 (Leaf 2, closed).** $\deg(1 - \pi) = \#E(\mathbb{F}_q)$. *Sketch.* $\ker(1-\pi)$ = the $\pi$-fixed points = $E(\mathbb{F}_q)$; combined with a separable-degree/ramification identity at the point at infinity. ∎

**Theorem 5.4 (the divisor foundation).** (a) $f_T$ exists for $T\in E[\ell]$ (Abel–Jacobi via $\operatorname{Pic}^0 E \cong E$, characteristic-uniform). (b) The geometric pullback $\varphi^*(Q) = \sum_{\varphi P = Q}(P)$ is defined, with $\deg \varphi^*(Q) = \#\ker\varphi$ and the group-sum ("$\sigma$") section $\sigma(\varphi^*(Q) - \varphi^*(O)) = \#\ker\varphi \cdot P_0$ (III.6.1b). (c) $g_T$ exists once $\#E[\ell] \cdot P_0 = O$.

**Theorem 5.5 (the pairing value layer).** Over $\overline{\mathbb F}_q$, a function with trivial divisor is a nonzero constant; hence $e_\ell(S,T)$ is a well-defined constant, $e_\ell(S,T)^\ell = 1$, $e_\ell(\cdot,T)$ is multiplicative ($c_{12}=c_1c_2$), and $e_\ell(O,T)=1$ — all **parametric on a single "translation-invariance witness"** $\operatorname{div}(g\circ\tau_S) = \operatorname{div}(g)$ for $S\in E[\ell]$.

**Theorem 5.6 ($[\ell]$ separable).** For $\ell \ne p$, $[\ell]$ is a finite separable isogeny. *Sketch.* $[\ell]^*\omega = \ell\,\omega \ne 0$ (formal-group / invariant-differential route, no division-polynomial Wronskian), and "$\psi^*\omega \ne 0 \Rightarrow$ separable" (II.4.2c). ∎

## 6. In progress / 7. Targets

The reduction (5.1) consumes, per $\ell\ne p$, three symplectic-scaling data. Producing them is the Weil-pairing construction, in tickets: `PAIRING-DEF` (the $e_\ell$ of 4.2, tying 5.4–5.5 to $E[\ell]$), `PAIRING-PROPS` (bilinear/alternating/nondegenerate, III.8.1), `ADJOINT` (III.8.2), `DET-DEG` (III.8.6, assembling 5.2 + props + adjoint), and `ASSEMBLE`. Each rests on one of the three sub-dependencies in §8. Torsion is currently carried **parametrically**: a general lemma gives $\#E[\ell] = \ell^2$ from $[\ell]$-separability + finite-dimensionality + **a fibre witness** "$\#\{P : [\ell]P = [\ell]P_0\} = \deg_s[\ell]$", which is the unproven input.

## 8. Where we're stuck (the three sub-dependencies)

**8.1 — $\#E[\ell] = \ell^2$ over $\overline{\mathbb F}_q$, and why the obvious device is impossible.**
We need the fibre witness of §6, i.e. III.4.10c for $[\ell]$: separable $\Rightarrow$ every fibre has $\deg = \ell^2$ points. The project's unconditional fibre-counting machinery requires the morphism to restrict to an $\mathbb{F}_q$-algebra map on **affine coordinate rings**, $\varphi^* : R \to R$ (a "coordinate-ring pullback witness"). **For $[\ell]$ this map provably does not exist:** $[\ell]^* x = \Phi_\ell(x)/\Psi_\ell^2(x)$ is a genuine rational function whose denominator vanishes at the affine $\ell$-torsion, so $[\ell]^* x \notin R$ (and $R \hookrightarrow K(E)$, so nothing in $R$ maps to it). Geometrically, $[\ell]$ does **not** preserve the affine chart $E \smallsetminus \{O\}$ — it maps $E \smallsetminus E[\ell] \to E \smallsetminus \{O\}$, with poles exactly along the fibre $[\ell]^{-1}(O) = E[\ell]$. (Frobenius is the unique isogeny whose coordinate pullback $x \mapsto x^q$ is *polynomial*, hence the only one with such a witness; this is why the closed Leaf 2 used a Frobenius-specific fixed-point count that does **not** generalise to $[\ell]$.) So the affine route is dead, and $\#E[\ell]=\ell^2$ needs a **function-field-level** III.4.10c: separable $[\ell]$ is unramified (étale), so all fibres have $\deg$ points, *without* an affine $R\to R$ map. The project does have unconditional fibre-counting for maps that *do* have a coordinate witness — notably the coordinate map $x : E \to \mathbb{P}^1$ (degree 2, witness = the inclusion $\mathbb{F}_q[x]\hookrightarrow R$) — so one option is to factor $[\ell]$ through such maps (e.g. the induced $x$-line map $x \mapsto \Phi_\ell(x)/\Psi_\ell^2(x)$ of degree $\ell^2$). **(Question 1.)**

**8.2 — The translation-invariance witness / function evaluation.** Theorem 5.5 is parametric on $\operatorname{div}(g\circ\tau_S) = \operatorname{div}(g)$ for $S\in E[\ell]$, and the actual pairing value $g(X+S)/g(X)$ needs *pointwise evaluation* of a function at a point and its translate — infrastructure the function-field layer does not yet have natively. We have the maximal-ideal/valuation transport pieces (translation acts compatibly on the local rings) but have not assembled them into the clean divisor-transport that discharges the witness. This is genuinely new (but, we believe, bounded) infrastructure. **(Touches Question 2.)**

**8.3 — The separable adjoint, III.8.2.** The scaling identity (step 2 of §3) needs $e_\ell(\varphi S, T) = e_\ell(S, \hat\varphi T)$. We have a *Picard* dual `picDual` ($=\sigma\circ\varphi^*$ on divisor classes, sorry-free, with $\mathrm{picDual}\circ\varphi = [\deg\varphi]$), and the $\sigma$-bridge $\hat\varphi T = \sigma(\varphi^*((T))-(O))$ is then automatic by construction; the **genuine isogeny dual** `isogDual` is, by contrast, gated on a large unfinished construction, so we route around it. For separable $\varphi$, Prop 8.2's divisor pullback is multiplicity-free, which should keep this bounded. We want to confirm the cleanest formalisation. **(Question 3.)**

## 9. Questions for the reviewer

**Q1 (cleanest route to $\#E[\ell]=\ell^2$).** Given that the affine "$[\ell]$ is finite" device (a coordinate-ring map $R\to R$) provably cannot exist (§8.1), what is the cleanest constructive route to $\#E[\ell]=\ell^2$ over $\overline{\mathbb F}_q$? Candidates we see: (a) a function-field-level statement that a separable isogeny is unramified and therefore has all fibres of size $\deg$ (the integral closure of $[\ell]^*R$ in $K(E)$ is module-finite, étale); (b) descending to the $x$-line via the degree-$\ell^2$ map $x\mapsto\Phi_\ell/\Psi_\ell^2$, which *does* have a coordinate witness, and counting there; (c) something else entirely (Tate-module, or a direct kernel-as-group-scheme count). Which is least painful to make fully rigorous, and are there pitfalls (wild ramification can't occur since $\ell\ne p$, but are there subtleties at $O$ or at the ramification of the $x$-map)?

**Q2 (is the full pairing the soundest path?).** We are constructing the divisor-theoretic Weil pairing $e_\ell(S,T)=g_T(X+S)/g_T(X)$, which forces the function-evaluation infrastructure of §8.2. Is this the soundest route to $\det\rho_\ell\equiv\deg$, or is there a materially shorter path to **(qf\_nonneg)** that we are missing — e.g. obtaining $\det\rho_\ell(\varphi)\equiv\deg\varphi$ without constructing $e_\ell$ pointwise (a more algebraic/cohomological avatar of the pairing), or even bypassing the pairing and the matrix representation altogether for the specific element $r\pi-s$?

**Q3 (separable adjoint, III.8.2).** What is the cleanest way to formalise $e_\ell(\varphi S,T)=e_\ell(S,\hat\varphi T)$ for separable $\varphi$, given that we have the Picard dual (sorry-free, $\mathrm{picDual}\circ\varphi=[\deg\varphi]$, with the $\sigma$-bridge automatic) but not the genuine isogeny dual? In particular: is it legitimate and clean to run all of Prop 8.6 with `picDual` in the role of $\hat\varphi$ — i.e. does the pairing adjoint genuinely only need the Picard-level dual and the multiplicity-free pullback, never the isogeny dual as a *map*?

**Q4 (strategic — is Route 2A still right?).** We have now hit three genuine geometric sub-dependencies on Route 2A (§8.1 torsion/finite-morphism, §8.2 function evaluation, §8.3 adjoint), each bounded-but-real. The abstract reduction (Th. 5.1) and the divisor foundations (5.4–5.5) are done. Stepping back: is finishing Route 2A still the soundest path to **(qf\_nonneg)**, or — knowing what we now know — would you steer us to (i) Route 1 (degree as a quadratic form via dual additivity, accepting whatever characteristic-$p$ care that needs), (ii) a Tate-module / $\ell$-adic representation packaging that might absorb §8.1–8.3 more uniformly, or (iii) a different decomposition of the endgame? Concretely: of §8.1–8.3, which would you attack first, and is any of them a warning sign that the route is more expensive than it looked at round 18?

## 11. Document metadata
- Project: Hasse bound for elliptic curves over finite fields (constructive, characteristic-uniform), Lean 4 / mathlib.
- Round: 19. Brief generated 2026-05-31.
- Build status: the reduction (Th. 5.1) and the Weil-pairing foundations (Th. 5.2, 5.4, 5.5, 5.6) are axiom-clean; the whole bound is `sorry`-reduced to the three sub-dependencies of §8 (plus the parametric torsion fibre witness). Leaf 2 (5.3) closed.
- Prior context: rounds 17 (endorsed finite-level pairing) and 18 (endorsed Route 2A; confirmed clean machinery gives $\det\equiv N$, the sign needs the separable adjoint).
