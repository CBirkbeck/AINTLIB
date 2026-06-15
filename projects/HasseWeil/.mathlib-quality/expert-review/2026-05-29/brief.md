# Review brief (round 7) — Hasse bound: is the dual-isogeny machinery necessary, or is there a leaner route?

*Prepared 2026-05-29 for the same arithmetic-geometry reviewer as rounds 1–6. Self-contained; no repository access required.*

*Central question this round: **the whole Hasse bound now reduces (by a sorry-free assembly) to two open leaves, and the deep one forces us to build dual isogenies of general endomorphisms from scratch (mathlib has none). Do we actually need that, or is a different proof of Hasse — e.g. Stepanov's elementary method — substantially cheaper to formalise?***

---

## 1. Goal

Prove, fully formally (Lean 4 / mathlib), the **Hasse bound** for an elliptic curve $E$ over a finite field $K = \mathbb{F}_q$:
$$\bigl|\,\#E(\mathbb{F}_q) - q - 1\,\bigr| \;\le\; 2\sqrt{q},$$
unconditionally and uniformly in the characteristic (including $p = 2, 3$ and the supersingular cases).

The bound is already reduced, by a **sorry-free assembly theorem**, to exactly **two** open mathematical leaves (§3, §5, §6). This round asks whether those leaves — especially the deepest one — are the right effort target, or whether a different proof discharges the goal far more cheaply.

---

## 2. Background, conventions, references

### 2.1 Setting and notation

- $K = \mathbb{F}_q$, $q = p^n$, $p = \operatorname{char} K$. $E/K$ an elliptic curve in Weierstrass form; $K(E)$ its function field; $\omega$ the invariant differential.
- $\pi \in \operatorname{End}(E)$ is the **$q$-power Frobenius**; its function-field comorphism is $\pi^*: f \mapsto f^{\,q}$.
- For $\alpha \in \operatorname{End}(E)$, $\deg \alpha := [K(E) : \alpha^* K(E)]$; for $\alpha = [m]$, $\deg[m] = m^2$.
- $\#E(\mathbb{F}_q)$ = number of $K$-rational points (affine points plus $O$).
- $t := 1 + \deg\pi - \deg(1-\pi) = 1 + q - \deg(1-\pi)$ (the "trace").

### 2.2 References

- **[Silverman]** J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009. We follow its Hasse proof **V.1.1**; supporting machinery is **III.4** (isogeny degree, separability, $\#\ker$), **III.5** (Frobenius, differentials, II.4.2(c)), **III.6** (dual isogeny; degree as a positive-definite quadratic form, **III.6.3**), **VII.2** (formal group; kernel of reduction is a subgroup).
- **[Bombieri 1973]** E. Bombieri, "Counting points on curves over finite fields (d'après S. A. Stepanov)," *Séminaire Bourbaki* 1972/73, exp. 430.
- **[Schmidt 1976]** W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, LNM 536, Springer.
- **[Washington]** L. C. Washington, *Elliptic Curves: Number Theory and Cryptography*, 2nd ed., CRC.
- **[mathlib]** State of the relevant API (verified 2026-05-29): mathlib's elliptic-curve library has Weierstrass models, variable changes, coefficient reduction, **division polynomials** $\psi_n$ with their **degrees**, and the affine/projective/Jacobian point groups — **but no isogenies, no dual isogeny, no degree map on endomorphisms, no formal-group point theory, and no Hasse bound.** Everything at the isogeny level is project-built.

### 2.3 State of the art

Hasse's theorem has several independent proofs: (i) Silverman V.1.1 (degree is a positive-definite quadratic form on $\operatorname{End}(E)$, via dual isogenies); (ii) eigenvalues of Frobenius on the Tate module / Weil pairing; (iii) Weil's intersection theory on $E\times E$; (iv) **Stepanov's elementary polynomial method** (Bombieri/Schmidt): proves $|\#C(\mathbb{F}_q) - q - 1| \le 2g\sqrt q$ for a smooth curve of genus $g$ using only the function field, Frobenius, and Riemann–Roch / explicit pole-order bounds — no isogenies, no cohomology. None of these is formalised in mathlib. The project committed early to route (i).

---

## 3. Current strategy and where it stands

Silverman **V.1.1**:

1. $\#E(\mathbb{F}_q) = \deg(1-\pi)$.  *(Leaf 2, §5.)*
2. $\deg(r\pi - s) = q\,r^2 - t\,r s + s^2$ for all $r,s\in\mathbb{Z}$, and being a degree it is $\ge 0$ — i.e. $\deg$ is a positive-definite quadratic form.  *(Leaf 1, §6.)*
3. Non-negativity of that binary form for all integers $(r,s)$ forces $t^2 - 4q \le 0$, i.e. $|t|\le 2\sqrt q$; with (1), $|\#E(\mathbb{F}_q) - q - 1| = |t| \le 2\sqrt q$.

**Status.** One Lean theorem assembles the bound with a **sorry-free body** from precisely two open inputs:

- **Leaf 1** (Silverman III.6.3): $\;0 \le q\,r^2 - t\,r s + s^2$ for all $r,s\in\mathbb{Z}$.
- **Leaf 2** (Silverman V.1.1 / III.4.10): $\;\deg(1-\pi) = \#E(\mathbb{F}_q)$.

Step (3) — discriminant $\Rightarrow$ bound — is **done, axiom-clean**. So the whole problem is the two leaves, and essentially **all the difficulty is in Leaf 1**.

---

## 4. What is already proved (reusable assets — all axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`)

1. **Frobenius and its degree.** $\pi$ as an isogeny; $\pi^* f = f^q$; $\deg\pi = q$ (from $[K(E):K(E)^q] = q$).
2. **Verschiebung = dual of Frobenius exists.** $\exists\, V \in \operatorname{End}(E)$, $V\pi = \pi V = [q]$ — uniform in $p$, via "$q$-th root surjectivity" ($[q]^*$ lands in $K(E)^q = \operatorname{im}\pi^*$, so $[q]$ factors through $\pi$). *This is the dual of $\pi$ specifically.*
3. **Separability $\Leftrightarrow$ differential criterion (II.4.2(c)) — just completed.** For any $\alpha$: $\alpha$ separable $\iff$ $\alpha^*:\Omega_{K(E)/K}\to\Omega_{K(E)/K}$ injective $\iff a_\alpha \ne 0$, where $\alpha^*\omega = a_\alpha\omega$ ($\Omega$ is $1$-dim over $K(E)$). The finiteness side condition is discharged unconditionally by a transcendence-degree argument.
4. **$1-\pi$ is separable**, $a_{1-\pi}=1$ (since $(1-\pi)^*\omega = \omega - \pi^*\omega = \omega - 0 = \omega$).
5. **$\#\ker(1-\pi) = \#E(\mathbb{F}_q)$**, since $\ker(1-\pi) = \{P:\pi P = P\} = E(\mathbb{F}_q)$.
6. **Discriminant wiring**, done: "$q r^2 - t rs + s^2 \ge 0\ \forall r,s$" $\Rightarrow$ "$t^2 \le 4q$" $\Rightarrow$ "$|t|\le 2\sqrt q$".
7. **Place-at-$O$ valuation identity — just completed.** The formal Laurent-expansion order at $O$ equals the norm/$\operatorname{ord}_\infty$ valuation, for all $f\in K(E)$. (Pole-order bookkeeping at $O$.)
8. **$\deg[m]=m^2$, $\operatorname{tr}[m]=2m$, $[q]=V\pi$**, and the III.6.3 identity for *multiplication* maps $\deg[rm-s] = m^2 r^2 - 2m\,rs + s^2$ (done unconditionally).

So Frobenius, its dual, the separability criterion, the rational-point/kernel identification, and the whole algebraic back-end are in hand.

---

## 5. Leaf 2 — $\deg(1-\pi) = \#E(\mathbb{F}_q)$ (the easier leaf)

By assets 4+5, $1-\pi$ is separable and $\#\ker(1-\pi) = \#E(\mathbb{F}_q)$. So Leaf 2 is exactly **Silverman III.4.10(a)** for the single separable isogeny $1-\pi$:
$$\boxed{\;\alpha\text{ separable}\;\Longrightarrow\;\deg\alpha = \#\ker\alpha\;}$$
(a separable isogeny is étale, so its fibres have size = degree). **Not yet formalised.** The project pursued it via a heavy detour — viewing $\deg(1-\pi) = [K(E):(1-\pi)^*K(E)]$ and counting rational points through the **splitting of places** over the pole locus of $(1-\pi)^*x$ (the $\sum e_P f_P = \deg$ fundamental identity plus a "every place over $(x)$ is a kernel place" claim). That detour had a confirmed-**false** sub-route (the divisibility `nReduced_R_div_D_sq`, which round 5 established is false) and is **mid-reformulation** per your "Option I′" guidance. The fundamental-identity and tower steps are done; the missing piece is the place $\leftrightarrow$ rational-point bijection at the pole locus.

**Observation to check:** now that separability of $1-\pi$ is a finished, axiom-clean result, the Sinf/inertia detour may be unnecessary — one might get $\deg = \#\ker$ for separable $1-\pi$ directly (separable $\Rightarrow$ étale $\Rightarrow$ the fibre over $O$, $=\ker$, has $\deg$ geometric points), reusing standard separable-field-extension / fibre-count facts rather than a bespoke ramification computation.

---

## 6. Leaf 1 — non-negativity of the degree quadratic form (the deep leaf)

Need $\;0 \le q r^2 - t rs + s^2\;$ for all $r,s\in\mathbb{Z}$. The Silverman route: this equals $\deg(r\pi - s)$, and degrees are $\ge 0$; so it suffices to realise, for each $(r,s)\neq(0,0)$, an isogeny of degree $q r^2 - t rs + s^2$ — namely $r\pi - s$.

The identity $\deg(r\pi-s) = q r^2 - t rs + s^2$ is Silverman III.6.3, proved from bilinearity of $\langle\phi,\psi\rangle = \deg(\phi+\psi) - \deg\phi - \deg\psi$, which Silverman gets from **dual isogenies**: $\deg\phi = \hat\phi\phi$ and $\widehat{\phi+\psi} = \hat\phi+\hat\psi$.

**Where we are stuck.** We have the dual of *Frobenius* (asset 2) but **not the dual of a general endomorphism** like $r\pi - s$. The open leaf asks for a genuine $\beta_{\mathrm{dual}}$ with $\beta_{\mathrm{dual}}\circ(r\pi-s) = [\,q r^2 - t rs + s^2\,]$ **as a full morphism (comorphism included)**. Building $r\pi-s$ and its dual as honest isogenies requires either:

- **Silverman III.6.1** (dual of an arbitrary isogeny — via $E/\ker$, or via $\operatorname{Pic}^0$); **or**
- a direct addition-formula construction of $rV - s$ whose well-definedness needs a **pole-order bound at $O$** that is the **Silverman VII.2** "kernel of reduction is a subgroup" content (the addition formula alone cannot resolve the order: the two summands' $x$-coordinates have equal pole orders and the leading terms can cancel — only the subgroup property forces the sum's $x$ to have a pole).

Neither is in mathlib; each is a multi-week from-scratch development by mathlib standards. The characteristic-divisible sub-cases ($p\mid r$ or $p\mid s$, supersingular) need the inseparable factorisation $[p]=V\pi$ and the same bilinearity.

**Crux:** positive-definiteness of the degree form is the single deep obstruction, and via Silverman it forces dual isogenies of general endomorphisms. Is that genuinely necessary?

---

## 7. A systemic modelling issue (soundness footnote, relevant to Q3/Q4)

Our isogeny type bundles a function-field comorphism (algebra hom) and a point-map (group hom) as **independent fields with no enforced compatibility and no basepoint-preservation constraint**. This has twice produced *false-as-stated* lemmas (a separability claim for $[p]$ that fails in the supersingular case; a pole-order claim that fails because a translation's comorphism is an admissible "isogeny" in this type), beyond an earlier "placeholder" class (now purged) that paired a correct point-map with a fake comorphism and thereby made false degree statements provable. We can fix this structurally (add a basepoint/compatibility constraint, or use the compatible isogeny type the project also has), but it is a core-type refactor mid-proof.

---

## 8. Where we're stuck — summary

- **Stuck 8.1 (Leaf 1, deep).** Positive-definiteness of the degree form $\Rightarrow$ dual isogenies of *general* endomorphisms (Silverman III.6.1 / VII.2). The Frobenius dual alone is insufficient; mathlib provides nothing here.
- **Stuck 8.2 (Leaf 2, moderate).** $\deg(1-\pi) = \#E(\mathbb{F}_q)$, i.e. Silverman III.4.10(a) for the (proven) separable $1-\pi$; pursued via a heavy places/ramification route, mid-reformulation; likely admits a much shorter separable-étale route.

---

## 9. Questions for the reviewer

**Q1 (headline — is a leaner proof the better target?).** Our route's deep obstruction is constructing dual isogenies of general endomorphisms (III.6.1/VII.2), and mathlib has *no* isogeny/dual/formal-group infrastructure. Would a **different proof of Hasse be substantially cheaper to formalise**? Specifically, is **Stepanov's elementary method** (Bombieri/Schmidt — auxiliary polynomial + pole-order/Riemann–Roch estimates on $K(E)$, no isogenies, no quadratic form on $\operatorname{End}E$) realistic here, given that we already have $K(E)$, the Frobenius comorphism $f\mapsto f^q$, division polynomials, and pole-order/valuation bookkeeping at $O$ (assets 1, 7, 8)? If you favour Stepanov: which reference and which key estimate to target first, and what pitfalls (the genus-1 auxiliary-polynomial / derivative step; small-characteristic derivative degeneracies) should we anticipate? Conversely, is there a reason Stepanov is a *worse* formalisation target than it looks?

**Q2 (if we keep the current route — is the general dual really unavoidable?).** Silverman gets bilinearity of $\langle\phi,\psi\rangle$ from duals. Is there a path to "$q r^2 - t rs + s^2 \ge 0\ \forall r,s$" that avoids the dual of each $r\pi-s$ — e.g. needing only (a) the **parallelogram law** $\deg(\phi+\psi)+\deg(\phi-\psi)=2\deg\phi+2\deg\psi$ (making $\deg$ a quadratic form), plus (b) one non-degeneracy input — where (a) might follow from a more primitive additivity fact than full duality? In particular: **can the whole quadratic form be pinned down from just $\{1,\pi,V\}$ and the relations $V\pi=[q]$, $\pi+V=[t]$** (all of which we have, asset 2/8), rather than from duals of all $r\pi-s$? (E.g., is $\deg(r\pi-s) = (r\pi-s)\widehat{(r\pi-s)} = (r\pi-s)(rV-s)$ computable directly from $V\pi=[q]$ and $\pi+V=[t]$ once one knows $\widehat{r\pi-s} = rV - s$ — and is *that* dual identity cheaper than a general III.6.1?)

**Q3 (Leaf 2 shortcut).** With $1-\pi$ proven separable, what is the cleanest route to $\deg(1-\pi)=\#\ker(1-\pi)$ (III.4.10(a)) — the separable$\Rightarrow$étale fibre count via standard separable-field-extension theory (number of embeddings into $\overline K$ fixing the subfield, or the trace form), without the bespoke ramification-over-places machinery we built?

**Q4 (modelling).** Worth re-modelling isogenies with a built-in basepoint/comorphism-compatibility constraint (§7) to kill the false-statement class at the type level, or is carrying explicit "genuine isogeny" hypotheses per lemma the pragmatic choice this late?

**Q5 (meta / leverage).** Of the §4 assets, which survive a switch to Stepanov (Q1) or a leaner quadratic-form argument (Q2)? We want the route that strands the least finished work — without committing further to a multi-week dual-isogeny build if an elementary route reaches the bound first.

---

## 10. Document metadata

- Project: formal Hasse bound for elliptic curves over finite fields (Lean 4 / mathlib).
- Build status: compiles cleanly; the Hasse bound is assembled by a sorry-free skeleton from the two open leaves of §3; ~48 `sorry`s remain across the supporting development, concentrated in the Leaf-1 (quadratic-form/dual) and Leaf-2 (V.1.3) machinery.
- Recent context (round 7): completed an axiom-clean separability⟺differential criterion (II.4.2(c)) and the place-at-$O$ valuation identity; purged a class of unsound "placeholder" isogenies; surfaced two false-as-stated lemmas (both from the §7 modelling issue) and replaced them with true, hypothesis-explicit forms.
- Prepared 2026-05-29.
