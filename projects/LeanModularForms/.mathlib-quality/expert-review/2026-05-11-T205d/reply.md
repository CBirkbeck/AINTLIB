# Reviewer reply — 2026-05-11 T205-d brief

*Received 2026-05-11. Verbatim transcript below.*

---

## Assessment

T205-d is still the right near-term critical target, but the current formulation of the remaining "DS Prop 5.5.2(b)" blocker should be corrected before more Lean work is spent on it.

The pointwise Lemma 7.1 as drafted is very likely **not the right identity under the project's slash convention**. With the slash action
$$(f|_k\alpha)(z)=\det(\alpha)^{k-1}(cz+d)^{-k}f(\alpha z),$$
the clean cancellation is obtained with the **adjugate**
$$\alpha^*=\det(\alpha)\alpha^{-1},$$
not with $\alpha^{-1}$. If one insists on using $\alpha^{-1}$, an extra scalar appears. In fact, for $\delta=\det\alpha>0$,
$$(g|_k\alpha^{-1})(\alpha z)=\delta^{2-k}(g|_k\alpha^*)(\alpha z),$$
so the drafted identity with a $\delta^{k-1}$ factor is not consistent with the stated normalization. This is probably why the cancellation is fighting Lean: the target is scalarly misaligned.

The project should pivot from "formalize DS 5.5.2(b) in the raw $\alpha^{-1}$ form" to "formalize the adjugate pointwise kernel identity and derive any $\alpha^{-1}$ version as a scalar corollary if needed." That is the Lean-friendly and mathematically faithful form for the current convention.

The two-step API remains correct in spirit:
1. finite-index fundamental-domain transport — already done;
2. Hecke-correspondence adjoint — still open.

But Step 2 should be stated first as a **determinant/character-free adjugate correspondence identity**:
$$\langle T_{\Gamma\alpha\Gamma} f,g\rangle_\Gamma = \langle f,T_{\Gamma\alpha^*\Gamma}g\rangle_\Gamma,$$
with determinant and diamond/character corrections postponed to the specialization identifying $\Gamma_1(N)\alpha^*\Gamma_1(N)$ with the explicit diamond-shifted $T_p$.

Layers 5–8 of the old 8-layer chain should be retired from the active proof path. Keep the triple-product identity, the $\sigma_p$-style bookkeeping, and any genuinely reusable iUnion/FD lemmas, but do not continue the "M∞ stockpile" or branch-closure route. It is pushing the proof toward a more complicated version of the same adjugate change-of-variables identity.

Alternative routes through Atkin–Lehner–Li orthogonality or $U_p$-eigenspace decompositions are not a better way to prove the good-prime adjoint. They either depend on comparable adjoint/trace identities or solve a different bad-prime problem. The direct adjugate/Petersson correspondence proof is still the cleanest path.

## Mathematical idea

Let
$$\alpha=\begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad \delta=\det\alpha>0,\qquad j(\alpha,z)=cz+d,$$
and let
$$\alpha^*=\delta\alpha^{-1}=\begin{pmatrix}d&-b\\-c&a\end{pmatrix}.$$

Two elementary identities drive the whole proof:
$$\operatorname{Im}(\alpha z)=\frac{\delta\operatorname{Im}z}{|j(\alpha,z)|^2}$$
and
$$j(\alpha^*,\alpha z)=\frac{\delta}{j(\alpha,z)}.$$

Then
$$(g|_k\alpha^*)(\alpha z)=\delta^{k-1}\left(\frac{\delta}{j(\alpha,z)}\right)^{-k}g(z)=\delta^{-1}j(\alpha,z)^k g(z).$$

Taking conjugates and multiplying by $\operatorname{Im}(\alpha z)^k$:
$$\overline{(g|_k\alpha^*)(\alpha z)}\operatorname{Im}(\alpha z)^k = \delta^{-1}\overline{j(\alpha,z)}^k\overline{g(z)} \cdot \frac{\delta^k\operatorname{Im}(z)^k}{j(\alpha,z)^k\overline{j(\alpha,z)}^k} = \delta^{k-1}j(\alpha,z)^{-k}\overline{g(z)}\operatorname{Im}(z)^k.$$

Therefore the clean pointwise identity is
$$f(\alpha z)\overline{(g|_k\alpha^*)(\alpha z)}\operatorname{Im}(\alpha z)^k = (f|_k\alpha)(z)\overline{g(z)}\operatorname{Im}(z)^k.$$

This has **no extra determinant factor**.

If one instead uses $\alpha^{-1}$:
$$(g|_k\alpha^{-1})(\alpha z) = \delta^{1-k}j(\alpha,z)^k g(z),$$
so
$$f(\alpha z)\overline{(g|_k\alpha^{-1})(\alpha z)}\operatorname{Im}(\alpha z)^k = \delta^{2-k}(f|_k\alpha)(z)\overline{g(z)}\operatorname{Im}(z)^k.$$

Thus the raw $\alpha^{-1}$ formulation must carry a $\delta^{2-k}$ factor under the stated convention. A $\delta^{k-1}$ factor belongs to a different slash normalization or a differently normalized operator.

After the pointwise identity is proved, integration is conceptually straightforward:
- integrate over a measurable domain $D$;
- change variables by the Möbius action of $\alpha$;
- use hyperbolic-measure invariance;
- transport the domain from a $\Gamma$-fundamental domain to an $\alpha^{-1}\Gamma\alpha$- or intersection-subgroup fundamental domain using the finite-index FD-transport theorem already proved.

The Hecke-correspondence identity is then the finite-sum version over double-coset representatives. The specialization to $T_p$ is the algebraic identification of the adjugate double coset with the explicit diamond-shifted $T_p$.

## Lean-facing next steps

The next work should be split into theorem-level tickets, not into more "8-layer" local reductions.

**First ticket** (illustrative name `peterssonKernel_slash_adjoint_pointwise_adjugate`):
The pointwise identity expressing
$$f(\alpha z)\overline{(g|_k\alpha^*)(\alpha z)}\operatorname{Im}(\alpha z)^k = (f|_k\alpha)(z)\overline{g(z)}\operatorname{Im}(z)^k.$$

Do **not** target the current Lemma 7.1 with $\alpha^{-1}$ and a $\det(\alpha)^{k-1}$ factor. If the worker needs an $\alpha^{-1}$ version, prove it later as a corollary with the scalar $\det(\alpha)^{2-k}$.

This ticket should factor out the two matrix identities as tiny private lemmas:
- `j_peterssonAdj_smul`: $j(\alpha^*,\alpha z) = \det\alpha / j(\alpha,z)$
- `im_smul_eq_det_div_normSq`: $(\alpha z).\mathrm{im} = \det\alpha \cdot z.\mathrm{im} / \|j(\alpha,z)\|^2$

Then prove one cancellation lemma packaging the complex norm algebra:
- `conj_slash_peterssonAdj_times_im_smul_pow`: $\overline{(g|_k \alpha^*)(\alpha z)} \cdot (\alpha z).\mathrm{im}^k = \det\alpha^{k-1} \cdot j(\alpha,z)^{-k} \cdot \overline{g(z)} \cdot z.\mathrm{im}^k$

The goal is to prevent Lean from repeatedly rediscovering $|j|^{2k}=j^k\overline{j}^k$.

**Second ticket** (illustrative name `peterssonIntegral_slash_adjoint_smul_domain`):
$$\int_D \mathrm{kernel}_k(f|_k\alpha, g)(z)\, d\mu = \int_{\alpha\cdot D} \mathrm{kernel}_k(f, g|_k\alpha^*)(z)\, d\mu.$$

This should consume the pointwise identity plus the already available hyperbolic measure-preserving/change-of-variables theorem. If the project already has `peterssonInner_slash_adjoint` or a domain-level version of DS 5.5.2(a), inspect whether it already proves this ticket. If so, do not reprove the pointwise identity at full generality; specialize and reuse the existing theorem.

**Third ticket** (illustrative name `petN_doubleCoset_adjoint_adjugate`):
$$\mathrm{petN}\left(\sum_{r\in R} f|_k r, g\right) = \mathrm{petN}\left(f, \sum_{r\in R^*} g|_k r\right)$$
where $R$ represents $\Gamma\backslash\Gamma\alpha\Gamma$ and $R^*$ represents $\Gamma\backslash\Gamma\alpha^*\Gamma$.

This is the real Step 2. It should consume:
- finite-index FD transport;
- domain-level slash adjoint;
- finite-sum linearity;
- integrability preservation for cusp forms under slash by Hecke representatives.

State this first without character/determinant correction. Character and determinant bookkeeping should not appear here unless the code's Hecke operator is normalized in a way not described in the brief.

**Fourth ticket** (illustrative name `petN_heckeT_p_diamond_shift_core`):
$$\mathrm{petN}(T_p f, g) = \mathrm{petN}(\langle p \rangle^{-1}\,f \text{ or } g, T_p g)$$
(use the exact project target orientation).

This ticket handles only the specialization:
- $\alpha = \mathrm{diag}(1,p)$;
- $\alpha^* = \mathrm{diag}(p,1)$;
- identify the adjugate-side double-coset operator with the explicit diamond-shifted $T_p$;
- use the triple-product identity and diamond unitarity.

This step is **not "purely mechanical."** It has real bookkeeping: $\mathrm{diag}(p,1)$ is not the same $\Gamma_1(N)$-double coset as $\mathrm{diag}(1,p)$, and central scalar matrices are not slash-trivial under the project convention. Organize it through the diamond operator/coset action of $p \in (\mathbb{Z}/N)^\times$, not by pretending the two $\Gamma_1$ double cosets are equal.

Layers 5–8 of the old chain should be parked. Keep only:
- triple-product identity;
- $\sigma_p$ or diamond-coset permutation lemmas needed for Step 3;
- reusable FD/iUnion lemmas from Step 1.

Everything else should be removed from the active proof plan.

## Risks or missing facts

1. **Scalar mismatch**: Under the slash convention in the brief, the raw $\alpha^{-1}$ DS(b)-style identity carries a $\det(\alpha)^{2-k}$ factor, not $\det(\alpha)^{k-1}$. The worker should verify the code's slash convention and switch to the adjugate identity.

2. **Group orientation**: Confusing $\alpha^{-1}\Gamma\alpha$, $\alpha\Gamma\alpha^{-1}$, and the intersection subgroup. The FD transport theorem must match the orientation of the double-coset representatives used in the Hecke operator. A wrong orientation can still look plausible but will give the wrong transversal and the wrong number of tiles.

3. **Index $p+1$ vs $p$**: For the usual intersection with $\Gamma_1(N)$ and $p\nmid N$, the relevant Hecke degree is $p+1$. Some upper-only $U_p$-style subgroup quotients have size $p$, but the full good-prime $T_p$ correspondence has $p+1$ representatives. The worker should check that the subgroup in `Gamma_p_α_PSL_R_FD_finite_index_decomp_auto` matches the full double-coset degree used in $T_p$.

4. **Central scalar action**: With this slash convention, a scalar matrix $\lambda I$ acts by $\lambda^{k-2}$, not trivially. Any Step 3 proof that identifies $\mathrm{diag}(p,1)$ with a scalar multiple of $\mathrm{diag}(1,p)$ must track that scalar or avoid it by using the diamond/coset formulation.

5. **Over-generalisation**: The project only needs $\Gamma_1(N)$, $\alpha \in \Delta_0(N)$, and then $\alpha = \mathrm{diag}(1,p)$. A fully general congruence-subgroup theorem is elegant but may cost hundreds of extra lines. Prove the narrow theorem first.

6. **Alternative routes are not free**: Atkin–Lehner–Li orthogonality normally depends on the same adjoint/trace structure. $U_p$-decomposition is a bad-prime tool and does not prove the good-prime DS 5.5.3 adjoint needed here.

**Scale estimate (revised)**: If the worker uses $\alpha^*$ and reuses the already proved single-slash adjoint theorem, the new pointwise algebra should be much smaller, perhaps **150–300 LOC**, with another few hundred lines for the aggregate correspondence and $T_p$ specialization. The painful parts will be coercions between rational/real matrices, power exponents, and matching the project's existing slash-action API, not the mathematical cancellation itself.

## Manager message to worker

Stop targeting DS Prop 5.5.2(b) in the raw $\alpha^{-1}$ form. Under our slash convention, that identity has the wrong scalar if stated as in the brief. The clean target is the adjugate identity with $\alpha^* = \det(\alpha)\alpha^{-1}$.

Next ticket should be `peterssonKernel_slash_adjoint_pointwise_adjugate`.

Prove the pointwise identity
$$f(\alpha z)\overline{(g|_k\alpha^*)(\alpha z)}\operatorname{Im}(\alpha z)^k = (f|_k\alpha)(z)\overline{g(z)}\operatorname{Im}(z)^k.$$

Do not put any extra determinant factor in this statement. The determinant and character corrections appear later only when identifying the adjugate double-coset operator with the explicit diamond-shifted $T_p$.

Break the proof into three private lemmas:
1. $j(\alpha^*,\alpha z) = \det\alpha / j(\alpha,z)$;
2. $\operatorname{Im}(\alpha z) = \det\alpha \cdot \operatorname{Im}(z) / |j(\alpha,z)|^2$;
3. the complex cancellation lemma combining the conjugate slash factor with the transformed $y^k$.

After the pointwise lemma, prove or reuse the domain-level integrated version. If an existing `peterssonInner_slash_adjoint` theorem already states this with $\alpha^*$, use it instead of reproving the pointwise calculation.

Then prove the actual Step 2 theorem as an adjugate double-coset correspondence:
$$\mathrm{petN}(T_{\Gamma\alpha\Gamma} f, g) = \mathrm{petN}(f, T_{\Gamma\alpha^*\Gamma} g).$$

This Step 2 theorem should be determinant/character-free unless the code's Hecke operator has an additional normalization not described in the brief.

Finally specialize to $\alpha = \mathrm{diag}(1,p)$. This is not just automatic simplification: $\mathrm{diag}(p,1)$ is not the same $\Gamma_1(N)$-double coset as $\mathrm{diag}(1,p)$. Use the diamond/coset action of $p \in (\mathbb{Z}/N)^\times$, the triple-product identity, and diamond unitarity to identify the adjugate-side correspondence with the target $\langle p\rangle^{-1}T_p$.

Park Layers 5–8 of the old 8-layer chain. Keep only the triple-product identity, the $\sigma_p$/diamond permutation lemmas needed for specialization, and reusable FD/iUnion lemmas. Do not continue the M∞ stockpile or branch-closure route.

Also verify the index/orientation of `Gamma_p_α`: for the full good-prime $T_p$ correspondence the relevant degree is $p+1$, not $p$. If the FD-transport theorem is using a $p$-element upper-only quotient, it is not the right subgroup for the full $T_p$ adjoint.
