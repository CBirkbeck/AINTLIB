# Reviewer reply — 2026-05-11 T205-d residual closure brief

*Received 2026-05-11. Verbatim transcript below.*

---

## Assessment

The restructuring is mathematically sound as a **consumer chain**: the symmetric identity
$$\langle T_p f, g \rangle_N = \langle \langle u \rangle f, T_p g \rangle_N$$
does imply the usual unsymmetric adjoint form
$$\langle T_p f, g \rangle_N = \langle f, \langle u \rangle^{-1} T_p g \rangle_N$$
provided the project's diamond unitarity is oriented correctly, namely
$$\langle \langle u \rangle f, h \rangle_N = \langle f, \langle u \rangle^{-1} h \rangle_N.$$
Then Hecke/diamond commutation gives the canonical operator form. So **Q1 is yes**: symmetric ⇒ unsymmetric is a legitimate route.

The strategic issue is different: `petN_heckeT_p_symmetric_form` is **too large as a primitive worker target**. It is a clean named residual, but the natural proof target is still the **double-coset adjugate correspondence theorem**, not the symmetric identity directly. The symmetric identity is the right final consumer, but the theorem to assign should be closer to:
$$\langle T_{\Gamma \alpha \Gamma} f, g \rangle_\Gamma = \langle f, T_{\Gamma \alpha^* \Gamma} g \rangle_\Gamma$$
for the specific $\Gamma = \Gamma_1(N)$, $\alpha = \mathrm{diag}(1,p)$ or a slightly general $\alpha \in \Delta_0(N)$. Then specialize the adjugate double coset to $\langle u \rangle^{-1} T_p$, and finally derive the symmetric form by diamond unitarity.

**Path A is the right path, but I would revise its organization.** Do not make the worker prove a direct equality of the two unfolded sums in §7 as a monolithic σ_p-reindex. Prove the adjugate correspondence theorem first, then handle the $T_p$-specific diamond identification separately. **Path B is not a shortcut**; Atkin–Lehner–Li orthogonality uses the same adjoint/trace formalism and is at best equivalent work. **Path C is a bad-prime $U_p$ theory and does not prove the good-prime $T_p$ adjoint.** **Path D is not actionable.**

The biggest hidden trap in the brief is the phrase **"induced map on Hecke representatives $\beta \mapsto \beta'$."** For Hecke adjoints, adjugates of **left** coset representatives naturally become **right** coset representatives. A clean left-representative map $\beta_b \mapsto \beta_{b'}$ should not be expected in that naive form. For example, at level 1:
$$\begin{pmatrix} 1 & b \\ 0 & p \end{pmatrix}^* = \begin{pmatrix} p & -b \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} 1 & -b \\ 0 & 1 \end{pmatrix} \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix},$$
so all these adjugates lie in the **same left coset**, although they are distinct as the transposed correspondence data. This is exactly why per-$\beta$ balancing fails. The bijection lives on the **finite correspondence / tile index / right-left quotient data**, not on the displayed upper-triangular left representatives alone.

## Mathematical idea

Let $D = \langle u \rangle$ where $u = \overline{p} \in (\mathbb{Z}/N)^\times$. If
$$\langle T_p f, g \rangle_N = \langle Df, T_p g \rangle_N,$$
then diamond unitarity gives
$$\langle Df, T_p g \rangle_N = \langle f, D^{-1} T_p g \rangle_N.$$
That proves the standard adjoint form. Since $D^{-1}$ commutes with $T_p$, it also gives the canonical form with $T_p(D^{-1} g)$, depending on the project's preferred orientation.

The proof of the symmetric form should come from the **geometric transpose of the Hecke correspondence**. For a representative $\beta$ of the double coset, the single-slash adjoint changes
$$\int_{\mathcal{F}_\Gamma} \mathrm{pet}_k(f \mid_k \beta, g)$$
into an integral over $\beta \mathcal{F}_\Gamma$ with $g \mid_k \beta^*$. The individual domain $\beta \mathcal{F}_\Gamma$ is **not** a $\Gamma$-fundamental domain. **Only after summing over all representatives** does the collection of domains tile the correct finite-index subgroup quotient. **This is the actual content of DS 5.5.3.**

So the natural theorem is:
$$\sum_{\beta \in R(\Gamma \backslash \Gamma\alpha\Gamma)} \langle f \mid_k \beta, g \rangle_\Gamma = \sum_{\beta^\vee \in R(\Gamma \backslash \Gamma\alpha^*\Gamma)} \langle f, g \mid_k \beta^\vee \rangle_\Gamma,$$
where the right side is **not obtained by a naive pointwise map $\beta \mapsto \beta^*$**, but by the **transposed finite correspondence**. The FD-transport theorem already formalized is exactly the right analytic foundation for this.

For $\alpha = \mathrm{diag}(1,p)$, $\alpha^* = \mathrm{diag}(p,1)$. The adjugate double coset is identified with the original $T_p$-double-coset after the diamond correction $\langle u \rangle^{-1}$. This is where $\sigma_p$, the $\Gamma_0/\Gamma_1$ quotient action, and the triple-product identities belong. They **should not be mixed into the analytic correspondence-adjoint theorem.**

## Lean-facing next steps

Create a focused ticket under T205-d-SYMM, but **do not assign `petN_heckeT_p_symmetric_form` as the direct proof goal**. Assign the following smaller theorem chain.

### Step 1: wrapper around the already-proved integrated slash-adjoint

```lean
-- name illustrative
theorem peterssonInner_slash_adjoint_for_heckeRep
    (β : GL (Fin 2) ℚ) ... :
    ∫ z in FΓ, petersson k (f ∣[k] β) g z ∂μ
      =
    ∫ z in β • FΓ, petersson k f (g ∣[k] peterssonAdj β) z ∂μ
```

If `peterssonInner_slash_adjoint` already gives this, the ticket should only produce the specialization/wrapper and the required integrability hypotheses. **Do not re-prove the pointwise kernel unless Lean needs it for rewriting.**

### Step 2: finite-correspondence aggregation theorem

```lean
-- name illustrative
theorem petN_doubleCoset_adjoint_adjugate
    (Γ := Gamma1 N)
    (α : GL (Fin 2) ℚ)
    (R : Finset ...)
    (hR : R is a left-transversal for Γ \ ΓαΓ)
    (Rstar : Finset ...)
    (hRstar : Rstar is the transposed/left-transversal data for Γ \ Γ(peterssonAdj α)Γ) :
    petN (∑ β ∈ R, f ∣[k] β) g
      =
    petN f (∑ β' ∈ Rstar, g ∣[k] β')
```

This is the real Path A3/A4. It should consume the FD-transport theorem and the integrated slash-adjoint theorem. Acceptance should be the theorem above for the specific $\Gamma_1(N)$ and $\alpha = \mathrm{diag}(1,p)$ if general $\alpha$ is too expensive.

### Step 3: $T_p$-specific adjugate-coset identification

```lean
-- name illustrative
theorem heckeT_p_adjugate_correspondence_eq_diamond_inv_T_p :
    (adjugate-side aggregate for diag(1,p))
      =
    diamondOp u⁻¹ (heckeT_p ...)
```

The worker should organize this at the level of **double-coset/transversal equality**, not as a naive map $b \mapsto b'$ on the upper-triangular left representatives. If an explicit map is unavoidable, **first prove a right-transversal version and then convert it to the existing left-transversal Hecke operator.**

The warning example is:
$$\beta_b^* = \begin{pmatrix} p & -b \\ 0 & 1 \end{pmatrix} = T^{-b} \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix},$$
so the adjugates collapse as left cosets but not as correspondence data. This is a sign that **the indexing object is wrong** if the proof tries to map displayed left reps directly.

### Step 4: close

```lean
theorem petN_heckeT_p_adjoint_standard_form
theorem petN_heckeT_p_symmetric_form
```

The direction "canonical/unsymmetric adjoint ⇒ symmetric form" is just diamond unitarity:
$$\langle f, D^{-1} T_p g \rangle_N = \langle Df, T_p g \rangle_N.$$
Since the current code already has the reverse implication, this should be a short closure once the adjugate correspondence theorem lands.

### Cost estimate

- A1/A2 wrappers: 30–100 lines if existing integral slash adjoint is usable.
- The aggregation theorem: 150–300 lines if FD-transport API is clean, more if integrability/AE-disjointness hypotheses need rewriting.
- $T_p$-specific adjugate/diamond identification: 150–250 lines.
- **Total: 350–650 lines is realistic.**
- A direct proof of the monolithic symmetric residual could easily exceed that and be harder to debug.

## Risks or missing facts

1. **Wrong "$\beta \mapsto \beta'$" statement**: The adjugate of a left-transversal is not generally a left-transversal. Treat the transpose as a relation between finite correspondences or between right/left quotient data. If the worker insists on explicit upper-triangular formulas, they may rediscover the same collapse of $\beta_b^*$ into the lower left coset and think the theorem is false.

2. **Circularity**: Any proof that derives the symmetric form from the unsymmetric/canonical adjoint theorem is circular **unless the unsymmetric theorem was independently proved from the adjugate correspondence**. The safe route is:
   $$\text{single-slash adjoint + FD transport} \to \text{double-coset adjugate theorem} \to T_p\text{-diamond specialization} \to \text{unsymmetric/canonical form} \to \text{symmetric form}.$$

3. **Overgeneralization**: Full general $\alpha \in \Delta_0(N)$, all characters, all congruence subgroups is elegant but not necessary. **Minimal non-circular theorem is the adjugate correspondence for $\Gamma_1(N)$, $\alpha = \mathrm{diag}(1,p)$, $p \nmid N$. Generalize only after closure.**

4. **Underestimating A3**: Even with FD transport done, Lean may require explicit null-measurability, integrability under slash, and pairwise AE-disjointness of the finite family of tiles. Separate these into wrappers around the existing FD theorem rather than fold them into the adjugate proof.

5. **Path B**: Li's newform orthogonality uses trace/adjoint relations of degeneracy and Hecke correspondences. May not literally invoke $T_p^* = \langle p \rangle^{-1} T_p$, but uses same analytic adjoint infrastructure. **Should not be assigned as a shortcut to T205-d.**

## Manager message to worker

TICKET: T205-d-SYMM
STATUS: active
LEAN ISSUE: no
MATH ISSUE: no, but the current residual is too monolithic for the next proof pass
BLOCKER: `petN_heckeT_p_symmetric_form`

The restructuring is sound: the symmetric form $\mathrm{petN}(T_p f, g) = \mathrm{petN}(\langle u \rangle f, T_p g)$ does imply the unsymmetric DS adjoint form by diamond unitarity, and then Hecke/diamond commutation gives the canonical operator form. So the consumer chain is valid.

**Do not try to prove `petN_heckeT_p_symmetric_form` directly by another global $\sigma_p$ reindex.** The better primitive target is the adjugate double-coset correspondence. Work in this order:

1. Wrapper around existing `peterssonInner_slash_adjoint` for a Hecke representative $\beta$.
2. Finite-correspondence aggregation theorem for $\Gamma = \Gamma_1(N)$, $\alpha = \mathrm{diag}(1,p)$.
3. $T_p$-specific identification of adjugate-side aggregate with $\langle u \rangle^{-1} T_p$ (where the diamond/$\sigma_p$ bookkeeping belongs).
4. Close unsymmetric adjoint form, then `petN_heckeT_p_symmetric_form` by diamond unitarity.

**Important warning**: do not model this as a naive function on the displayed upper-triangular left representatives $\beta_b \mapsto \beta_{b'}$. The adjugates of left representatives naturally give **right-transversal data**.

Park Path B and Path C. Do not open Atkin–Lehner–Li orthogonality or $U_p$-decomposition as a workaround for this good-prime adjoint theorem.

**Acceptance for the next report**: either a compiling adjugate-correspondence aggregation theorem for $\Gamma_1(N)$, $\alpha = \mathrm{diag}(1,p)$, or one exact missing FD/integrability/transversal lemma blocking that theorem.
