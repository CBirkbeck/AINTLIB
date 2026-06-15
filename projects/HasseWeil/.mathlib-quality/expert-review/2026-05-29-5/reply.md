# Reviewer reply — round 11 (2026-05-29)

## Verdict

Yes: the §3 finding is correct. The "narrow Route A" formal-group pole-bound route does **not** close Leaf 1 by itself. It gives you a genuine (rV-s) and hence can supply the comorphism-level composition

(rV-s)(rπ-s)=[N], N=qr²-trs+s²,

but it does **not** prove that (rV-s) is the dual of (rπ-s). That missing statement is exactly the signed degree statement in disguise:

(rV-s)(rπ-s)=[deg(rπ-s)].

Given the Vieta composition (rV-s)(rπ-s)=[N], proving `IsDualOf (rV−s) (rπ−s)` is equivalent to proving deg(rπ-s)=N, which is the goal. Your brief formulates this point accurately.

So I would **abandon BRIDGE-003 as a primary Hasse-bound route**. It may remain useful infrastructure for addition-pullback/genuineness elsewhere, but for Leaf 1 it is dominated by the real target: dual existence/additivity on the Frobenius plane. Dual existence plus dual additivity gives both facts you need: it constructs the genuine dual and proves it has the right defining composition.

## Q1 — Is the §3 finding correct?

Yes. Let β=rπ-s, β^∨=rV-s. Suppose you have proved the genuine comorphism-level identities β^∨β=[N], ββ^∨=[N]. Taking degrees gives only deg(β^∨)deg(β)=N². Even if you also prove deg(β^∨)=deg(β), you only get deg(β)=|N|. That is insufficient. Hasse needs N≥0, and the clean way to get that is to identify β^∨=β̂. Then β̂β=[deg β], so comparing with [N] gives the signed identity deg β=N.

There is no sign hidden in degree multiplicativity. For example, [-1]∘[m]=[-m] has positive degree m² but negative multiplication scalar. So a composition equal to [N] can have negative N. The sign comes from the dual relation, not from the degree product.

Thus BRIDGE-003 supplies only: genuineness of rV-s + β^∨β=[N], i.e. your condition (i). It does not supply condition (ii). Your analysis is right.

## Q2 — Pic⁰ route or kernel/factorisation route?

Choose the **Pic⁰ route**.

The kernel/factorisation route is good for proving existence of a dual in a classical way, but it is less convenient for what Leaf 1 actually needs: **additivity of the dual**.

You need widehat(rπ-s)=r·π̂-s=rV-s. Pic⁰ functoriality gives this naturally. The dual is built as the Pic⁰-push/pull map transported through E≃Pic⁰(E), and functoriality/additivity of Pic⁰ maps gives (φ+ψ)^=φ̂+ψ̂ with the correct genuine morphism/comorphism data.

The kernel/factorisation route, by contrast, typically proves dual existence by factoring [deg α] through α. That gives the dual of a particular α, but dual additivity is a second theorem. Proving it from the factorisation/quotient construction usually requires uniqueness of duals, degree bookkeeping, quotient curves (E/ker α), separable/inseparable factorisation, and then another argument that the factorisations behave additively. It is not the shortest way to get (rπ-s)^=rV-s.

So the route I would commit to is:
  Pic⁰(E) ≅ E
  + Pic⁰ functoriality/push-pull
  + dual composition α̂ ∘ α = [deg α]
  + dual additivity
  ⇒ (rπ−s)^ = rV−s
  ⇒ deg(rπ−s)=qr²−trs+s².

You do not necessarily need to expose a full public theorem ∀ α, ∃! α̂ first. You can target the narrower theorem:
  theorem frobeniusPlane_dual (r s : ℤ) : IsDualOf (r • V - s • id) (r • π - s • id)
But the proof will almost certainly use the same Pic⁰ functoriality as the general theorem. If the general statement is not much more expensive once the machinery exists, proving the general `exists_dual` may be cleaner and more reusable.

### A useful implementation refinement

You do not need to construct (rV-s) via `addIsog`/BRIDGE-003 if the Pic⁰ dual theorem returns a genuine dual β̂. Instead:
1. Let β̂ be the Pic⁰-defined genuine dual of β=rπ-s.
2. Prove its **point-map** equals rV-s using Pic⁰ functoriality/additivity.
3. Use genuine-isogeny extensionality to identify compositions with [N].
4. Compare β̂β=[deg β] with [N].
This is precisely why dual existence subsumes BRIDGE-003 for Leaf 1: it avoids constructing rV-s by the addition formula entirely.

## Q3 — Any cheaper substitute for the quadratic-form content?

I do not see a cheaper substitute that avoids equivalent duality content.

**Parallelogram law.** A direct proof of deg(φ+ψ)+deg(φ-ψ)=2deg φ+2deg ψ would indeed give the quadratic-form structure. But proving this law is essentially proving that deg is a quadratic form on End(E). In standard elliptic-curve theory, that comes from dual isogenies/Rosati, intersection theory, or Weil pairing. It is not a lighter primitive; it is the same theorem in another form. I agree it does not look independent.

**Degree symmetry deg(rV-s)=deg(rπ-s).** Even if you prove this independently, the composition identity only gives deg(rπ-s)=|N|. It does not prove N≥0. The sign remains the missing information. The sign is exactly what the dual relation supplies.

**Tate module / Weil pairing.** Valid alternate proof. For ℓ≠p, prove deg(α)≡det(α|E[ℓⁿ]) (mod ℓⁿ), compute determinant of rπ-s from the characteristic polynomial of Frobenius, lift congruences to integers. But requires E[N]≅(ℤ/N)², Weil pairing, determinant-degree formula, Frobenius trace comparison, congruence-to-integer lifting. Not lighter than Pic⁰; a serious alternative route, not a shortcut.

**Point-count/kernels for rπ-s.** Only helps for separable members and still leaves a hard two-parameter kernel-size problem. In inseparable cases also need deg_i(rπ-s). Likely worse than Pic⁰.

So no, there is no evident cheaper substitute. The alternatives are equivalent in content or larger in infrastructure.

## Q4 — Does §3 change the round-10 recommendation?

Yes. Stop treating BRIDGE-003 as the Hasse-critical path for Leaf 1. Commit the deep effort to dual existence/additivity, preferably via Pic⁰. BRIDGE-003 gives a genuine rV-s, but the Hasse argument still needs the independent dual relation. If you prove the dual theorem, the dual itself is genuine by construction and equals rV-s by additivity; therefore BRIDGE-003 becomes unnecessary for Leaf 1. I would not delete BRIDGE-003 work if it is useful elsewhere: it remains valuable addition-pullback/formal-group infrastructure. But it should not drive the Hasse-bound critical path.

### Revised critical path
1. Pic⁰ dual construction / functoriality. Prove a genuine dual isogeny α̂ with α̂α=[deg α].
2. Dual additivity on the Frobenius plane. Prove widehat(rπ-s)=rV-s at least at point-map level, with the dual itself genuine.
3. Use extensionality. The point-map Vieta computation gives (rV-s)(rπ-s)=[N]. Since the dual is genuine, extensionality upgrades to comorphism-level.
4. Compare scalar multiplications. From β̂β=[deg β] and β̂β=[N], conclude deg β=N.
5. Then Leaf 1 follows.

## One caution: zero and scalar-collapse cases

The claim `0 < deg(rπ − s)` should be handled carefully. True for nonzero genuine isogenies. But if rπ-s=0 as an endomorphism in a supersingular/scalar situation, the natural degree is 0, not positive. The final theorem must isolate the zero-endomorphism branch cleanly. For the generic branch this is fine. For the global ∀ r s, use:
  by_cases hβ : rπ - s = 0
    · Q(r,s)=0, prove directly from the scalar relation / trace relation
    · use deg β > 0 and dual argument
or define the theorem in terms of an endomorphism degree with deg 0 = 0.

## Final answers
Q1. Yes. The finding is correct. BRIDGE-003 gives genuineness/composition, not the dual relation. Two-sided [N] plus degree multiplicativity gives only a square/absolute-value statement, not the signed degree.
Q2. Use the Pic⁰ route. Natural for dual additivity. Kernel/factorisation can prove existence, but additivity is much less direct and likely heavier.
Q3. No cheap substitute apparent. Parallelogram law, degree symmetry, torsion determinant routes either encode the same duality content or require large new infrastructure.
Q4. Yes — abandon BRIDGE-003 as a Hasse-critical path and commit to dual existence/additivity. Keep BRIDGE-003 only as reusable infrastructure.
