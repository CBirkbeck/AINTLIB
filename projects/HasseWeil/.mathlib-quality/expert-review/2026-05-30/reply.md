# Reviewer reply — round 12 (2026-05-30)

## Verdict
Not Route A or Route B as stated. The cleanest route is **Route C: repair the Pic⁰ route at the divisor/class-group level — use scheme-theoretic divisor pullback / ideal extension with ramification multiplicities, NOT prime comap.**

The brief's "Pic⁰ is degree-blind" is correct for the *implemented point-level/comap bridge*, but NOT true of classical Pic⁰ functoriality. Classical Pic⁰ sees the full degree (incl. inseparable) because divisor pullback includes ramification indices. For finite α: C→C':
  α*(Q) = Σ_{P↦Q} e(P/Q)·P,   α_*(P) = [κ(P):κ(Q)]·Q,
so  α_*α*(Q) = Σ_{P↦Q} e(P/Q)f(P/Q)·Q = deg(α)·Q  — the full function-field degree.
Inseparable Frobenius sanity check: topologically a bijection on geometric points, so prime comap sees one point, but divisor pullback gives multiplicity q. So a Pic⁰ construction based on comap of maximal ideals is degree-blind; one based on divisor pullback is not. The brief's own "class-group functoriality with norm/extension and norm∘ext=(·)^[deg]" is EXACTLY the piece that sees full degree.

Recommendation:
  Primary: repair Pic⁰ functoriality from prime-comap to divisor/ideal extension with ramification exponents.
  Secondary: keep formal-group Route A only for local/genuineness lemmas if needed.
  Do NOT start quotient-by-kernel Route B as the main path.

## The key correction: Pic⁰ is not intrinsically degree-blind
The diagnosis is accurate about the *implementation*: contraction of a rational point's maximal ideal through α* records set-theoretic image/preimage; norm∘comap sees residue/inertia degree, not full ramification. But Pic⁰ functoriality uses divisor pullback/pushforward. In ideal-class language: pullback of a prime is EXTENSION of ideals 𝔭 ↦ 𝔭·O_L = ∏_{𝔓|𝔭} 𝔓^{e}, and N(𝔭 O_L) = 𝔭^{Σ e·f} = 𝔭^{[L:K]} = full degree.
So the bug is NOT "Pic⁰ cannot see inseparability." The bug is: the implemented Pic⁰-isogeny bridge used prime contraction/comap where the duality proof needs divisor pullback/ideal extension. Good news: the Pic⁰ work is not wasted — one correction, not abandonment.

## Q1 — Route A or B? → Route C (corrected Pic⁰).
If forced, A is probably lighter than full kernel quotient by non-étale group schemes. But try the Pic⁰ repair first (reuses the new infrastructure, addresses the actual failure).
- Why not A primary: constructing a genuine (rV−s) via formal-group pole bounds makes the map genuine but does NOT prove it's the DUAL. (rV−s)(rπ−s)=[N] at the pullback level gives only deg(rV−s)deg(rπ−s)=N², NOT deg(rπ−s)=N. (e.g. [3]∘[2]=[6] but deg[2]=4≠6.) A degree-extraction lemma from a scalar composition is FALSE without a hidden duality/degree-equality hypothesis. Route A still lacks the sign/dual content.
- Why not B primary: E/ker(β) for β=rπ−s with p|s needs non-étale group schemes (infinitesimal kernels, Frobenius factorisation, quotient-by-finite-flat-group-scheme). Much larger than a divisor-pullback correction in Lean.

## Q2 — Does E/ker(β) handle inseparable cleanly? Mathematically yes, formally heavy.
For inseparable β, ker is a finite group scheme with infinitesimal part. Quotient exists but needs β=σ∘F^k (or F^k∘σ), relative Frobenius + separable + descent/twist identification. Delivers the inseparable factor p^k but the Frobenius-twist + finite-flat-quotient machinery is real content. Not lighter than the Pic⁰ repair unless you already have quotient group-schemes.

## Q3 — Degree-decomposition shortcut? Possible but k is NOT v_p(s).
a_β = −s, so β separable ⟺ p∤s. But the exact inseparable degree is NOT generally p^{v_p(s)}: rπ already contains a q-Frobenius contribution and cancellations shift the Frobenius power. The correct k = max{n : β*K(E) ⊆ K(E)^{p^n}} (largest Frobenius power through which the comorphism factors) — a function-field/Frobenius-slope statement. Computing it uniformly needs (1) full Frobenius-power factorisation, (2) separable degree of the remaining factor, (3) product=N. Comparable to quotient/factorisation machinery; not a cheap shortcut.

## Q4 — Missing third route / how Pic⁰ contributes: the ramified divisor-pullback / ideal-extension version of Pic⁰ functoriality.
Implement class-group pullback as [𝔞]↦[𝔞ℬ] (extension, with 𝔭ℬ=∏𝔓^e), so N_{B/A}(𝔭ℬ)=𝔭^{[L:K]} (full degree), i.e. α_*α*D=(deg α)D — works for inseparable maps because ramification records inseparable multiplicity.
Suggested Lean targets:
  classGroup_norm_ext_eq_pow_finrank : normClass (extendClass c) = c ^ finrank   [you have a version]
  divisor_pullback_point_class_eq_extension : classOf(α* P) = idealClassOf(extendIdeal (maxIdeal P))  [WITH multiplicities]
  pic_push_pull_eq_degree : α_*(α* D) = (deg α)•D   on Pic⁰   [the full-degree Pic⁰ theorem you need]
This avoids A/B: Pic⁰ constructs the dual at the divisor/class level with the right scalar deg β; then use genuine-isogeny extensionality / the existing bridge to get the comorphism.

## Warning about "genuine comorphism of the Pic⁰ map"
If Pic⁰ is only an abstract group iso E(F)≅Cl(F[E]), constructing the function-field comorphism of the Pic⁰-induced map is nontrivial. You may not need to construct it separately IF you can prove extensionality: (1) construct a candidate genuine δ by existing means (or via the Pic⁰ map if supported); (2) prove its action on classes/points agrees with the Pic⁰ dual; (3) prove the dual composition equality by class-group functoriality; (4) genuine-isogeny extensionality identifies comorphisms. If no candidate genuine map exists, you still need a genuine-map construction — the corrected Pic⁰ route gives degree/composition; the local formal-group route gives genuineness if needed. Complementary.

## Recommended path
- Step 1: Fix the Pic⁰ bridge — replace point/maximal-ideal comap with divisor/ideal-extension (with ramification multiplicities). (Don't call classical Pic⁰ degree-blind; call the current implementation degree-blind.)
- Step 2: Prove full-degree Pic⁰ push-pull α_*α*=[deg α] on Pic⁰ (use the already-proved norm/extension class-group theorem). THE critical theorem.
- Step 3: Recover dual additivity (φ+ψ)^=φ̂+ψ̂ ⟹ (rπ−s)^=rV−s.
- Step 4: Close with shipped V, Vπ=[q], π+V=[t], point-map composition.

## Direct answers
Q1: Between A and B, A probably lighter, but recommend NEITHER as primary — repair Pic⁰ via divisor pullback/ideal extension with ramification (lighter than quotient-by-non-étale-kernel, reuses your new infra).
Q2: Quotients handle inseparable mathematically but only via finite group schemes / Frobenius factorisation — substantial, relocates the same inseparable content.
Q3: Degree-decomposition possible but k is the largest Frobenius power through which β* factors, NOT v_p(s); a serious function-field/Frobenius-divisibility problem.
Q4: The missing route is to FIX the Pic⁰ implementation (comap-on-primes → ideal extension / divisor pullback with ramification). Then Pic⁰ contributes exactly to the inseparable part.
