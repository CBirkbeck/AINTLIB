# Reviewer reply — 2026-06-24 (round 2; Eichler-integral injectivity)

## Verdict
There is a THIRD option, now recommended: **prove period-map injectivity using the Eichler integral
and Bol's identity.** This avoids the Petersson product, cup products, Green–Stokes,
fundamental-domain tilings, and Shimura's boundary formula (IHR-c). It uses only one-variable
integration, a change of variables under SL₂(ℤ), Fourier expansions at cusps, and the vanishing of
holomorphic modular forms of negative weight. Do NOT switch to the q-expansion-lattice route, and do
NOT commit to the multi-month tiling assembly before trying this. If it proves awkward in Lean, citing
classical **period-map injectivity** is entirely acceptable — a cleaner cited input than IHR-c or FIH.

## 1. Injectivity without IHR-c
Γ = Γ₁(N), n = k-2, f ∈ S_k(Γ), ι(f)=0, so for all cusps α,β and all P ∈ Sym^n:
  ∫_α^β f(τ)P(τ,1) dτ = 0.   (1)

### 1.1 Eichler integral
At ∞: f(z) = Σ_{m≥1} a_m q^m. Set
  E_f(z) = Σ_{m≥1} (a_m / m^{k-1}) q^m.   (2)
With D = (1/2πi) d/dz:  D^{k-1} E_f = f.   (3)
Up to a fixed nonzero constant C_k:  E_f(z) = C_k ∫_z^{i∞} f(τ)(τ-z)^{k-2} dτ   (4)
(absolutely convergent by cusp decay).

### 1.2 Modularity defect = period polynomial
For γ = [[a,b],[c,d]] ∈ Γ:
  (E_f|_{2-k} γ)(z) - E_f(z) = C_k ∫_{γ⁻¹∞}^∞ f(τ)(τ-z)^{k-2} dτ.   (5)
Expanding (τ-z)^n = Σ_j C(n,j)(-z)^{n-j} τ^j, every coefficient of the RHS is a period ∫ f τ^j dτ.
So (1) ⟹ E_f|_{2-k} γ = E_f for all γ ∈ Γ.   (6)
Thus E_f transforms as a modular form of weight 2-k = -n (the classical Eichler cocycle; the
Eichler–Shimura map sends f to its cohomology class; cf. connecting morphism of an exact sequence).

### 1.3 Holomorphy at every cusp (must be included; invariance on ℍ alone allows weakly-holo forms)
For a cusp α = σ∞, the Eichler integral based at α, E_{f,α}(z) = C_k ∫_z^α f(τ)(τ-z)^n dτ, differs
from E_f by C_k ∫_α^∞ f(τ)(τ-z)^n dτ = 0 by (1). So E_{f,α} = E_f.   (7)
After slashing by σ, the LHS becomes the Eichler integral at ∞ of f|_k σ. If the cusp width is h and
(f|_k σ)(z) = Σ_{m≥1} b_m e^{2πimz/h}, then
  (E_f|_{2-k} σ)(z) = C_k' Σ_{m≥1} (b_m / (m/h)^{k-1}) e^{2πimz/h}.   (8)
Only positive Fourier powers ⟹ E_f holomorphic AND vanishing at every cusp.

### 1.4 Finish by negative-weight vanishing
If k>2: E_f has weight 2-k < 0. Formalization-friendly (avoids valence formula): with n = k-2 > 0,
E_f^{12} Δ^n has weight 12(2-k) + 12n = 0, holomorphic on ℍ, vanishing at every cusp (Δ does), so it
is a holomorphic function on the compact modular curve, hence constant, hence 0; Δ has no zeros on ℍ,
so E_f = 0. If k=2: E_f has weight 0, holomorphic on the compactified curve, vanishes at cusps, so
E_f = 0. Then (3): f = D^{k-1} E_f = 0.
⟹ **Eichler-integral injectivity: ι : S_k(Γ₁N) → Hom_ℤ(𝕄, ℂ) is injective for all k ≥ 2.** Proves
IHR-d without IHR-c.

## 2. Fit with group cohomology
Exact sequence of Γ-modules (Bol): 0 → V_{k-2} → O(ℍ)_{2-k} --D^{k-1}--> O(ℍ)_k → 0,  (9)
V_{k-2} = ker D^{k-1} = polynomials of degree ≤ k-2. Bol's identity: D^{k-1}(F|_{2-k}γ) =
(D^{k-1}F)|_k γ.  (10). Antiderivative of f ⟹ connecting cocycle γ ↦ E_f|_{2-k}γ - E_f; (5) identifies
it with the period cocycle. KEY: because ι(f)=0 (the FULL modular-symbol functional is zero, stronger
than the cohomology class being zero), the cocycle is LITERALLY zero, not just a coboundary —
eliminating polynomial-correction-term issues. The existing divisor cocycle stays useful.

## 3. §2(a) cup products — NOT cheaper
Cup-product nondegeneracy on parabolic cohomology → injectivity of the holomorphic period map requires
showing the pairing of [f] with the conjugate class is a nonzero multiple of (f,f)_Pet — the
Haberland–Shimura formula. So cup product ↔ Petersson does not remove the global identity, it packages
it cohomologically; proving the comparison recreates the boundary/de Rham integration. The useful
group-cohomological route is the connecting-homomorphism/Eichler-integral argument, NOT cup product.

## 4. §2(b) Fourier inversion — possible, not recommended as foundation
Periods relate to additive twists / critical L-values; Paşol–Popa give coefficient formulas from
period polynomials. But: recovering all coefficients is stronger than injectivity; needs twist + tail
control; boundary values don't give simple uniqueness; eigenform-only formulas need reduction to
eigenforms. The Eichler-integral argument uses the q-expansion only for the easy cusp-holomorphy step.

## 5. Updated cost calculus
KEEP IHR-a, IHR-b; FORMALIZE the Eichler-integral proof of IHR-d; DO NOT formalize IHR-c. Atomic
results needed: (1) construction + convergence of E_f; (2) D^{k-1}E_f = f; (3) transformation-defect
formula (5); (4) expansion of the defect in terms of the period functional; (5) local-cusp identity
(7) + positive Fourier expansion (8); (6) vanishing in weight < 0 and weight 0. None needs a 2D region
integral. The modular-symbol route is still lighter than an integral model or global q-lattice; the
expensive part was choosing to prove injectivity through Petersson/Haberland rather than Eichler
integrals.
If citing: best cited input = **period-map injectivity** (canonical, normalization-independent),
ranked: period-map injectivity > IHR-c > FIH.

## 6. Weight 1
Deligne–Serre **Prop 2.7** is the precise input: defines L by integrality of q-expansions of all
diamond translates, L finite free over ℤ, Hecke+diamond stable, S_K = K ⊗_ℤ L for all char-0 K, and
derives algebraic integrality + finite-degree of the eigenvalues. It is in §2, BEFORE the
Galois-representation construction, so citing it does NOT import the full DS weight-1 theorem. (DS also
note: bounded denominators in weight 1 alternatively via ×Δ, reducing to weight 13 + Shimura k≥2.)
CAVEATS: dim_ℂ S_1 < ∞ + integral-looking Hecke formula do NOT prove full rank (only stability once
the structure is present). And DS Prop 2.7's Fourier formula for T_p-stability is for p∤N — if the
weight-1 FIH includes bad-prime U_p, add that separately (or via local newform theory), don't
attribute to Prop 2.7. Suggest: separate weight-1 theorem under the DS lattice input.

## 7. Soundness audit of IHR-c — POTENTIALLY SERIOUS
𝕄 = (Div⁰(P¹Q) ⊗ Sym^{k-2}ℤ²)_Γ (coinvariants). For g₀ ∈ Γ and y in the tensor module, by definition
of coinvariants [(1-g₀)y] = 0 in 𝕄. (11)  g₀ = [[1,0],[N,1]] ∈ Γ₁(N), so a symbol literally
(1-g₀)·{0,∞} CANNOT be a nonzero element of the coinvariant Manin module IF (1-g₀) is the DIAGONAL
action defining 𝕄. It CAN be nonzero: (a) as a raw edge chain before coinvariants; (b) if g₀ acts only
on the divisor factor with the polynomial coefficient untransformed; (c) as one term in a paired-edge
formula whose two edges carry different coefficient polynomials. These are DIFFERENT TYPED statements —
make the distinction explicit. (g₀ fixes 0, sends ∞→1/N, so raw difference ≈ {1/N,∞}; raw nonzeroness
does NOT imply coinvariant-class nonzeroness.)
Also: A(f,g) is NOT generally a "genuine nonzero area integral" — it vanishes for many (f,g); nonzero
only after g = i^{k-2}f, f≠0. Convention (conjugate-linear in 1st arg) should be explicit.
Faithful statement of IHR-c: either a FIXED bilinear/sesquilinear comparison A(f,g) = B(ι(f),ι(g))
(Haberland–Shimura), B fixed independent of f; or the minimal consequence ι(f)=0 ⟹ A(f,g)=0 ∀g. Do
not certify the schematic brief formula as a literal restatement of Shimura (8.2.22) without auditing
constants/conjugations/orientations.

## 8. Soundness audit of the lattice input
Λ ⊂ S_k, ℂ ⊗ Λ ≅ S_k, Λ finite free + Hecke-stable: sound, and faithfulness of the ℂ-action follows
from scalar-extension (need not be assumed). Two qualifications:
1. **Finite generation is NOT automatic from finite-dimensionality + ℂ-spanning** — a ℤ-submodule of a
   finite-dim ℂ-space may have infinite rank. Freeness follows once f.g. + torsion-free are known, but
   f.g. is part of the SUBSTANTIVE lattice theorem (DS prove it via bounded denominators + separating
   Fourier functionals).
2. For Γ₁(N) the natural lattice is NOT just {f : a_m(f) ∈ ℤ at ∞}; DS impose integrality on all
   diamond translates with cyclotomic-integer coefficients. Shimura Thm 3.52 is for Γ(N), k≥2; passing
   to the Γ₁(N) full-operator lattice is an extra step. DS Prop 2.7 is the closer citation.

## Recommended final dependency graph
k≥2: finite Manin module + integral Hecke action + equivariant period map + **Eichler-integral
injectivity** ⟹ FIH ⟹ (a_n alg. integers; K_f/ℚ finite; label canonicity).
k=1: Deligne–Serre-type full-rank Hecke-stable lattice ⟹ FIH ⟹ same.
Central conclusion: **Do not build the global boundary identity solely to prove injectivity. Replace
IHR-c by the Eichler-integral/Bol argument; if one classical citation remains necessary, cite
period-map injectivity itself.**

## References cited by reviewer
- Holomorphic modular forms and cocycles (Res. Math. Sci., Springer, doi 10.1007/s40687-018-0128-2).
- Eichler–Shimura isomorphism and group cohomology on arithmetic groups (arXiv:1701.00611).
- Modular forms and period polynomials, Paşol–Popa (arXiv:1202.5802).
- Deligne–Serre, "Formes modulaires de poids 1" (Ann. ÉNS; Numdam asens.1277) — Prop 2.7.
- Shimura Thm 3.52 (integral Fourier basis for S_k(Γ(N)), k≥2); Murty notes (Queen's) for context.
