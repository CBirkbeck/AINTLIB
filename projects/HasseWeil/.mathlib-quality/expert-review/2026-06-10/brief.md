# Review brief (round 24) — the dual isogeny: the last wall is `#ker φ = deg φ` for separable φ

*Prepared 2026-06-10 for the same senior arithmetic-geometry reviewer as rounds 1–23.
Self-contained but focused, in the style of round 23: a **single-wall** brief. Round 23's
Route B closed the unconditional Hasse bound (machine-checked, no unproven assumptions).
Since then the project has moved to the Silverman continuation — isogeny foundations,
the Tate module, and the dual isogeny — and that whole programme now funnels into **one**
remaining mathematical wall. We ask how to break it, plus three smaller questions.*

---

## 0. Orientation (one paragraph)

After round 23 the Hasse bound was completed. The continuation since then, all
machine-checked with no unproven assumptions unless stated: **(a)** Silverman III.4.8 —
*every isogeny is a group homomorphism* — is now a theorem in our framework (via the
Picard-group pushforward and the norm–conorm identity div(N_φ f) = φ_*(div f), II.3.6);
**(b)** the Tate-module chapter is complete (E[ℓⁿ] ≅ (ℤ/ℓⁿ)², T_ℓ(E) ≅ ℤ_ℓ², and the
ℓ-adic representation ρ_ℓ : Gal → GL₂(ℤ_ℓ)); **(c)** the dual-isogeny apparatus is built:
the dual exists *concretely* for [n] (with [n]^ = [n]), for the q-power Frobenius π
(with π̂ = the Verschiebung V, V∘π = [q], constructed, not assumed), and for composites
(with the faithful multiplicativity: the dual of ψ∘φ composed with ψ∘φ is [deg ψ∘φ]);
and the dual of an *arbitrary* isogeny is reduced to the dual of its separable part via
φ = φ_sep ∘ πʳ. Every remaining gap in the dual / isogeny-class programme reduces to one
statement: **#ker φ = deg φ for a general separable isogeny** (Silverman III.4.10c).
This is exactly the fact the Hasse proof was engineered to avoid (round 22's "use #ker
as the exponent" simplification). Now we need it.

## 1. Setting and notation

- E, E₁, E₂ are elliptic curves over a field F (usually F = K̄, an algebraic closure of
  a finite field; some statements hold over any F), given by Weierstrass equations, with
  function fields K(E) etc. and distinguished point O (the place at infinity).
- An **isogeny** φ : E₁ → E₂ is carried by its function-field embedding
  φ* : K(E₂) ↪ K(E₁) (an F-algebra map) together with the regularity condition at O
  ("functions regular at O pull back to functions regular at O"). The **degree** is
  deg φ = [K(E₁) : φ*K(E₂)]; separable/inseparable degrees as usual. The point map is
  recovered from φ* where needed (a coordinate-ring witness; for [n], π, V and their
  composites this is constructed, not assumed).
- **ord_P** denotes the normalized valuation at a closed point/place P; ord_∞ = ord_O.
- ker φ = the kernel of the induced group homomorphism on points (III.4.8 makes this a
  group); τ_T = translation by T; τ_T* the induced automorphism of K(E₁).
- [n] is multiplication by n; π the q-power Frobenius of a curve over a field with q
  elements (or its base change to K̄); V the Verschiebung.

## 2. Established since round 23 (the toolkit the answer may use)

All of the following are proven and machine-checked, with no unproven inputs:

**T1 (III.4.8).** Every isogeny is a group homomorphism on points. *Sketch:* the divisor
pushforward φ_* descends to Pic⁰ because pushforward preserves principal divisors —
div(N_φ f) = φ_*(div f) for the field norm N_φ (II.3.6; proved via the global norm
balance m_Q^{deg} = ∏ relNorm(m_P)^{e_P} together with Σ e_P f_P = deg and the
residue-degree computation f = 1 over algebraically closed F) — then the Abel–Jacobi
square κ₂∘φ = φ_*∘κ₁ and injectivity of κ₂ transfer additivity to φ. ∎

**T2 (fibre torsors — the III.4.10a transport).** If *some* fibre of φ has cardinality
equal to deg_s φ, then *every nonempty* fibre does. (Fibres are kernel cosets via T1;
the torsor transport is done. So the wall reduces to exhibiting **one** good fibre.)

**T3 (Σ e·f = deg, per place).** For every maximal ideal Q of the affine coordinate ring
of E₂ (under a coordinate-ring witness for φ, the extension being module-finite):
Σ_{P over Q} e_P · f_P = deg φ. Moreover **f_P = 1** for every P when F is algebraically
closed (residue fields are F itself; proven). At the infinite place the full pullback
formula **ord_∞(φ*g) = e_φ(O) · ord_∞(g)** holds for every isogeny, with **e_φ(O) ≥ 1
always** (no hypotheses; the e ≥ 1 step is a new lemma: an ord-valuation trivial on a
subfield over which the extension is algebraic is trivial, by the minimal-polynomial
ultrametric argument — and K(E₁) is always algebraic over φ*K(E₂) by transcendence-
degree reasons).

**T4 (fixed field = image; circularity mapped).** For any isogeny over any field,
*given* the translation covariance (τ_T*∘φ* = φ* for T ∈ ker φ) *and* #ker φ = deg φ,
the image is exactly the fixed field: φ*K(E₂) = K(E₁)^{ker φ}. Conversely, given the
covariance and the two dimension counts ([K(E₁) : Fix] = #ker by Artin's theorem,
[K(E₁) : Im] = deg), the equality Im = Fix is *equivalent* to #ker = deg. So the
fixed-field route cannot supply the count; one side must be geometric.

**T5 (translation covariance, generally).** The covariance τ_T*∘φ* = φ* (T ∈ ker φ),
and the generic-point covariance needed throughout, holds for every isogeny equipped
with a coordinate-ring witness over K̄. (New engine: evaluation coherence at all but
finitely many closed points + "two rational functions agreeing at cofinitely many
points are equal", using that E(K̄) is infinite via the ℓ-torsion counts.)

**T6 (the dual apparatus).** [n] is an isogeny in our framework for every n ≠ 0
(including p | n; the regularity-at-O condition was proven by an even/odd pole-parity
argument in the basis {1, y} over F(x)). The dual exists concretely with its defining
identity: [n]^ = [n] over any field (the inclusion Im([n²]*) ⊆ Im([n]*) is free from
the multiplicativity [nm]* = [m]*∘[n]*, which is proven); π̂ = V with V∘π = [q]
(V constructed from the q-th-root description of K(E)^q, its regularity at O *derived*);
duals compose faithfully (the dual of ψ∘φ satisfies the [deg ψ · deg φ] identity once
each factor has its witness); and every isogeny with inseparable degree a power of q
factors as φ = φ_sep ∘ πʳ with the dual of φ reduced to the dual of φ_sep. The **only
missing input in this entire apparatus** is the witness package for a *general
separable* φ, whose sole non-formal content is the count below.

**T7 (the Galois half).** For separable φ: separability of K(E₁)/φ*K(E₂) is in hand
(via the invariant differential: the differential coefficient a_φ ≠ 0 ⟺ separable);
#Aut(K(E₁)/φ*K(E₂)) ≤ deg_s φ = deg φ (basic Galois theory); and the kernel-translation
map T ↦ τ_T* into that automorphism group is *injective*. What is open is its
**surjectivity** (equivalently: normality of the extension plus the count — this is
Silverman III.4.10b/c).

## 3. The wall, precisely

> **Wall (Silverman III.4.10c).** Let φ : E₁ → E₂ be a separable isogeny (over K̄, say).
> Then #ker φ = deg φ.

By T2 it suffices to exhibit **one** point Q ∈ E₂ with #φ⁻¹(Q) = deg φ (the fibre over
O, which is nonempty since it contains ker φ ∋ O, then has the same cardinality).

Silverman's own proof rests on II.2.6b — "#φ⁻¹(Q) = deg_s φ for all but finitely many
Q" — which he cites from the general theory of curves (Hartshorne II.6.8/6.9). That
generic-fibre count is exactly what our framework lacks.

**Candidate route W (please audit).** Work at the finite places under a coordinate-ring
witness; let B ⊂ places(E₂) be a finite bad set: the ramified places, the poles of the
witness data, and the image of O.
1. (T3) For Q ∉ B: Σ_{P over Q} e_P·f_P = deg φ, and f_P = 1 (algebraically closed).
2. **(NEW — the crux)** Separability of K(E₁)/φ*K(E₂) implies all but finitely many
   places of E₂ are unramified in K(E₁). Then for Q ∉ B: #{places over Q} = deg φ.
3. (Mostly built) Places of K(E₁) over Q correspond bijectively to points P ∈ E₁ with
   φ(P) = Q (the smooth-point ↔ maximal-ideal dictionary; lying-over supplies the
   points, so these fibres are automatically nonempty; this machinery was built for
   II.3.6). Hence #φ⁻¹(Q) = deg φ for Q ∉ B. Conclude by T2.

The genuinely new content is step 2 — "separable ⟹ almost everywhere unramified" for an
extension of curve function fields, in a Dedekind-ring formulation our coordinate rings
satisfy. Our proof-assistant library has the **different ideal** (𝔡 of a module-finite
extension of Dedekind domains, with its basic theory), suggesting: 𝔡 ≠ 0 for a separable
extension; ramified primes divide 𝔡; hence finitely many. Alternatives we see: the
discriminant of the minimal polynomial of a primitive element z (separable ⟹ disc ≠ 0;
ramified places away from the poles of z divide it); or a derivative criterion
(e_P > 1 at good P forces P | g′(z) for the minimal polynomial g of z).

## 4. Secondary gaps (smaller questions)

**G1 (II.2.12 existence).** Our factorization φ = φ_sep ∘ πʳ currently *takes as input*
the inclusion Im(φ*) ⊆ Im((πʳ)*) = K(E)^{qʳ}. The missing existence statement is: for
inseparable φ, Im(φ*) ⊆ K(E)^p. We already know "φ separable ⟺ the differential
pullback is nonzero" (the invariant-differential coefficient a_φ). The classical route:
dφ* = 0 forces Im(φ*) ⊆ ker(d), and **ker(d : K(E) → Ω¹) = K(E)^p** for the function
field of a curve in characteristic p. Is there a low-machinery proof of that kernel
computation (or a better route to G1) — e.g. direct computation in K(E) = F(x)[y] with
d on the basis {1, y} and the Weierstrass relation?

**G2 (the twist).** For an endomorphism over 𝔽_q whose inseparable degree p^k is *not*
a power of q (e.g. inseparable degree p over 𝔽_{p²}), the factorization passes through
the Frobenius twist E^{(p)} ≠ E. We believe constructing E^{(p)} (coefficient p-th
powers), its ellipticity, and the relative p-power Frobenius is routine in our two-curve
framework, and note that [p]-multiples are already covered by [n]^ = [n]. Is there a
hidden subtlety — or an argument avoiding the twist entirely for the *dual-existence*
question over 𝔽_q?

**G3 (architecture sanity).** The dual is organized witness-parametrically: per isogeny,
a package (range inclusion Im([deg φ]*) ⊆ Im(φ*); ∞-regularity reflection — now free;
the regularity of [deg φ] — now free) from which the dual morphism and the identity
φ̂∘φ = [deg φ] are *constructed*. Uniqueness (∃!) and the III.6.2 layer (φ̂̂ = φ,
additivity of the dual) are not yet attempted. Any integrity concern with
witness-parametric duals as the long-term shape, before we invest in III.6.2?

## 5. Questions

> **Q1 (the main one).** For the Wall: is route W (§3, steps 1–3) the right
> formalization-grade proof of #ker = deg for separable φ? For step 2 — "separable ⟹
> all but finitely many places unramified" — which formulation is cheapest in a Dedekind
> setting: (a) the different ideal (𝔡 ≠ 0 for separable; ramified ⟹ divides 𝔡), which
> our library already provides; (b) the discriminant of a primitive element; (c) a
> derivative criterion at a primitive element, avoiding ideal machinery? Any pitfalls at
> the excised places (witness poles, the image of O, the ramified locus) — in particular
> anything beyond "the good set is nonempty because E₂ has infinitely many places"
> (which we have)?

> **Q2.** Is there a route to the count that avoids the generic-fibre argument entirely
> — e.g. proving *surjectivity* of ker φ → Aut(K(E₁)/φ*K(E₂)) directly (a Galois-descent
> argument not presupposing the count), or a duality/degree-pairing trick using the
> already-constructed dual apparatus (V∘π = [q], [n]^ = [n], faithful composition) to
> bootstrap the count for general separable φ from the known cases? We suspect not
> (Silverman's III.4.10b surjectivity *uses* the count), but a cheaper bootstrap would
> change our plan.

> **Q3.** For G1: the cleanest proof of ker(d) = K^p for the function field of a curve
> in characteristic p at our machinery level — direct computation in F(x)[y] with the
> Weierstrass relation, or general 1-form theory? And is Im(φ*) ⊆ K^p for inseparable φ
> best obtained via dφ* = 0, or is there a more elementary route?

> **Q4.** For G2: confirm the twist construction is routine (or name the subtlety), and
> whether dual-existence over 𝔽_q can dodge the twist.

> **Q5 (meta).** Priorities: attack the Wall now (route W; the e/f machinery exists and
> step 2 is the only new piece), or first finish the III.6.2 layer (φ̂̂ = φ, additivity)
> witness-parametrically, or consolidate? Given the goal — isogeny classes as the
> foundation for an LMFDB-style catalogue — what ordering would you take?

## 6. Status summary

| Component | Status |
|---|---|
| Hasse bound (rounds 1–23 programme) | done, machine-checked, no unproven inputs |
| III.4.8 (isogeny = group hom) | **done** (Pic⁰ + norm–conorm II.3.6) |
| Tate module: E[ℓⁿ] ≅ (ℤ/ℓⁿ)², T_ℓ ≅ ℤ_ℓ², ρ_ℓ → GL₂(ℤ_ℓ) | **done** |
| Isogeny-class relation: reflexivity, transitivity | done |
| Fibres are kernel torsors (one good fibre ⟹ all) | done |
| Σ e·f = deg per place; f = 1 over K̄; ord_∞ formula with e ≥ 1 | done |
| Fixed field = image (given covariance + count); circularity mapped | done |
| Covariance for general isogenies (coordinate witness, over K̄) | done |
| [n] an isogeny for all n ≠ 0 (incl. p | n); [n]^ = [n] | done |
| π̂ = V (constructed), V∘π = [q]; faithful composition of duals | done |
| Arbitrary dual reduced to the separable part (q-power case) | done |
| **#ker = deg for general separable φ (III.4.10c)** | **the Wall — §3** |
| II.2.12 existence; ker d = K^p; the twist | open (G1, G2) |
| III.6.2 layer (φ̂̂ = φ, dual additivity); conductor theory | not attempted |

## 7. Document metadata

- Project: Silverman continuation (isogeny foundations, Tate module, dual isogeny) on
  top of the completed Hasse-bound formalization; Lean 4 / Mathlib.
- Brief: round 24, 2026-06-10. Continues rounds 1–23; round 23's reply (Route B) is
  integrated and the bound is complete.
- Build status: everything compiles; the only unproven statement in the dual programme
  is the universal witness whose mathematical content is the Wall (plus the named G1/G2
  inputs, carried as explicit hypotheses where used).
- Core ask: §5 — Q1 (route W and the cheapest almost-everywhere-unramifiedness), with
  Q2 as the shortcut audit.
- References: Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106 —
  II.2.6, II.2.11–12, II.4.2, III.4.8–4.12, III.6.1–6.2; Hartshorne, *Algebraic
  Geometry*, GTM 52 — II.6.8–6.9 (for the generic-fibre count Silverman cites).
  Prior replies rounds 16–23 (this conversation).
