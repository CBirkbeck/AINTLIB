# [T-E5-KM47] KM 4.7 quote pass — verbatim source of record

Read 2026-07-08 by fable-P4 from `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`
(scanned; no text layer — read as page images. **Offset: pdf page = book page + 11.**)

| what | book pp. | pdf pp. |
|---|---|---|
| §4.6.2 (Legendre moduli problem) | 111 | 122 |
| **§4.7 A basic result: representability and rigidity** | 111–117 | 122–128 |
| SCHOLIE (4.7.0) + proof | 111–116 | 122–127 |
| COROLLARY 4.7.1 / 4.7.2 | 116–117 | 127–128 |
| APPENDIX (A.4) More on rigidity and representability | 125–128 | 136–139 |
| Loeffler §3.6–3.7 | pp. 17–18 of `modcurvesnotes.pdf` (text layer) | — |

---

## 1. KM SCHOLIE (4.7.0) — book p. 111 (pdf 122), §4.7

> **SCHOLIE (4.7.0)** *Let 𝒫 be relatively representable and affine over* (Ell); *then a
> necessary and sufficient condition that 𝒫 be representable is that 𝒫 be rigid.*
>
> *Proof.* As already pointed out above (4.4), any representable problem is automatically
> rigid. Conversely, suppose 𝒫 is rigid, relatively representable and affine. We must show
> it is represented, by an
>
>   E, α_univ ∈ 𝒫(E/𝕸(𝒫)) ↓ 𝕸(𝒫)
>
> where 𝕸(𝒫) is an affine ℤ-scheme. For this, it suffices to show that 𝒫 is separately
> representable over both ℤ[1/2] and over ℤ[1/3], (the rigidity of 𝒫 will then provide a
> unique isomorphism between the restrictions to ℤ[1/6] of the representing objects, giving
> a representing object over ℤ by "recollement").
>
> To show the representability separately over ℤ[1/2] and ℤ[1/3], we will make use of the
> Legendre and the naive level three moduli problems discussed in 4.6 above. To clarify the
> argument, we will axiomatize it.

## 2. The axiomatized engine — book p. 112 (pdf 123)

> Let N ≥ 1 be an integer, G a finite group, and δ a relatively representable and affine
> moduli problem on (Ell) which satisfies the following axioms:
>
> 1) δ is representable, by an affine ℤ[1/N]-scheme
> 2) G operates upon δ, in such a way that for every elliptic curve E/S with S a
>    ℤ[1/N]-scheme, the S-scheme δ_{E/S} is a finite etale G-torsor.
>
> We claim that over ℤ[1/N], 𝒫 is represented by the affine ℤ[1/N]-scheme
>
>   𝕸(𝒫, δ)/G .
>
> Once we have verified this claim, we simply apply it successively with (N = 2, δ =
> Legendre problem, G = GL(2, ℤ/2ℤ) × {±1}) and with (N = 3, δ = naive level three problem,
> G = GL(2, 𝔽₃)).

### Proof of the claim (book pp. 112–116, pdf 123–127), step by step

> (i) **Simultaneous problem.** "Because δ is representable, and 𝒫 is relatively
> representable, the simultaneous problem (𝒫, δ) is representable, by 𝕸(𝒫, δ) =
> 𝒫_{E/𝕸(δ)}. Because 𝕸(δ) is affine, and 𝒫 is affine over (Ell), the scheme 𝕸(𝒫, δ) is
> affine over 𝕸(δ), hence absolutely affine. Let G operate upon 𝕸(𝒫, δ) through its action
> on δ." (p. 112)

> (ii) **The one-cocycle θ.** "The action of g ∈ G on 𝕸(𝒫, δ) is defined as follows; the
> curve E, with (α_univ, gβ_univ) […] is an elliptic curve with (𝒫, δ)-structure over
> 𝕸(𝒫, δ), so it is 'classified' by a unique morphism g : 𝕸(𝒫, δ) → 𝕸(𝒫, δ), for which we
> have an isomorphism g*(E, α_univ, β_univ) —θ(g)→ (E, α_univ, gβ_univ) over 𝕸(𝒫, δ).
> Forgetting β_univ, θ(g) defines an 𝕸(𝒫, δ)-isomorphism θ(g) : g*(E, α_univ) ≅
> (E, α_univ). **Because the moduli problem 𝒫 is rigid, the object (E, α_univ) has no
> non-trivial automorphisms.** Therefore θ(g) is the unique 𝕸(𝒫, δ)-isomorphism between
> g*(E, α_univ) and (E, α_univ). By uniqueness, θ must be compatible with composition of
> elements of G, (i.e., g ↦ θ(g) is a one-cocycle)." (p. 113)

> (iii) **Free action, quotient, torsor.** "By axiom 2) and the rigidity of 𝒫, G operates
> freely on 𝕸(𝒫, δ). **Because 𝕸(𝒫, δ) is affine, the quotient 𝕸(𝒫, δ)/G exists**, and the
> projection π_univ : 𝕸(𝒫, δ) → 𝕸(𝒫, δ)/G is a finite etale G-torsor [De-Ga III, 2,6.1]
> (SGA III, Exp V, 4.1)." (p. 113)

> (iv) **Descent.** "Because g ↦ θ(g) is compatible with composition, θ is descent data for
> (E, α_univ) relative to this projection. Because E is projective, via I⁻¹(0), it descends,
> and because 𝒫 is relatively affine, α_univ descends (SGA I, Exp VIII, 7.8, 1.2 and 1.7).
> Thus we obtain an object E₀, α_univ,₀ ∈ 𝒫(E₀/(𝕸(𝒫, δ)/G)) […] whose pull-back to
> 𝕸(𝒫, δ) is the original (E, α_univ)." (pp. 113–114)

> (v) **(E₀, α_univ,₀) represents 𝒫.** "Let S be a ℤ[1/N]-scheme, and (E/S, α ∈ 𝒫(E/S)) an
> elliptic curve over S with level 𝒫-structure. We must show that it is induced from
> (E₀, α_univ,₀) by a unique map S → 𝕸(𝒫, δ)/G. For this, consider the finite etale
> G-torsor δ_{E/S} →π S, over which E acquires its universal level δ-structure β_univ. The
> classifying map for (E ×_S δ_{E/S}, α, β_univ) is a map f : δ_{E/S} → 𝕸(𝒫, δ) which is
> (tautologically) G-equivariant. Passing to quotients by G yields a map f₀ […] Because the
> vertical arrows are finite etale G-torsors, the G-equivariance of f guarantees that this
> diagram is cartesian." (pp. 114–115)
>
> "To establish a), we note that because 𝒫 is rigid, and π is etale and surjective, it
> suffices to show that on δ_{E/S}, π*f₀*(E₀, α_univ,₀) is isomorphic to π*(E, α). But this
> is clear from the commutativity of the above diagram, and the definition of f." (p. 115)
>
> "[…] is necessarily an isomorphism (being a G-map between G-torsors). Therefore we have a
> cartesian diagram of G-torsors […] and an isomorphism h*(E_univ, α_univ, β_univ) ≅
> (E, α, β_univ) over δ_{E/S}. Therefore h = f, since both classify (E, α, β_univ) over
> δ_{E/S}. From the equality h = f, we deduce h₀π = f₀π, whence h₀ = f₀ because π is etale
> and surjective. Q.E.D." (p. 116)

## 3. Corollaries — book pp. 116–117 (pdf 127–128)

> **COROLLARY 4.7.1.** *Any relatively representable moduli problem 𝒫 which is affine and
> etale over* (Ell), *and rigid, is representable by a smooth affine curve over* ℤ.
>
> *Proof.* By 4.7.0, 𝒫 is representable by an affine, and we have
> 𝕸(𝒫) ⊗ ℤ[1/2] = 𝕸(𝒫, Legendre)/(a finite group acting freely),
> 𝕸(𝒫) ⊗ ℤ[1/3] = 𝕸(𝒫, naive level 3)/(a finite group acting freely).
> Therefore it suffices to prove that 𝕸(𝒫, Legendre) is a smooth curve over ℤ[1/2], and
> that 𝕸(𝒫, naive level 3) is a smooth curve over ℤ[1/3]. By hypothesis, 𝒫 is etale over
> (Ell), so that the morphisms 𝕸(𝒫, Legendre) → 𝕸(Legendre), 𝕸(𝒫, naive level 3) →
> 𝕸(naive level 3) are *etale*. This reduces us to checking that 𝕸(Legendre) and 𝕸(naive
> level three) are both smooth curves over ℤ, a fact which is obvious by inspection of their
> explicit defining equations (2.2.9, 2.2.11). Q.E.D.

> **COROLLARY 4.7.2.** *For N ≥ 3, the naive level N moduli problems of 4.6 is
> representable, by a smooth affine curve* Y(N) *over* ℤ[1/N].
>
> *Proof.* This results from 4.7.1 above, thanks to the rigidity 2.7.2 and the relative
> representability 3.7.1 of naive level N structures. Q.E.D.

## 4. The Legendre problem, verbatim — KM (4.6.2), book p. 111 (pdf 122)

> **(4.6.2)** Another example of a moduli problem 𝒫 which is etale over (Ell) is the
> Legendre moduli problem 2.2.9
>
>   E/S ↦ pairs (φ₂, ω) consisting of an S-group-scheme isomorphism
>   φ₂ : (ℤ/2ℤ)² ≅ E[2] together with an S-basis ω of ω_{E/S} for which the adapted x
>   satisfies x(P₂) = 0, x(Q₂) = 1.
>
> The corresponding S-scheme 𝒫_{E/S} is concentrated over S[1/2], over which it is a finite
> etale GL(2, ℤ/2ℤ) × {±1} torsor.

## 5. APPENDIX (A.4) — book pp. 125–128 (pdf 136–139)

> **(A.4.1)** Let R be a ring, 𝒫 a moduli problem on (Ell/R), and 𝒫̃ the contravariant
> functor on (Sch/R) defined by (cf. 4.3.1)
> **(A.4.1.1)** S/R ↦ isomorphism classes of pairs (E/S, α) with E an elliptic curve over S
> and α ∈ 𝒫(E/S) a "level 𝒫 structure" on E/S.
>
> It is a tautology that
> **(A.4.1.2)** 𝒫 is representable ⟺ { 𝒫̃ is representable *and* 𝒫 is rigid }.
>
> However, it is *not* in general true that 𝒫̃ representable ⟹ 𝒫 rigid.
>
> Here is a simple counterexample, due to Ofer Gabber. At the expense of Zariski-localizing
> on Spec(R), we may suppose that there exists an elliptic curve over R. Fix one, say E₀/R,
> and define a moduli problem 𝒫 on (Ell/R) by defining
> **(A.4.1.3)** 𝒫(E/S) = { the set with one element, if E/S is S-isomorphic to E₀/S; the
> empty set, if not. }
> This 𝒫 is not rigid (because the automorphism −1 acts trivially), but the associated
> functor 𝒫̃ is visibly representable (by Spec(R) itself!).

> **PROPOSITION (A.4.2).** *Let R be a ring, and 𝒫 a moduli problem on* (Ell/R). *Suppose
> that for every R-scheme S and for every elliptic curve E/S, the contravariant functor on*
> (Sch/S) *defined by (cf. 4.2) T ↦ 𝒫(E_T/T) is an etale sheaf on* (Sch/S). *(N.B. This
> condition is automatically satisfied if 𝒫 is relatively representable.) Then the following
> conditions are equivalent.*
>
> (1) 𝒫̃ *is representable.*
> (2) 𝒫̃ *is representable, and* 𝒫 *is rigid.*
> (3) 𝒫 *is representable.*
>
> [Proof, pp. 126–128: (2)⟺(3) is "mise pour memoire"; (1)⟹(2) by contradiction — a
> non-rigid 𝒫 yields E/S, α, g ≠ id with g*(α) = α; by rigidity (2.4.2) a geometric point
> s with g_s ≠ id on E_s; by (2.7.2) g_s has finite order d ≥ 2; a cyclic Galois twist
> E₂/K of E₁/K by g₁ produces two pairs (E₁/K, α₁), (E₂/K, α₂) that are not K-isomorphic
> but become isomorphic over L — two distinct elements of 𝒫̃(K) becoming equal in 𝒫̃(L),
> contradicting representability since X(K) → X(L) is always injective.]

## 6. Loeffler, `modcurvesnotes.pdf` §3.7 (p. 18) — the project's current statement

> **Definition 3.7.1.** […] (3) We say that P is *representable* if it is representable; it
> is *relatively representable* if, for every E/S ∈ Ob(Ell/R), the functor Sch/S → Set,
> T ↦ P(E ×_S T /T) is representable.
>
> **Proposition 3.7.2.** For P a moduli problem, let P̃ : Sch/R → Set be the functor
> P̃ : S ↦ {pairs (E, α), E/S elliptic curve, α ∈ P(E/S)}. If P is representable on Ell/R,
> then P̃ is representable on Sch/R.
> *Remark.* The converse is not quite true.
>
> **Definition 3.7.3.** P is *rigid* if for all E/S ∈ Ob(Ell/R), Aut(E/S) acts on P(E/S)
> without fixed points.
>
> **Exercise.** (1) Any representable functor is rigid; (2) if P is rigid and P̃ is
> representable, then P is representable.
>
> **Theorem 3.7.4.** (Katz–Mazur) *P is representable if and only if it is relatively
> representable and rigid.*
>
> *Proof.* (Sketch) Start from two basic moduli problems: 'naive level Γ(3)' over ℤ[1/3];
> 'Legendre moduli problem' (Γ(2) with choice of differential) over ℤ[1/2]. Both have group
> actions (GL₂(𝔽₃) and GL₂(𝔽₂) × {±1}). Given P relatively representable and rigid,
> construct one object by taking E/Y(3) — relative representability gives us a scheme over
> Y(3) — and this has a GL₂(𝔽₃)-action. **Take invariants (this is OK since P is rigid)**,
> so we get an object E/S representing P on Ell/R[1/3]. Legendre gives an object over R[1/2]
> similarly. By rigidity these agree over R[1/6], so we get a representing object over R.

> **Proposition 3.6.1.** Let X be a **quasiprojective** S-scheme (for some base scheme S),
> and let G be a finite group acting […] there exists a unique S-scheme X/G […] for
> X = Spec(A) affine, Spec(A^G) works.

---

## 7. RECONCILIATION: Lean ↔ source, and the STATEMENT MISMATCH (flagged, not fixed)

Our decl (`Moduli/EllCategory.lean`):

```lean
theorem representable_iff (P : ModuliProblem R) :
    P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid
```

**Match, term by term.** `ModuliProblem R = (EllObj R)ᵒᵖ ⥤ Type u` is KM's "moduli problem on
(Ell/R)" = Loe Def 3.7.1(2) (contravariant functor on Ell/R). `Representable = P.IsRepresentable`
is KM's "𝒫 is representable" (the functor on (Ell/R) is representable) — **not** 𝒫̃, which is a
functor on (Sch/R) and which our formalization does not yet have. `RelativelyRepresentable` is
KM 4.2 / Loe 3.7.1(3) (with our added naturality clause, which KM leaves implicit). `Rigid` is
KM 4.4 / Loe Def 3.7.3 verbatim ("Aut(E/S) acts on P(E/S) without fixed points"). Our statement
is therefore *Loeffler's Theorem 3.7.4 verbatim*.

**⚠️ MISMATCH (statement risk, T-E5 owner decision — flagged per dispatch, NOT fixed):**

1. **KM's SCHOLIE (4.7.0) carries a hypothesis our statement does not have: 𝒫 is
   "relatively representable *and affine over* (Ell)".** Loeffler's Thm 3.7.4 drops it. The
   affineness is *load-bearing twice* in KM's proof, not decorative:
   - p. 112, step (i): "Because 𝕸(δ) is affine, and 𝒫 is affine over (Ell), the scheme
     𝕸(𝒫, δ) is affine over 𝕸(δ), **hence absolutely affine**";
   - p. 113, step (iii): "**Because 𝕸(𝒫, δ) is affine, the quotient 𝕸(𝒫, δ)/G exists**".
   Without it the free quotient of a scheme by a finite group need not be a scheme (it is an
   algebraic space). Loeffler's own quotient input, his Prop 3.6.1, is stated only for
   **quasiprojective** X — so even his sketch's "take invariants" step tacitly needs a
   hypothesis he never states in 3.7.4. Note also KM's step (iv) uses "𝒫 is **relatively
   affine**" a third time, to descend α_univ (SGA I VIII 7.8).
   ⟹ **The Lean `representable_iff` as stated is not supported by either source's proof.**
   The honest options (T-E5 pickup):
   (a) **KM-honest**: add `P.AffineOverEll` (relative representability *by affine* S-schemes)
       to the ⇐ direction. Loses nothing downstream: every consumer (T-E9's `P_H`, T-H4/T-H6,
       T-E7) is affine-over-Ell — indeed KM 4.7.1/4.7.2 and Loe 3.8.2 all carry
       "affine and étale over (Ell)".
   (b) Weaken to quasi-projective-over-Ell and pay for Loe 3.6.1 in that generality (T-Q5).
   (c) Keep the general statement and route through algebraic spaces — **out of scope** (no
       algebraic-space theory in mathlib).
   *Recommendation: (a), with the ⇒ direction left hypothesis-free.*

2. **The ⇒ direction is not "free" either.** KM 4.4 gives representable ⟹ rigid (Loe Exercise
   (1)). But representable ⟹ **relatively** representable requires the Isom-scheme of the
   universal curve: for `E/S`, `T ↦ 𝒫(E_T/T) ≅ Hom_{Ell}(E_T/T, E_univ/𝕸(𝒫))` and one must
   exhibit this as a scheme over `S`. KM never states this implication separately (it is
   implicit in 4.3); Loeffler asserts it inside 3.7.4. ⟹ own leaf, own gap ticket.

3. **`𝒫̃` is absent from our formalization**, so KM (A.4.1.2)/(A.4.2) and Loe 3.7.2 + Exercise
   (2) — the cheapest route to the ⇐ direction *given* `𝒫̃` representable — are currently
   unstatable. Gabber's counterexample (A.4.1.3) shows `𝒫̃`-representability is strictly
   weaker than `𝒫`-representability, so `𝒫̃` is genuinely a second object, not a synonym.
   ⟹ cut `[T-E5c]` (define `𝒫̃`) only if route (A.4.2) is chosen; the bootstrap route
   (4.7.0) does not need it.
