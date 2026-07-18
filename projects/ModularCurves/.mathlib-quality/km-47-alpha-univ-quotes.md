# [PHASE B source of record] KM 4.7.0 proof — α_univ-descent + the representability bijection, verbatim

Read 2026-07-10 by fable-P4 from `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`
(scanned, read as page images). **Offset: pdf page = printed page + 11.** Chapter 4 "The
formalism of moduli problems", the proof of THEOREM 4.7.0 — printed pp. 113–116 = pdf pp. 124–127.
(The 4.7.0 statement itself and the θ-cocycle setup open on printed p. 112–113; the quotes below
start where the descent argument begins.)

## (p. 113) The θ-cocycle, freeness, and the torsor

> E, with (α_univ, gβ_univ) [over] 𝕸(𝒫,δ) is an elliptic curve with (𝒫,δ)-structure over
> 𝕸(𝒫,δ), so it is "classified" by a unique morphism
>
>   g : 𝕸(𝒫,δ) → 𝕸(𝒫,δ),
>
> for which we have an isomorphism
>
>   g*(E, α_univ, β_univ) —θ(g)→ (E, α_univ, gβ_univ)
>
> over 𝕸(𝒫,δ). Forgetting β_univ, θ(g) defines an 𝕸(𝒫,δ)-isomorphism
>
>   θ(g) : g*(E, α_univ) ≅ (E, α_univ).
>
> Because the moduli problem 𝒫 is *rigid*, the object (E, α_univ) has no non-trivial
> automorphisms. Therefore θ(g) is the unique 𝕸(𝒫,δ)-isomorphism between g*(E, α_univ) and
> (E, α_univ). By *uniqueness*, θ(g) must be compatible with composition of elements of G,
> (i.e., g ↦ θ(g) is a one-cocycle).
>
> By axiom 2) and the rigidity of 𝒫, G operates freely on 𝕸(𝒫,δ). Because 𝕸(𝒫,δ) is affine,
> the quotient 𝕸(𝒫,δ)/G exists, and the projection
>
>   π_univ : 𝕸(𝒫,δ) → 𝕸(𝒫,δ)/G
>
> is a finite etale G-torsor [De-Ga III, 2.6.1] (SGA III, Exp V, 4.1). Because g ↦ θ(g) is
> compatible with composition, θ is descent data for

## (p. 114) THE DESCENT STEP (E and α_univ descend) — the two sentences our Phase A/B replace

> (E, α_univ) relative to this projection. Because E is projective, via I⁻¹(0), it descends,
> and because 𝒫 is relatively affine, α_univ descends (SGA I, Exp VIII, 7.8, 1.2 and 1.7).
> Thus we obtain an object
>
>   E₀, α_univ,0 ∈ 𝒫(Ell(𝕸(𝒫,δ)/G))  [an elliptic curve E₀ over 𝕸(𝒫,δ)/G with 𝒫-structure]
>
> whose pull-back to 𝕸(𝒫,δ) is the original (E, α_univ).

[Phase A = "Because E is projective … it descends" WITHOUT SGA VIII 7.8 (route (a):
`exists_ellipticCurveGeom_quotient_of_globalModel`). Phase B first target = "because 𝒫 is
relatively affine, α_univ descends".]

## (p. 114) The representability claim and the δ-torsor

> It remains to show that (E₀, α_univ,0) over 𝕸(𝒫,δ)/G does in fact represent 𝒫 over ℤ[1/N].
> Let S be a ℤ[1/N]-scheme, and (E/S, α ∈ 𝒫(E/S)) an elliptic curve over S with level
> 𝒫-structure. We must show that it is induced from (E₀, α_univ,0) by a unique map
> S → 𝕸(𝒫,δ)/G. For this, consider the finite etale δ-torsor over S
>
>   π : δ_{E/S} → S,
>
> over which E acquires its universal level δ-structure β_univ. The classifying map for
> (E ×_S δ_{E/S}, α, β_univ) is a map
>
>   f : δ_{E/S} → 𝕸(𝒫,δ)
>
> which is (tautologically) G-equivariant. Passing to quotients by G yields a map f₀ which
> sits in a commutative diagram

## (p. 115) The cartesian square, existence a), and the uniqueness setup

> [diagram: δ_{E/S} —f→ 𝕸(𝒫,δ); π ↓ … ↓ π_univ; S —f₀→ 𝕸(𝒫,δ)/G]
>
> Because the vertical arrows are finite etale G-torsors, the G-equivariance of f guarantees
> that this diagram is cartesian.
>
> We must show that a), f₀*(E₀, α_univ,0) is isomorphic to (E, α), and that b), f₀ is the
> unique map of S to 𝕸(𝒫,δ)/G for which this is true. To establish a), we note that because
> 𝒫 is *rigid*, and π is etale and surjective, it suffices to show that on δ_{E/S},
> π*f₀*(E₀, α_univ,0) is isomorphic to π*(E, α). But this is clear from the commutativity of
> the above diagram, and the definition of f.
>
> To show the uniqueness of f₀ we argue as follows. Let
>
>   h₀ : S → 𝕸(𝒫,δ)/G
>
> be any morphism for which h₀*(E_univ,0, α_univ,0) ≅ (E/S, α), and denote by X the
> fiber-product
>
> [diagram: X —h→ 𝕸(𝒫,δ); ↓ … ↓ π_univ; S —h₀→ 𝕸(𝒫,δ)/G.]
>
> Then X/S is a G-torsor, and the pull-back to X of (E/S, α) acquires an δ-structure β. The
> resulting G-equivariant S-morphism which classifies this δ-structure

## (p. 116) Uniqueness b) closes; COROLLARY 4.7.1

> [diagram: X → δ_{E/S} over S]
>
> is necessarily an isomorphism (being a G-map between G-torsors). Therefore we have a
> cartesian diagram of G-torsors
>
> [diagram: δ_{E/S} —h→ 𝕸(𝒫,δ); π ↓ … ↓ π_univ; S —h₀→ 𝕸(𝒫,δ)/G]
>
> and an isomorphism h*(E_univ, α_univ, β_univ) ≅ (E, α, β_univ) over δ_{E/S}. Therefore
> h = f, since both classify (E, α, β_univ) over δ_{E/S}. From the equality h = f, we deduce
> h₀π = f₀π, whence h₀ = f₀ because π is etale and surjective. Q.E.D.
>
> COROLLARY 4.7.1. *Any relatively representable moduli problem 𝒫 which is affine and etale
> over (Ell), and rigid, is representable by a smooth affine curve over ℤ.*
>
> *Proof.* By 4.7.0, 𝒫 is representable by an affine, and we have
>
>   𝕸(𝒫) ⊗ ℤ[1/2] = 𝕸(𝒫, Legendre) / (a finite group acting freely)
>   𝕸(𝒫) ⊗ ℤ[1/3] = 𝕸(𝒫, naive level 3) / (a finite group acting freely).
>
> Therefore it suffices to prove that 𝕸(𝒫, Legendre) is a smooth curve over ℤ[1/2], and that
> 𝕸(𝒫, naive level 3) is a smooth curve over ℤ[1/3]. By hypothesis, 𝒫 is etale over (Ell),
> so that the morphisms […]

## Reconciliation → the Phase-B decomposition (route (a) dialect)

* KM's two descent sentences split: **E-descent** = Phase A's engine (DONE, axiom-clean;
  quotient-construction instead of SGA VIII 7.8 — `E₀ := E/G`, and the pullback statement *is*
  our cartesian square `IsPullback q C.π C'.π quotientπ`). **α_univ-descent** = "𝒫 relatively
  affine ⟹ α descends": in our stack, rel-rep gives `𝒫_{E/X}` affine over `X`; `α` is a section
  `X → 𝒫_{E/X}`; the θ-compatibility makes it `G`-equivariant; the descended section is produced
  by the **quotient universal property** (`exists_quotientπ_lift`, T-Q5 — PROVEN) against the
  base-change identification `𝒫_{E₀/(X/G)} ×_{X/G} X ≅ 𝒫_{E/X}` (rel-rep base-change + Phase A's
  cartesian square). No SGA 1.2/1.7 needed.
* The **δ-torsor** `δ_{E/S}` is the rel-rep scheme of the auxiliary problem `δ` at `E/S`
  (finite étale since `δ` is); `β_univ` is its tautological point.
* The **cartesian-square lemma** (p. 115, "G-equivariance ⟹ cartesian" for a G-equivariant map
  of finite étale G-torsors over `S → S'`) and the **G-torsor-map-is-iso** lemma (p. 116) are the
  two reusable torsor facts.
* **Rigidity is used twice**: uniqueness of θ (making it a cocycle — Phase A consumed this via
  `pointedIso_exists_variableChange`-uniqueness) and the étale-descent of the isomorphism in a)
  (reduce an iso-check to a surjective étale cover — needs the rel-rep sheaf/rigidity apparatus).
