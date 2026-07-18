# [B2 EVENT #2 / T-H4·T-H6 repoint] KM Chapter 7 §7.1 — the quotient problem, verbatim

Source of record for the T-H4/T-H6 repoint (b2_log.jsonl entries dated 2026-07-09). Read
2026-07-09 by fable-P4 from `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (scanned,
read as page images). **Offset: pdf page = printed page + 11.** Chapter 7 "QUOTIENTS BY FINITE
GROUPS", §7.1 "The general situation" — printed pp. 186–188 = pdf pp. 197–199.

`P_H` is **defined** here as the quotient moduli problem `[Γ(N)]/H` — NOT as naive global
`H`-orbits. The naive-orbit presheaf `gammaHNaiveProblem R N H` is not a Zariski/fppf sheaf and is
therefore *not* relatively representable for `H ≠ ⊥` (refuted:
`gammaHNaiveProblem_not_relativelyRepresentable`); this is the transcription slip the repoint fixes.

## (7.1.1) — the action (printed p. 186)

> **(7.1.1)** Let `R` be a ring, `G` a finite group, and `𝒫` a moduli problem on `(Ell/R)`. We say
> that `G` operates on `𝒫` if for every `R`-scheme `S`, and every elliptic curve `E/S`, the group
> `G` operates on the set `𝒫(E/S)` in such a way that for every morphism in `(Ell/R)`, viewed as a
> Cartesian diagram [`E₁ →ᵃ E` over `S₁ →ᶠ S`], the obvious diagram of actions below commutes:
> [`G × 𝒫(E/S) → 𝒫(E/S)` and `G × 𝒫(E₁/S₁) → 𝒫(E₁/S₁)` intertwined by `id × (α,f)*` and `(α,f)*`].
> If `𝒫` is relatively representable, then for every `E/S`, the group `G` acts on the `S`-scheme
> `𝒫_{E/S}`.

## (7.1.2) — the quotient problem 𝒫/G (printed pp. 186–187)

> **(7.1.2)** Let `𝒫` and `𝒫'` be two relatively representable moduli problems on which `G`
> operates, and let `𝒫 → 𝒫'` be a `G`-equivariant morphism of moduli problems on `(Ell/R)`; for
> every `E/S/R`, we are given a `G`-equivariant map of `G`-sets `𝒫(E/S) → 𝒫'(E/S)` compatible with
> morphisms in `(Ell/R)`. We say that `𝒫'` is **"the" quotient of `𝒫` by `G`**, and write
> `𝒫' = 𝒫/G`, if the following two conditions hold:
>
> - **(Q1):** `G` operates trivially on `𝒫'`.
> - **(Q2):** For every representable moduli problem `δ` on `(Ell/R)` which is étale over `(Ell/R)`,
>   the quotient scheme `𝕸(δ, 𝒫)/G` exists, and it maps isomorphically to `𝕸(δ, 𝒫')`.
>   [Equivalently: for every modular family of elliptic curves `E/S/R`, the quotient scheme
>   `(𝒫_{E/S})/G` exists, and maps isomorphically to `(𝒫'_{E/S})`.]

## THEOREM 7.1.3 (printed pp. 187–188)

> **THEOREM 7.1.3.** Let `𝒫` be relatively representable and affine over `(Ell/R)`, and `G` a finite
> group acting on `𝒫`. Then
>
> **(1)** The quotient `𝒫/G` exists as a relatively representable moduli problem, affine over
> `(Ell/R)`, with trivial `G`-action. For any relatively representable `𝒫'`, any `G`-equivariant map
> `𝒫 → 𝒫'` factors uniquely through the projection `𝒫 → 𝒫/G`, so that `𝒫/G` represents the covariant
> functor on the category of all relatively representable moduli problems with trivial `G`-action
> defined by `𝒫' ↦ Hom_{G-equiv}(𝒫, 𝒫')`.
>
> **(2)** If `G` operates freely on `𝒫`, in the sense that for every `E/S/R`, `G` operates freely on
> the set `𝒫(E/S)`, then `𝒫` is an **étale `G`-torsor over `𝒫/G`**; for every `E/S/R`, `G` operates
> freely on the `S`-scheme `𝒫_{E/S}`, `𝒫_{E/S}` is an étale `G`-torsor over `(𝒫/G)_{E/S}`, and
> `(𝒫_{E/S})/G ≅ (𝒫/G)_{E/S}`.
>
> **(3)** For any `E/S/R`, the quotient scheme `𝒫_{E/S}/G` exists, and there is a natural
> `S`-morphism `(𝒫_{E/S})/G → (𝒫/G)_{E/S}`, which is bijective on geometric points. It is an
> isomorphism if any of the following conditions hold: (a) `E/S` is (as representable moduli problem)
> flat over `(Ell/R)`; (b) the order of `G` is invertible on `S`; (c) `G` operates freely on `𝒫`.
>
> **(4)** The morphism `𝒫 → 𝒫/G` is **finite**.
>
> **(5)** If `𝒫` is normal, so is `𝒫/G`.
>
> **(6)** If `𝒫` is finite over `(Ell/R)` and `R` is noetherian, then `𝒫/G` is finite over `(Ell/R)`.

## Reconciliation → the corrected T-H4 / T-H6

* `P_H := [Γ(N)]/H`, with `Γ(N)` = naive full level `N` (`gammaFullNaiveProblem`, relatively
  representable and finite étale where `N` is invertible) and `H ⊆ GL₂(ℤ/N)` acting through
  `EllipticCurve.glSmul`. `P_H` is pinned by **(Q1)+(Q2)** of 7.1.2; it is *not* the naive
  orbit presheaf.
* **T-H4 (corrected)** — `P_H` relatively representable and finite étale: KM 7.1.3(1),(2),(4). Staged
  as `gammaH_relativelyRepresentable` + `gammaHNaive_toQuotient` (GammaHRepresentability.lean); the
  `H = ⊥` case coincides with `Γ(N)` itself (`gammaHNaive_relativelyRepresentable_bot`, PROVEN).
* **T-H6 (corrected)** — rigid `P_H` representable, base smooth+affine: KM COROLLARY 4.7.2's own
  proof (rigidity 2.7.2 + rel-rep 3.7.1 + the KM 4.7 engine), i.e. the amended `representable_iff`
  (T-E5, with `AffineOverEll` from 7.1.3(2),(4)) applied to `P_H`. Staged as
  `gammaH_representable_of_rigid`; gated on the KM 4.7 ⇐ engine (`exists_ellipticCurveGeom_quotient`,
  CHARTER-FP4).
* The **falsity of the naive statements** is locked into the library by
  `gammaHNaiveProblem_not_relativelyRepresentable` (the codiagonal counterexample). The naive
  declarations in `GammaH.lean` are `theorem_statement_protected` — kept as documented non-goals,
  never deleted.
