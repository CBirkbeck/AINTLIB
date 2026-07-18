# STREAM-Y1 — decomposition: the Y₁(N) representability + smoothness assembly (T-E7)

**Target**: `gammaOneNaive_representable` (`Moduli/Representability.lean:250`, HELD file — not
edited): for `N ≥ 4`, `N` invertible in `R`, `(gammaOneNaiveProblem R N).Representable ∧
∀ X, Nonempty (RepresentableBy X) → Smooth X.structMap ∧ IsAffineHom X.structMap`.

**Skeleton**: `ModularCurves/ModularCurve/YOneAssembly.lean` (NEW, registered in root
`ModularCurves.lean`). `lake build ModularCurves.ModularCurve.YOneAssembly` — **GREEN**
(2026-07-08, 3093 jobs, sorries only: 19 sorried leaves; the MASTER bridge
`gammaOneNaive_representable_assembly` is term-assembled with **no sorry of its own** and its
statement is identical to the held target, so T-E7 closes by `exact` once the leaves land).

**Source of record**: refs/ModularCurves/modcurvesnotes.pdf (Loeffler), §3.3 pp. 12–14 and
§3.4 p. 15 — full proofs read (Definition 3.3.3, Proposition 3.3.4 with proof, Corollary 3.3.5
with proof, Definition 3.3.6 with the Remark, Lemma 3.4.2 with proof, Proposition 3.4.3,
Theorem 3.4.4 with proof). Page numbers below are the *printed* page numbers.

**RR-only rule check**: no leaf assumes anything except through proofs or the named tracked
gates listed in §7; BB-RR enters only through the already-standing `EllipticCurveGeom` bridge
(fibre condition), not through any new leaf of this stream.

---

## 1. The prose proof, preserving Loeffler's structure

### 1a. The construction (Def 3.3.3 → Prop 3.3.4 → Cor 3.3.5 → Def 3.3.6)

**Stage (Def 3.3.3, p. 13).** For `α, β ∈ Γ(S, O_S)` let `E(α,β) ⊆ P²_S` be
`Y²Z + αXYZ + βYZ² = X³ + βX²Z` with discriminant
`∆(α,β) = β³(α⁴ − α³ + 8α²β − 36αβ + 16β² + 27β)`; if `∆(α,β)` is a unit this is an elliptic
curve, and the computation displayed after the definition (`−P = (0:−β:1)`, `2P = (−β:β(α−1):1)`,
`−2P = (−β:0:1)`, `3P = (1−α:α−β−1:1)`, `−3P = (1−α:(α−1)²:1)`) shows the marked point
`P = (0:0:1)` *"does not have order 1, 2 or 3 in any fibre"* — the displayed multiples are
affine points, hence nonzero fibrewise.

**Normalisation (Prop 3.3.4, pp. 13–14).** If `E/S` is elliptic and `P ∈ E(S)` has
`P, 2P, 3P ≠ 0` in any fibre, there exist **unique** `α, β` with `∆(α,β)` a unit and a
**unique** isomorphism `E(α,β) ≅ E` sending `(0:0:1)` to `P`. Proof structure: *(local case)*
if `E` has a Weierstrass equation, translate `P` to `(0,0)`; since `P` is nowhere 2-torsion the
tangent at `P` is non-vertical, so a shear kills the `a₄`-term; since `P` is nowhere an
inflexion (3-torsion), `a₂` is a unit, and a scaling arranges `a₂ = a₃`, i.e. Tate normal form;
uniqueness by comparing coefficients. *(global case, verbatim p. 14)*: "Now consider a general
`E/S`. We know that there exists an affine covering `S = ⋃ᵢ Uᵢ`, such that `E|_{Uᵢ}` has a
Weierstrass equation over `Γ(Uᵢ, O_S)`, so we get `αᵢ, βᵢ ∈ Γ(Uᵢ, O_S)` such that
`(E|_{Uᵢ}, P_{Uᵢ}) ≅ (E(αᵢ, βᵢ), (0,0))`. Since `αᵢ, βᵢ` are unique, the[y] must agree on
`Uᵢ ∩ Uⱼ`. The sheaf property of `O_S` then implies that there exist `α, β ∈ Γ(S, O_S)` such
that `res_{Uᵢ}(α) = αᵢ` … Then `(E, P) ≅ (E(α,β), (0,0))`." Remark (verbatim): *"local
uniqueness gives global existence."*

**The atlas (Cor 3.3.5, p. 14, verbatim).** *"The pair
`(Spec ℤ[A, B, ∆(A,B)⁻¹], E(A,B), (0:0:1))` represents the functor `Schᵒᵖ → Set`,
`S ↦ {eq. classes of pairs (E,P), E/S elliptic curve, P ∈ E(S) not of order 1, 2, 3 in any
fibre}`."* (Proof: "(i) is a restatement of Proposition 3.3.4.")

**Y₁(N) (Def 3.3.6, p. 14, verbatim).** *"For `N ≥ 4`, let `Y_N` be the closed subscheme of
`Y = Spec ℤ[A,B,∆(A,B)⁻¹]`, where `N · (0:0:1) = (0:1:0)`, and let
`Y₁(N)_{ℤ[1/N]} = (Y_N − ⋃_{d|N, 4≤d<N} Y_d) ×_{Spec ℤ} Spec ℤ[1/N]`. By construction, this
represents the functor `S ↦ {elliptic curves E/S with point of exact order N}` on the category
of `ℤ[1/N]`-schemes."* Remark (verbatim, pp. 14–15): *"More precisely, `Y₁(N)_{ℤ[1/N]}` has a
universal elliptic curve over it by restricting `E(α,β)/Y`, and this has a point `(0,0)`. The
triple (`Y₁(N)_{ℤ[1/N]}`, this curve, this point) represents the above functor."*

Unpacking "by construction" (this is what §D formalises): given `(E/T, P)` with `P` of
fibrewise exact order `N` and `N` invertible on `T`: since `N ≥ 4` and no proper multiple of
`P` vanishes fibrewise, `P, 2P, 3P ≠ 0` fibrewise, so Cor 3.3.5 yields a unique classifying
map `u : T → Y` with `(E,P) ≅ u^*(E(A,B),(0,0))`; `N·P = 0` (the global killing clause) says
exactly that `u` factors through the closed `Y_N`; fibrewise exact order `N` says the image of
`u` misses each removed locus `Y_d` set-theoretically (if `u(x) ∈ Y_d` then `d·P_x = 0` with
`d | N`, `d < N`) — and conversely a point killed by `N` whose order is not a proper divisor
of `N` has exact order `N` (any `a·P_x = 0` with `0 < a < N` forces `gcd(a,N)·P_x = 0`, a
proper-divisor kill; proper divisors `≤ 3` cannot occur on the atlas). So maps `T → Y₁(N)`
over `ℤ[1/N]` correspond exactly to naive `Γ₁(N)` pairs; uniqueness of the classifying map
(including its curve-component: Prop 3.3.4's *unique isomorphism*) makes the correspondence
bijective and natural.

### 1b. Smoothness (Lemma 3.4.2 → Prop 3.4.3 → Thm 3.4.4)

**Lemma 3.4.2 (p. 15, verbatim).** *"(1) The composition of smooth morphisms is smooth.
(2) If `E/S` is an elliptic curve and `N ≥` is [sic] invertible on `S`, then `[N] : E → E` is
smooth."* Proof of (2), verbatim: *"The morphism `[N]` multiplies a global differential by
`N`, so it induces an isomorphism of tangent space. In other words, it is an étale morphism,
and étale morphisms are smooth."* — In this repo this is exactly **BB-DIFF**
(`mulByHom_formallyUnramified` → `mulBy_etale` → `torsionπ_etale`, `EllipticCurve/Torsion.lean`,
with the in-flight discharge route `MulByHomUnramified.lean`); we consume it as a named gate.

**Prop 3.4.3 (p. 15, verbatim).** *"(Functorial criterion for smoothness) Let `X → Spec(R)` be
a scheme of finite type over `R`, where `R` is noetherian. Then the map `X → Spec(R)` is a
smooth morphism if and only if it is formally smooth, i.e. for any local `R`-algebra `A` and a
nilpotent ideal `I ⊂ A`, the map `Hom_{Sch/R}(Spec A, X) → Hom_{Sch/R}(Spec A₀, X)` is
surjective, where `A₀ = A/I`."* (Proof: "See Stacks Project §36.9.")

**Thm 3.4.4 (p. 15, verbatim).** *"`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."* Proof,
verbatim: *"Let `A` be a local `ℤ[1/N]`–algebra, and let `I ⊂ A` be nilpotent. Let
`(E₀, P₀) ∈ Y₁(N)(A₀)`. The ring `A₀` is local, so `E₀` has a Weierstrass equation over
`Spec(A₀)`. Lift coefficients arbitrarily to `A` to get `E/A` lifting `E₀`; note that
`∆(E) ∈ Aˣ` since its image in `A₀` is in `A₀ˣ`. Can we lift `P₀` to an `N`-torsion point of
`E`, i.e. is `E[N]` smooth? Yes, since `[N] : E → E` is smooth, and a composition of smooth
morphisms is smooth. (We apply this to `[N]` composed with the structure map `E → Spec A`.)
Hence `(E₀, P₀)` lifts to `(E, P)`, and we are done."*

Unpacked (as §E formalises): the formal criterion reduces smoothness to lifting pairs along
nilpotent thickenings; representability converts morphism-lifting to pair-lifting. Lift the
Tate coefficients (units lift mod nilpotents); lift the torsion point through the smooth
(étale) `E[N] → Spec A`; the lifted pair reduces to `(E₀,P₀)`, has the same fibres (nilpotent
thickening), hence still has fibrewise exact order `N`; renormalise to Tate form (Prop 3.3.4)
— the renormalisation reduces to the identity over `A₀` by the *uniqueness* clause, so the
corrected classifying map still lifts the given one and lands in `Y₁(N)`.

**Affineness** (needed by T-E7's statement; NOT proven in the notes — Loeffler displays `Spec`
only for `N = 5` in Def 3.3.6, and the board marks the general-`N` affineness QUOTE-PARTIAL):
over a base with `N` invertible, each removed `Y_d` (`d | N`) is **open in `Y_N`** as well as
closed: on `Y_N` the killed point classifies into the finite étale `E[N]` (Lemma 3.4.2(2)
again), the zero section of an étale separated family is an open immersion, and `Y_d ∩ Y_N` is
the preimage of it under the `d`-multiple section. Hence `Y₁(N)` is *clopen* in the affine
`Y_N`, i.e. the basic open of an idempotent — affine. (KM "affine over (Ell)" locator to be
attached when the KM Ch. 4 text is processed; the mathematics above is self-contained.)

Note (p. 15, verbatim, sanity): *"The schemes `Y_N/ℤ` are very rarely smooth; it was true for
`N = 5` essentially by accident."* — smoothness genuinely needs `ℤ[1/N]`; our standing
hypothesis `IsUnit (N : R)` supplies it.

---

## 2. Adjudicated architecture decisions (adversarial pass, 2026-07-08)

**(α) Work over arbitrary `R` (with `IsUnit (N : R)`) at once, not over `ℤ[1/N]` + base
change.** Loeffler constructs over `ℤ` and then `×_{Spec ℤ} Spec ℤ[1/N]`. The held T-E7
statement is over an arbitrary `R` with `N` invertible. The two routes: (i) construct over
`ℤ[1/N]`, then a change-of-base-ring comparison of `Ell/ℤ[1/N]` and `Ell/R` functors;
(ii) run the identical construction over `R` (the T-E1/T-E2 inputs are proven for *every*
ring, and the smoothness lifting never uses noetherianness — see (γ)). Route (ii) chosen: it
avoids an extra Ell-category comparison layer, and Loeffler's `× Spec ℤ[1/N]` step becomes
literally the standing hypothesis. ATTACK (does anything in the source *need* `ℤ`-initiality?):
Prop 3.3.4/Cor 3.3.5 are stated over arbitrary `S`; the only `ℤ`-specific display is the atlas
ring itself, and its universal property (T-E2) is ring-agnostic. No leaf lost. ATTACK
(noetherian, see (γ)). ATTACK (does `Smooth` base-change if someone later wants `ℤ[1/N]` →
`R` instead?): mathlib `smooth_isStableUnderBaseChange` exists, so the alternative route stays
open; recorded, not needed.

**(β) Cut the loci naively (killed loci + set-removal), NOT through the Drinfeld machinery
(T-D33/T-D17/T-D6).** The board's T-E7 line lists T-D6 as a dependency, and
`exists_exactOrderLocus_section` (T-D33, PROVEN) would give a *closed* Drinfeld exact-order
locus directly. Adjudication: the moduli problem being represented is the **naive** one
(`IsNaiveGammaOne` = global killing + geometric-fibre clauses); routing through the Drinfeld
locus requires KM 1.4.4 (T-D6b/T-D6c — both still `sorry`) to translate back, importing two
open boxes for no gain; Loeffler's own construction is pre-Drinfeld and matches the naive form
clause-for-clause (his `Y_N`-cut ≡ the killing clause, his set-removal ≡ the fibre clauses).
DEVIATION from the board's dependency list, gain: T-E7's representability half is now
**independent of T-D6**. The Drinfeld connection remains available downstream via the proven
`isGammaOne_iff_naive` (T-D9) for whoever needs the Drinfeld-form corollary. ATTACK (is the
naive locus really a subFUNCTOR — scheme-theoretic factoring vs set-theoretic?): the killing
clause is *scheme-theoretic* (factor through the closed `Y_N` ⟺ `N • P|_T = 0`, leaf Y1-C2 —
matching the ADVERSARIAL FIX in `IsNaiveGammaOne` that demands the global clause), while the
removed loci matter only *set-theoretically* (factor through an open ⟺ image avoids the closed
sets), matching the fibrewise clauses. Both matchings are leaves (Y1-C2, Y1-C3/C4), not
assumptions. ATTACK (nilpotents: could a `T`-map land set-theoretically in `Y_N` without the
section being killed?): yes — which is exactly why `Y_N` must be the scheme-theoretic cut and
why the `ℚ̄[ε]` counterexample forced the killing clause; the construction respects this.

**(γ) Upgrade Loeffler's formal criterion (local test rings, noetherian base) to mathlib's
`Algebra.FormallySmooth` (all square-zero/nilpotent pairs, no noetherian hypothesis).**
mathlib has NO scheme-level `FormallySmooth`; its `Smooth` is `HasRingHomProperty` for
`RingHom.Smooth = Algebra.FormallySmooth + FinitePresentation`. So the lifting must be proved
against **arbitrary** (not local) test pairs. Adjudication of soundness: Loeffler uses locality
of `A₀` ONLY to trivialise `ω_{E₀}` ("The ring `A₀` is local, so `E₀` has a Weierstrass
equation"). In our setting the lifting datum is a *morphism* `Spec A₀ → Y₁(N)`, and
representability hands `(E₀,P₀)` the global Tate equation `(α₀, β₀)` for free — locality is
never used. The noetherian hypothesis in Prop 3.4.3 is likewise an artefact of his reference;
mathlib's ring-level criterion has none (finite *presentation* replaces finite type — leaf
Y1-E4). DEVIATION (upgrade), justified line-by-line in leaf Y1-E5/E6 blocks. ATTACK (does any
step of the lifting secretly need `A` local — e.g. the torsion-point lift?): the lift goes
through `Algebra.FormallySmooth.lift` for the étale chart algebra of `E[N]`, stated for
arbitrary `B` and nilpotent `I` — no locality. ATTACK (square-zero vs nilpotent): mathlib's
`FormallySmooth.lift` is already stated for `IsNilpotent I` (`RingTheory/Smooth/Basic.lean:151`),
doing the dévissage internally — verified present.

**(δ) `E[N]`-lifting through the affine chart, dodging KM 2.3.1 (BB-QF/BB-FLAT).** The
torsion-point lift needs a ring-level smooth algebra; `E[N]` itself is affine only via
`torsionπ_isFinite`, which sits on the sorried KM 2.3.1 boxes (BB-QF). Adjudication: the point
`P₀` being lifted is *nowhere zero* (it has exact order `N ≥ 4` fibrewise, and
`Spec A ≅ Spec A₀` topologically), so it lives in `E[N] ∩ {affine Weierstrass chart}` — which
is closed in the affine chart (base change of `torsionι`, T-B3 proven) hence affine, and open
in the étale `E[N]` hence étale. So the lifting runs at ring level with gates reduced to
**BB-DIFF only**. ATTACK (is `E[N] ∩ chart → Spec A` really étale: open immersion ∘ étale?):
`IsOpenImmersion` is étale and `Etale` is multiplicative — mathlib instances, verified. ATTACK
(could the lift escape the chart?): irrelevant — any lift *within the chart-torsion scheme*
suffices; we never claim all torsion is affine. ATTACK (zero section of `E(α,β)`: is the
marked point's chart-membership fibrewise-checkable?): yes — a section misses the closed
zero-section image iff it misses it fibrewise, and `Spec A`, `Spec A₀` have identical points
and residue fields.

**(ε) Rigidity lives inside the atlas (T-E1 uniqueness), not as a separate Γ₁-rigidity
theorem.** The injectivity of the classifying correspondence needs: two `Ell/R`-maps
`f, g : Y → (atlas)` pulling the marked point to the same `P` are equal — including their
`top` components. A pointed automorphism over `𝟙` fixing the Tate marking is chartwise a
variable change (gate T-W7) fixing `(0,0)` with Tate-normal target, hence the identity by
T-E1's **uniqueness** clause. No `N ≥ 4` rigidity computation (`Aut(E, P_{≥4}) = 1` à la KM
2.7.x) is needed anywhere: the nowhere-order-`≤3` marking already rigidifies (this is Loeffler's
"unique isomorphism" in Prop 3.3.4, and why Cor 3.3.5 has no `N`). ATTACK ([-1]?): `[-1]`
moves the marked point (`P ≠ -P` since `2P ≠ 0` fibrewise — visible in the p. 13 display
`-P = (0:-β:1) ≠ (0:0:1)` as `β | ∆` is a unit… `β` a unit follows from `∆(α,β)` a unit since
`β³ ∣ ∆`), so it is excluded by the marking, consistent. ATTACK (translations?): excluded by
`zero_w` in `EllHom` (pointed category — the EllCategory adjudication of 2026-07-06).

**(ζ) Index set of the removed loci: Loeffler's `{d ∣ N, 4 ≤ d < N}` kept verbatim.** The
alternative `{d ∣ N, d < N}` is equivalent (the `d ≤ 3` loci are empty on the atlas) but drifts
from the display. Keeping his index set forces the comparison leaf to use
`tatePoint_nowhereGeomOrderLEThree` for the `d ≤ 3` cases — exactly the role Cor 3.3.5's
"not of order 1, 2, 3" plays in his construction. Edge checks: `N = 4, 5, 6` give the empty
filter (`properDivisors` are all `≤ 3`), so `Y₁(N) = Y_N` there — matching Loeffler's `N = 5`
display `Y₁(5) = Spec ℤ[1/5, B, ∆(1+B,B)⁻¹]` (the killed locus itself, cut by `3P = −2P` ⟺
`A = 1 + B` per Cor 3.3.5(ii)) and the order-arithmetic (`6·P = 0` + order ∉ {1,2,3} already
forces order 6). First genuinely removed locus: `N = 8` (`d = 4`).

---

## 3. The leaf tree (build order)

```
Y1-MASTER  gammaOneNaive_representable_assembly   [TERM-ASSEMBLED, no own sorry]
├── Y1-D3  yOne_representableBy                    (representability half)
│   ├── Y1-B2 (L-ATLAS) exists_tatePoint           [API-GAP: subtree §B2; gates T-W7, T-A6b]
│   │   ├── Y1-B1 projModel_locallyWeierstrass     [project-adapt of proven T-W5a]
│   │   ├── (T-E1, T-E2 — PROVEN, cited)
│   │   └── (PointsDictionary projModelPointsEquiv — PROVEN, cited)
│   ├── Y1-D1 factors_yOne_iff                     (locus ↔ functor)
│   │   ├── Y1-C2 killedLocus_spec
│   │   ├── Y1-C3 mem_killedLocus_range_iff
│   │   ├── Y1-C4 pull_smul_eq_zero_iff_residue
│   │   ├── Y1-A3 exists_properDivisor_smul_eq_zero
│   │   └── Y1-A2 IsNaiveGammaOne.nowhereGeomOrderLEThree
│   └── Y1-D2 isNaiveGammaOne_pullSection_iff      [gate T-E4-family canonicity]
├── Y1-F1  representableBy_smooth_isAffineHom      (transport; uses D3's witness +)
│   ├── Y1-E6 yOneStructMap_smooth                 (smoothness half)
│   │   ├── Y1-E5 yOne_infinitesimal_lifting       [gate BB-DIFF; uses D1/D3, T-E1]
│   │   ├── Y1-E4 yOneStructMap_locallyOfFinitePresentation
│   │   └── Y1-E2 yOne_isAffine
│   ├── Y1-E3 yOneStructMap_isAffineHom  ← Y1-E2
│   └── Y1-E2 yOne_isAffine ← Y1-E1 killedLocus_preimage_isOpen [gate BB-DIFF]
└── defs: tateCurveOver/tateRingOver/tateBase/tateGeom/tateUniversal [gate T-A6b]/tateEllObj/
      tatePoint (choose of Y1-B2)/killedLocus(π)/yOneSet (isOpen = Y1-C5)/yOne/yOneEllObj
```

Everything below `Y₁(N)`'s definition consumes `tatePoint` only through the two opaque pins
(`tatePoint_nowhereGeomOrderLEThree`, `tatePoint_classifies`) and `tateUniversal` only through
`tateUniversal_geom` — the heavy definitions ship their opaque interfaces in the same
increment (v10.24(b)); no `maxHeartbeats` anywhere.

---

## 4. Leaf blocks (quote · match · attacks · discharge · LOC)

Format per leaf: **[name]** (file line) — source locator; verbatim quote; Lean↔source match;
attacks (≥3); discharge class; LOC (grounded against the source's own line counts and the
repo's proven analogues).

### Y1-A2 `IsNaiveGammaOne.nowhereGeomOrderLEThree`
- **Source**: Loeffler Def 3.3.6, p. 14 — *"For `N ≥ 4`, let `Y_N` be…"*; the `N ≥ 4`
  hypothesis exists solely so exact-order-`N` points satisfy Prop 3.3.4's *"`P, 2P, 3P ≠ 0`
  in any fibre"* (p. 13).
- **Match**: `IsNaiveGammaOne`'s fibre clause forbids `a • P = 0` for `0 < a < N`; with
  `a ≤ 3 < 4 ≤ N` this specialises to `NowhereGeomOrderLEThree`, whose quantifier shape
  (`∀ k [Field k] [IsAlgClosed k] (t : Spec k ⟶ S)`) is copied from `IsNaiveGammaOne` so no
  quantifier mismatch can hide here.
- **Attacks**: (1) `N = 4` edge: `a ∈ {1,2,3}` all `< 4` ✓. (2) Hypothesis strength: does it
  need the killing clause? No — only the fibre clause; stated with the full `IsNaiveGammaOne`
  for interface simplicity. (3) Counterexample hunt for `N ≤ 3`: for `N = 3`, `a = 3` is NOT
  `< N`, so the lemma is false-shaped there — the `4 ≤ N` hypothesis is load-bearing and
  present. (4) Source drift: Loeffler never states this as a lemma; it is the (only) glue
  between Def 3.3.6's `N ≥ 4` and Prop 3.3.4's hypothesis — flagged as an unquoted-but-forced
  step.
- **Discharge**: pure logic over the definitions. mathlib-discharged (`omega`-grade arithmetic).
  **LOC ~8**.

### Y1-A3 `exists_properDivisor_smul_eq_zero`
- **Source**: Def 3.3.6, p. 14 — the removed union ranges over *"`d|N, 4≤d<N`"* while "exact
  order `N`" forbids all `0 < a < N`; the gcd reduction is the implicit bridge.
- **Match**: abstract `AddCommGroup` statement; instantiated at `E.Point t` (which carries
  `pointAddCommGroup`). Conclusion `∃ d ∈ N.properDivisors, 0 < d ∧ (d:ℤ) • x = 0` matches
  `Nat.mem_properDivisors : d ∣ N ∧ d < N`.
- **Attacks**: (1) `a` coprime to `N`: `gcd = 1`, `1 • x = x = 0` — a proper-divisor kill with
  `d = 1`, handled downstream by order-1-freeness of the atlas ✓ (the lemma must NOT claim
  `4 ≤ d`). (2) `N` prime: only `d = 1` possible — Y₁(p) removes nothing; consistent with §2ζ
  edge checks. (3) Discharge verification: `addOrderOf_dvd_of_nsmul_eq_zero` +
  `Nat.dvd_gcd`/Bézout via `Int.gcd_eq_gcd_ab` or `AddSubgroup.zsmul` — mathlib names verified
  to exist in the additive-order API (`Mathlib/GroupTheory/OrderOfElement.lean`). (4) `x = 0`
  edge: `d = 1` works (`0 < 1`, `1 ∣ N`, `1 < N` needs `N > 1` — from `ha0, haN`:
  `0 < a < N` gives `N ≥ 2` ✓).
- **Discharge**: mathlib-discharged. **LOC ~20**.

### Y1-B1 `projModel_locallyWeierstrass`
- **Source**: Prop 3.3.2, p. 13 (a global Weierstrass model is trivially locally Weierstrass);
  the *proof* is the repo's own `universalCurve_localModel` (`Moduli/WeierstrassAtlas.lean`,
  T-W5a, PROVEN sorry-free — verified `grep -c sorry` = 0) with `universalWeierstrassLoc`
  replaced by an arbitrary elliptic `W/A`.
- **Match**: statement is the `LocallyWeierstrass` field of `EllipticCurveGeom` for
  `projModelπ W`, exactly what `tateGeom` needs.
- **Attacks**: (1) Generality: the T-W5a proof inspected — no step uses the specific
  coefficients (the witnesses are `⊤`, `ΓSpecIso`, `isPullback_projModelBaseChange`); the
  adaptation is mechanical. (2) Duplication check (cardinal sin): rather than copy, the
  discharge should *generalise* T-W5a in place and re-instantiate it there — noted for the
  worker; either way one proof. (3) Elaboration risk: T-W5a's proof fought `IsIso` synthesis at
  instances-transparency (its comments record the fix pattern) — the general version inherits
  the same pattern, so LOC is budgeted at the full T-W5a size, not a fraction.
- **Discharge**: project-discharged-by-adaptation (`WeierstrassAtlas.lean:103-173`).
  **LOC ~80**.

### Y1-B2 `exists_tatePoint` (L-ATLAS — the master atlas leaf) — API-GAP with subtree
- **Source**: Cor 3.3.5, p. 14 (verbatim in §1a); Prop 3.3.4 + its general-case proof
  (verbatim in §1a); the marked-point display of p. 13 (*"so `P` does not have order 1, 2 or 3
  in any fibre"*).
- **Match**: `∃ P₀, NowhereGeomOrderLEThree P₀ ∧ ∀ (Y, P) nowhere-≤3, ∃! f : Y ⟶ tateEllObj,
  pullSection f P₀ = P` is Cor 3.3.5 read as an `Ell/R`-presheaf universal property: Loeffler's
  "eq. classes of pairs" functor on `Sch` is replaced by the sections-with-property presheaf on
  `Ell/R` (the project's KM-style register, per Loe Def 3.7.1) — the ∃!-classifying-map form is
  the standard equivalent of representability there, and is what Y1-D3's `RepresentableBy`
  assembly consumes. The uniqueness of `f` (both components) is Prop 3.3.4's *"unique
  `α, β` … and a unique isomorphism"*.
- **Subtree** (ordered; each item gets its own declaration when this leaf is opened as the
  stream's Act 2):
  1. **B2-i (affine-point extraction)**: a section of `projModel W` that is fibrewise never the
     zero point factors through the affine `Z ≠ 0` chart, yielding coordinates
     `(x, y) ∈ Γ(T)²` with `W.toAffine.Equation x y`. Substrate: `projModelPointsEquiv` +
     `InZChart` (PointsDictionary, PROVEN) fibrewise, then globalised on the affine chart
     (closed zero-section complement). ~60 LOC.
  2. **B2-ii (order ⟹ unit, converse dictionary)**: fibrewise `2P, 3P ≠ 0` makes
     `ψ₂ψ₃(x,y)` a **unit**: a non-unit lies in a maximal ideal (`Ideal.exists_le_maximal`),
     and at the corresponding residue field the division-polynomial dictionary
     (`Ψ_two`/`Ψ_three` as in T-E1's proof, plus the field-level 2-/3-torsion ⟺ vanishing
     equivalences — converses of `twiceNeZero_of_isUnit`/`thriceNeZero_of_isUnit`,
     `ForMathlib/TateNormalForm.lean`) produces a killed multiple, contradiction. Needs the
     residue-vs-geometric bridge Y1-C4 to move from `IsAlgClosed` quantifiers to maximal-ideal
     residue fields (pass to `AlgebraicClosure κ(m)`). ~90 LOC.
  3. **B2-iii (per-chart classification)**: on an affine chart `U` of `T`, T-E1
     `exists_unique_variableChange_isTateNormal` (PROVEN) + T-E2 `tateRing_homEquiv` (PROVEN,
     ring-agnostic) + gate **[T-W7]** (`pointedIso_exists_variableChange` to see every pointed
     model iso as a variable change; `projModelVCIso_injective` for faithfulness) produce the
     unique `(α_U, β_U)` and the unique pointed chart iso. ~120 LOC of glue.
  4. **B2-iv (gluing)**: Loeffler p. 14 verbatim (*"Since `αᵢ, βᵢ` are unique, they must agree
     on `Uᵢ ∩ Uⱼ`. The sheaf property of `O_S`…"*): uniqueness on overlaps ⟹ the `(α_U, β_U)`
     glue to `Γ(T)`-sections ⟹ a map `T → tateBase` via Γ–Spec (`ΓSpec.adjunction`); the chart
     isos glue to the cartesian `top` by uniqueness (same mechanism). ~150 LOC.
  5. **B2-v (uniqueness of the EllHom)**: §2ε — chartwise T-E1-uniqueness kills a pointed
     automorphism fixing the marking; `hom_ext` on the (separated) model. ~80 LOC.
  6. **B2-vi (the universal pair's own property)**: the p. 13 display: `−P, 2P, −2P, 3P, −3P`
     are affine points with explicit coordinates, nonzero in every fibre because they are
     affine (≠ point at infinity) — checked through `projModelPointsEquiv_some/zero` + the
     mathlib group law over each geometric fibre; `β` a unit (as `β³ ∣ Δ`) feeds the `2P ≠ 0`
     computation. ~120 LOC.
- **Attacks**: (1) *Cardinality trap* (the T-E2 adversarial fix precedent): the ∃!-form pins
  the classifying map by the *equation* `pullSection f P₀ = P`, not by a bare bijection — no
  cardinality-only discharge possible. (2) *Rigidity soundness*: see §2ε — `[-1]` and
  translations excluded; adjudicated against Loeffler's "unique isomorphism". (3) *Quantifier
  drift*: Loeffler's functor is on `Sch`; ours on `Ell/R`. For representability *of the
  Γ₁-problem* (a presheaf on `Ell/R`) the `Ell/R` form is the correct target and is strictly
  what D3 consumes; the `Sch`-form is recoverable but not needed. (4) *Zero-divisor bases*:
  `Γ(T)` arbitrary (nonreduced, disconnected) — T-E1/T-E2 are proven for arbitrary rings;
  disconnected `T` glues componentwise through the sheaf argument (no connectedness used).
  (5) *Empty `T`*: the unique map exists vacuously; `∃!` still holds — checked that `Ell/R`
  allows empty bases.
- **Discharge**: API-GAP (subtree above); gates consumed: **[T-W7]** (in flight, A-lane),
  **[T-A6b]** (for the ambient `tateUniversal` only). **LOC ~620 total** across 6 sub-leaves
  (grounded: Loeffler's Prop 3.3.4 proof is 14 source lines ≈ the historical ratio of the
  proven T-E1 (16 source lines → ~350 repo LOC over TateNormalForm.lean)).

### Y1-C1 `killedLocusπ_isClosedImmersion`
- **Source**: Def 3.3.6, p. 14: *"let `Y_N` be the **closed** subscheme of `Y` … where
  `N · (0:0:1) = (0:1:0)`"*.
- **Match**: `killedLocus := pullback ((N • P).1) E.zero`, `killedLocusπ = pullback.fst` — the
  scheme-theoretic locus where the section `N • P` equals zero; closedness = the quoted
  "closed subscheme".
- **Attacks**: (1) Is the pullback really the equalizer-locus? `fst ≫ (N•P).1 = snd ≫ zero`
  and composing with `π` forces `fst = snd`, so factoring through it ⟺ the two sections agree —
  verified in the Y1-C2 route. (2) Separatedness input: `IsClosedImmersion E.zero` from
  `zero ≫ π = 𝟙` + `of_comp` — the exact pattern of the PROVEN `torsionι_isClosedImmersion`
  (T-B3). (3) Degenerate `d = 0`: `0 • P = 0`, locus = everything — closed immersion still
  (pullback of zero along zero); harmless, never used.
- **Discharge**: project-discharged (mirror T-B3, `Torsion.lean:85-91`). **LOC ~12**.

### Y1-C2 `killedLocus_spec`
- **Source**: Def 3.3.6, p. 14 (the `N·P = 0` cut), against `IsNaiveGammaOne`'s global killing
  clause (`LevelStructure/Basic.lean:62`, the 2026-07-06 ADVERSARIAL FIX: *"the global killing
  clause `(N:ℤ) • P = 0` is REQUIRED"*).
- **Match**: `(∃ h, h ≫ killedLocusπ = t) ↔ (d:ℤ) • Point.pull E t P = 0` — the universal
  property that makes Loeffler's closed cut *be* the killing clause functorially.
- **Attacks**: (1) Direction check: `⟸` is `pullback.lift`; `⟹` composes the factoring with
  `pullback.condition` — both elementary; the smul↔composition bridge is
  `point_smul_eq_comp_mulBy` + `Point.pull_zsmul` (both PROVEN). (2) Uniqueness of `h`:
  closed immersions are mono — noted in the docstring, not needed in the iff. (3) Type-level
  drift: the killing clause of `IsNaiveGammaOne` is about the *section of the base-changed
  curve*; the bridge `asSection_zsmul` (PROVEN) + injectivity of `asSection` (from
  `asSection_val_fst`) converts — consumed in Y1-D1, kept out of this leaf to keep it
  section-free.
- **Discharge**: project+mathlib-discharged. **LOC ~35**.

### Y1-C3 `mem_killedLocus_range_iff`
- **Source**: Def 3.3.6, p. 14 — the removal `Y_N − ⋃ Y_d` is a removal of *loci*; the naive
  functor speaks of fibres. First half of the bridge.
- **Match**: `x ∈ range (killedLocusπ).base ↔ (d:ℤ) • pull (fromSpecResidueField x) P = 0`.
- **Attacks**: (1) `⟸` is Y1-C2 at `t = fromSpecResidueField x` + taking image of the unique
  point. (2) `⟹` is the nontrivial direction: a *reduced* one-point scheme maps through a
  closed immersion iff its point lies in the image — via the closed-immersion residue-field
  isomorphism (stalk surjectivity); verified mathlib has the ingredients
  (`IsClosedImmersion` stalk epi + `Scheme.Hom.residueFieldMap`); if the residue-iso packaging
  is missing, fallback: `Scheme.IdealSheafData` support membership. (3) Nonreduced trap: the
  statement deliberately uses only the residue-field point (reduced), never `Spec κ(x)[ε]` —
  set-membership cannot see nilpotents, and doesn't need to (the killing clause was already
  captured scheme-theoretically by Y1-C2; §2β).
- **Discharge**: mathlib-discharged (bounded plumbing). **LOC ~40**.

### Y1-C4 `pull_smul_eq_zero_iff_residue`
- **Source**: implicit in Def 3.3.6's "by construction" (fibres of the removed loci vs
  geometric fibres); the mechanism is standard fpqc descent of equality.
- **Match**: for any field-valued `t : Spec k ⟶ S` with image `x`:
  `a • pull t P = 0 ↔ a • pull (fromSpecResidueField x) P = 0` — converts the naive functor's
  `∀ (k) [IsAlgClosed k]` quantifier into the pointwise range conditions of Y1-C3, in both
  directions (existence of a geometric point over `x`: `AlgebraicClosure κ(x) : Type u`).
- **Attacks**: (1) Universe: `κ(x) : Type u`, its algebraic closure stays in `Type u` ✓ — the
  `IsNaiveGammaOne` quantifier is `Type u`-bounded, no lift needed. (2) The `⟸` direction
  needs *injectivity* of pulling along `Spec k → Spec κ(x)`: faithfully flat (field extension)
  + surjective qc ⟹ epi (`Flat.epi_of_flat_of_surjective`, verified in mathlib — the T-E11
  discharge already used it) ⟹ `cancel_epi` on the two morphisms `a•pull t P` vs zero. Factoring
  `t` through the residue field: mathlib's `SpecToEquivOfField`-style classification —
  verified the pieces exist (`Scheme.fromSpecResidueField`, `residueFieldMap`); worst case the
  factorisation is rebuilt in ~20 LOC. (3) `a = 0` edge: both sides `0 = 0` ✓ iff holds. (4)
  Hypothesis strength: `IsAlgClosed` NOT needed for this leaf (any field works) — stated
  field-general so both quantifier directions are served by one lemma.
- **Discharge**: mathlib-discharged. **LOC ~45**.

### Y1-C5 `yOneSet_isOpen`
- **Source**: Def 3.3.6, p. 14: the display `Y_N − ⋃_{d|N, 4≤d<N} Y_d` — for `Y₁(N)` to be a
  scheme, the removed set must be closed, i.e. its complement open.
- **Match**: `yOneSet` = complement of a **finite** union (Finset-indexed, Loeffler's exact
  index set `{d ∣ N, 4 ≤ d < N}` — §2ζ) of preimages of closed-immersion ranges.
- **Attacks**: (1) Finiteness: `Finset` — no topology of infinite unions. (2) Ranges closed:
  Y1-C1 + `IsClosedEmbedding.isClosed_range`. (3) Preimage under continuous `.base` ✓. (4)
  `N = 0` edge: `properDivisors 0 = ∅` — open trivially (and `[NeZero N]` guards real use).
- **Discharge**: mathlib-discharged. **LOC ~10**.

### Y1-D1 `factors_yOne_iff`
- **Source**: Def 3.3.6, p. 14, verbatim: *"By construction, this represents the functor
  `S ↦ {elliptic curves E/S with point of exact order N}` on the category of
  `ℤ[1/N]`-schemes."* — this leaf is the "by construction", §1a's unpacking, clause by clause.
- **Match**: factoring through `yOneBase` ⟺ `IsNaiveGammaOne N (asSection (pull t tatePoint))`
  on the base-changed universal curve. Shape mirrors the proven T-D33/T-W8 `_spec` interfaces
  (`levelSpaceΓ₁_spec`), so H-stream consumers see a familiar API. Decomposition inside:
  open-factoring ⟺ set-avoidance (mathlib `IsOpenImmersion.lift`/`Scheme.Opens` range
  conditions) + Y1-C2 (killing) + Y1-C3/C4 (fibres) + Y1-A3 (divisors) +
  `tatePoint_nowhereGeomOrderLEThree` (kills `d ≤ 3` and the `gcd = 1,2,3` cases).
- **Attacks**: (1) The `asSection`-vs-`pull` layer: `IsNaiveGammaOne`'s killing clause is about
  the *section* of the base-changed curve; `asSection_zsmul` (PROVEN) + `asSection` injectivity
  bridge — verified the two lemmas exist. (2) Fibre-of-fibre composition: geometric points of
  `T` map to geometric points of `tateBase` via `t` — the naive clauses compose along
  `Point.pull` functoriality (pull of pull = pull of composite, definitional up to `Category.assoc`).
  (3) `hN`/`hinv` audit: `hinv` is NOT used by this iff (both sides make sense without it);
  `hN` is likewise unused here — they are kept in the signature deliberately?? NO — adjudicated:
  drop-audit says the iff as stated *is* hypothesis-free, BUT the ≤3-cases need
  `tatePoint_nowhereGeomOrderLEThree` only (no `hN`); keep the hypotheses anyway since the
  statement is only ever consumed under them and a hypothesis-free claim invites scope creep —
  recorded as deliberate slack (a worker may weaken later; statement-safe direction). (4)
  Degenerate `T = ∅`: both sides true ✓. (5) `t` not over `Spec R`: the iff is stated for raw
  `t` — correct: the `R`-structure plays no role in the locus (matches Loeffler, whose cut is
  over `ℤ`).
- **Discharge**: assembly of Y1-C2/C3/C4/A3 + atlas pins. **LOC ~110**.

### Y1-D2 `isNaiveGammaOne_pullSection_iff`
- **Source**: KM-register functoriality (Loe Def 3.7.1's presheaf on `Ell/R`); the geometric
  content is GME Cor 2.2.5 canonicity (pointed isos of elliptic curves are group isos) — the
  same source as the held T-E4a `pullSection_add` docstring.
- **Match**: transports `IsNaiveGammaOne` across the cartesian square of an `Ell/R`-morphism:
  LHS on `X.curve`, RHS on `Y.curve.baseChange f.baseHom`; the two curves are pointedly
  isomorphic via `f.isPullback` + `zero_w`.
- **Attacks**: (1) *Duplication risk with T-E4* (cardinal sin): the held file's
  `gammaOneNaiveProblem.map` membership sorry is the ⟸ specialisation of this iff composed
  with functor laws; discharge MUST be coordinated — prove the canonicity transport once
  (this leaf), then close the held sorry from it (the held `map` field's proof term references
  nothing else). Logged as an explicit coordination note for the coordinator. (2) Does the
  transport need the full group-iso canonicity, or do the *clauses* transport barehanded?
  The killing clause `(N:ℤ) • P = 0` mentions the group structure of sections — two a-priori
  unrelated `grp` fields on the two curves — so YES, canonicity (or `abelEnrichment_unique`)
  is genuinely consumed; the fibre clauses alone would transport pointwise. This is the same
  dependency edge (A6.δ) the T-E4a amendment restored — consistent. (3) Direction audit: both
  directions needed (forward map of D3 uses ⟸ at the reflexive square; backward uses ⟹ along
  the classifying map). (4) `f` with non-flat `baseHom`: irrelevant — cartesianness is data in
  `EllHom`, no flatness used.
- **Discharge**: gate **[T-E4-family]** (GME 2.2.5 canonicity chain; in the project's
  canonicity stream). **LOC ~90** once the canonicity transport exists.

### Y1-D3 `yOne_representableBy`
- **Source**: Def 3.3.6 + Remark, pp. 14–15 (verbatim in §1a: *"The triple … represents the
  above functor"*).
- **Match**: `Functor.RepresentableBy (yOneEllObj R N)` for `gammaOneNaiveProblem R N`:
  `homEquiv : (Y ⟶ yOneEllObj) ≃ {P // IsNaiveGammaOne N P}` natural in `Y`. Forward:
  `f ↦ pullSection f (marked point)` — membership by Y1-D2 (⟸) + Y1-D1 at `t = 𝟙`-composite
  (the universal pair is itself naive-Γ₁ — "reflexivity instance"). Backward: Y1-A2 admits `P`
  to the atlas (`hN : 4 ≤ N` — HERE is where `N ≥ 4` is load-bearing); `tatePoint_classifies`
  gives the unique `f₀ : Y ⟶ tateEllObj`; Y1-D2 (⟹) + Y1-D1 factor `f₀.baseHom` through
  `yOne`; rebuild the `EllHom` into `yOneEllObj` (top = `pullback.lift`, cartesian by pasting).
  Round-trips: the ∃!-uniqueness of `tatePoint_classifies` (both components — §2ε). Naturality
  (`homEquiv_comp`): `EllHom.pullSection_comp` (PROVEN, held file) + uniqueness.
- **Attacks**: (1) *The held-file sorry does not leak*: `gammaOneNaiveProblem.map`'s membership
  proof is a `Prop` inside a subtype — naturality equations compare `.1`-components, so D3's
  proof is insulated from that sorry (verified by reading the `map` field: the value is
  `⟨pullSection …, sorry⟩` and `Subtype.ext` discharges equations). (2) The mono-composition
  trick for uniqueness: `yOneBase` mono (open ≫ closed immersion) makes "factor through yOne
  then include to atlas" injective on `baseHom`s; the `top` component rides on the atlas
  ∃!-uniqueness — no separate rigidity. (3) `Nonempty (...)` vs data: the leaf returns
  `Nonempty` to match the held statement's consumption; the underlying construction is
  explicit (no choice beyond the already-opaque `tatePoint`). (4) Naturality direction
  convention: mathlib `RepresentableBy.homEquiv_comp` is
  `homEquiv (f ≫ g) = F.map g.op (homEquiv f)`-shaped — checked against `pullSection_comp`'s
  variance (it matches the `map_comp` field of the held functor, same orientation).
- **Discharge**: assembly (Y1-B2, D1, D2, A2 + held-proven `pullSection_id/comp`).
  **LOC ~160**.

### Y1-E1 `killedLocus_preimage_isOpen` — gate [BB-DIFF]
- **Source**: Lemma 3.4.2(2), p. 15 (verbatim in §1b — `[N]` étale) + the affineness
  derivation of §1b (not in the notes; Loeffler's `Spec` display is `N = 5` only — Def 3.3.6,
  p. 14; board note QUOTE-PARTIAL).
- **Match**: on `{N • P = 0}` the `d`-killed sublocus (`d ∣ N`) is open: the classifying
  section into the étale separated `E[N]` hits the zero section in an open set.
- **Attacks**: (1) Gate audit: étale-ness of `E[N] → S'` is `torsionπ_etale` (PROVEN modulo
  the single BB-DIFF sorry — verified the only sorry in that chain is
  `mulByHom_formallyUnramified`, `Torsion.lean:228`, whose discharge is the in-flight
  `mulByHom_formallyUnramified'` MASTER); `NIsInvertible` transfers to the killed locus via
  global-sections functoriality (`IsUnit.map`). (2) The "section of étale separated is open"
  sub-step: mathlib has `[FormallyUnramified f] → IsOpenImmersion (pullback.diagonal f)`
  (`Morphisms/FormallyUnramified.lean:125`, verified) and a section is a base change of the
  diagonal (`IsPullback` of `(s, 𝟙)` against `Δ_f` — small categorical lemma, Stacks 024T
  pattern); separatedness of `torsionπ` from `torsionι` closed (T-B3, proven) + `E/S`
  separated (proper). If the section-vs-diagonal `IsPullback` is missing from mathlib it is a
  ~25 LOC sub-leaf, flagged. (3) `d ∤ N` misuse: hypothesis `hd : d ∣ N` required — without
  it `d • P` needn't be `N`-torsion on the locus and the classifying section doesn't exist;
  attack confirmed the hypothesis is necessary and present. (4) Char-`p` sanity (`N = p` NOT
  invertible): the lemma would be FALSE without `hN` (supersingular `E[p]` is infinitesimal;
  the zero section is closed-not-open) — `hN : NIsInvertible S N` is load-bearing, present ✓.
- **Discharge**: gate [BB-DIFF] + mathlib (bounded sub-leaf). **LOC ~85**.

### Y1-E2 `yOne_isAffine` — gate [BB-DIFF] via Y1-E1
- **Source**: §1b affineness derivation; Def 3.3.6's `N = 5` display as the base sanity case.
- **Match**: `yOneSet` open (C5) with closed complement-in-`Y_N` (E1 makes each removed set
  open, so their union is open, so `yOneSet` is ALSO closed) ⟹ clopen in the affine
  `Y_N ⊆ Spec R[A,B][Δ⁻¹]` (closed subscheme of affine is affine:
  `isAffine_of_isAffineHom` + closed immersions affine) ⟹ basic open of an idempotent
  (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`, verified in mathlib
  `RingTheory/Spectrum/Prime/Topology.lean:1085`) ⟹ affine (`IsAffineOpen.basicOpen`).
- **Attacks**: (1) Clopen direction check: E1 gives openness of the REMOVED sets — needed for
  closedness of `yOneSet`; C1+C5 give the other half — both present. (2) `NIsInvertible` on
  `Y_N`: from `IsUnit (N : R)` through `Γ(Spec R) ≅ R` and the structure maps — small glue,
  budgeted. (3) Idempotent route vs "open immersion with closed range is closed immersion":
  either lands; the idempotent lemma is verified-present so it anchors the plan. (4) Empty
  `yOne` (possible for special `R`!): `IsAffine ∅` holds ✓ no hidden nonemptiness.
- **Discharge**: mathlib + E1. **LOC ~70**.

### Y1-E3 `yOneStructMap_isAffineHom`
- **Source**: T-E7 statement (KM "affine over (Ell)" hypothesis-shape, KM 4.7.0 — locator ⧗).
- **Match/Attacks**: (1) source affine (E2) + target `Spec R` affine ⟹ affine morphism —
  `HasAffineProperty @IsAffineHom (fun X _ _ _ ↦ IsAffine X)` (verified,
  `Morphisms/Affine.lean:30`): over an affine target, `IsAffineHom f ↔ IsAffine X`.
  (2) No `hN/hinv` needed beyond E2's. (3) Definitional-unfolding risk of `yOneStructMap`
  (composite): property is composition-stable anyway.
- **Discharge**: mathlib + E2. **LOC ~10**.

### Y1-E4 `yOneStructMap_locallyOfFinitePresentation`
- **Source**: Prop 3.4.3, p. 15 (verbatim in §1b) — Loeffler's "finite type over noetherian
  `R`" is replaced by finite *presentation* over arbitrary `R` (§2γ); the constructions are
  visibly finitely presented.
- **Match**: `tateBase → Spec R` is a localized polynomial algebra (fp); `Y_N → tateBase` is
  the base change of the zero section, a finitely presented closed immersion — the zero
  section is lfp by the cancellation `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType`
  (project `ForMathlib/FinitePresentationCancel`, Stacks 01TX — the exact pattern of the
  PROVEN `mulByHom_locallyOfFinitePresentation`, `Torsion.lean:214-220`); open immersions are
  lfp; compose.
- **Attacks**: (1) fp of `Localization.Away` over `R`: `MvPolynomial` fp + `Away` fp
  (mathlib `RingHom.FinitePresentation` for localization away from one element — present;
  scheme-level via `HasRingHomProperty`). (2) The zero-section-of-what: of the *universal
  Tate curve* — its `π` is lfp because smooth (mathlib `Smooth → LocallyOfFinitePresentation`
  — definitional for the RingHom property); section = mono part of `zero ≫ π = 𝟙` +
  cancellation ✓ same as the Torsion.lean pattern. (3) `killedLocus` is a pullback of the zero
  section along `(N•P).1` — lfp stable under base change ✓ (mathlib instance).
- **Discharge**: project+mathlib. **LOC ~45**.

### Y1-E5 `yOne_infinitesimal_lifting` — gate [BB-DIFF]; the Thm 3.4.4 proof body
- **Source**: Thm 3.4.4, p. 15 — full proof verbatim in §1b.
- **Match** (step by step against the quote):
  | Loeffler | here |
  |---|---|
  | "Let `A` be a local `ℤ[1/N]`-algebra, `I ⊂ A` nilpotent" | arbitrary `R`-algebra `A`, `I` nilpotent (§2γ upgrade — soundness adjudicated there) |
  | "`(E₀,P₀) ∈ Y₁(N)(A₀)`" | `f₀ : Spec (A⧸I) ⟶ yOne` over `Spec R`; via Y1-D1/D3 this is the pair with its Tate coordinates `(α₀, β₀)` |
  | "`A₀` is local, so `E₀` has a Weierstrass equation" | **replaced**: representability hands the global Tate equation (no locality) |
  | "Lift coefficients arbitrarily … `∆(E) ∈ Aˣ` since its image in `A₀` is in `A₀ˣ`" | lift `(α₀,β₀)` through `A → A⧸I` (surjective); units lift mod nilpotent ideals (elementary: `ab = 1 + n`, `n` nilpotent ⟹ `1 + n` unit) |
  | "lift `P₀` to an `N`-torsion point … `E[N]` smooth? Yes, since `[N]` is smooth" | `torsionπ_etale` [BB-DIFF] restricted to the affine chart (§2δ), then `Algebra.FormallySmooth.lift` (`RingTheory/Smooth/Basic.lean:151`, verified: stated for `IsNilpotent I`) |
  | "(We apply this to `[N]` composed with the structure map …)" | **deviation**: his composition remark shows `E` smooth over `A`, not `E[N]`; the standard reading (KM 2.3.5) is base change of the étale `[N]` along the zero section — which is precisely `torsion := pullback (mulByHom N) zero` + `MorphismProperty.pullback_snd` (the PROVEN `torsionπ_etale` derivation). Mirrored via the standard reading; flagged as source-text slip, mathematics unchanged. |
  | "Hence `(E₀,P₀)` lifts to `(E,P)`, and we are done." | the lifted `(E,P)` is re-normalised: T-E1 (PROVEN) gives the unique variable change to Tate form marking `P` at `(0,0)`; over `A₀` the change reduces to the **identity** by T-E1-uniqueness (the pair was already normalised), so `(α',β') ≡ (α₀,β₀) mod I`; fibrewise exact order persists (`Spec A ≅ Spec A₀` as spaces with equal residue fields), so Y1-D1 lands the corrected classifying map in `yOne`, lifting `f₀`. This re-normalisation is the bookkeeping Loeffler's prose elides when passing from pair-lifting to map-lifting — flagged, adjudicated sound. |
- **Attacks**: (1) *Does the torsion lift stay in the chart?* Only its existence in
  `E[N] ∩ chart` is claimed — the lifting is against that scheme itself, so tautologically ✓
  (§2δ). (2) *Orders on `Spec A` vs `Spec A₀`*: nilpotent kernel ⟹ same points and residue
  fields — `P` and `P₀` have identical fibrewise multiples; needed both for T-E1's
  applicability (`NowhereOrderLEThree` unit input via B2-ii) and for the final Y1-D1
  membership. (3) *`∃!` not claimed*: only surjectivity (formal smoothness), matching
  Prop 3.4.3's "surjective"; uniqueness would be étaleness of `Y₁(N)` — FALSE (relative
  dimension 1) — statement shape verified not to overclaim. (4) *`hf₀` compatibility
  direction*: `Spec.map` contravariance checked (the composite `φ ≫ ofHom (mk I)` gives
  `Spec (A⧸I) → Spec R` ✓ — this type-checked in the green build). (5) Loeffler's criterion
  needs the lift *as a morphism over `R`* — the `f ≫ yOneStructMap = Spec.map φ` conjunct is
  in the statement ✓.
- **Discharge**: gates [BB-DIFF]; consumes T-E1 (proven), Y1-D1, Y1-D3, B2-i/ii substrate.
  **LOC ~220** (Loeffler's 8-line proof × the observed repo ratio for
  representability-mediated arguments).

### Y1-E6 `yOneStructMap_smooth`
- **Source**: Thm 3.4.4, p. 15 (headline, verbatim §1b) + Prop 3.4.3 (the criterion; §2γ
  upgrade).
- **Match**: mathlib `Smooth = HasRingHomProperty RingHom.Smooth`,
  `RingHom.Smooth = Algebra.Smooth = FormallySmooth ∧ FinitePresentation` (verified,
  `RingTheory/RingHom/Smooth.lean:74`). With `yOne` affine (E2): `Smooth (yOneStructMap) ↔`
  `RingHom.Smooth (R → Γ(yOne))` via `HasRingHomProperty.Spec_iff` (verified,
  `Morphisms/RingHomProperties.lean:357`) + iso-transport along `yOne ≅ Spec Γ(yOne)`.
  `FormallySmooth`: an `AlgHom Γ(yOne) → B⧸I` is a `Spec (B⧸I)`-point over `R` (Γ–Spec), which
  Y1-E5 lifts; `FinitePresentation`: Y1-E4 through the same dictionary.
- **Attacks**: (1) *Square-zero vs nilpotent*: `Algebra.FormallySmooth` is defined against
  square-zero; Y1-E5 is stated for nilpotent (stronger input demand, weaker to prove? — NO:
  square-zero ⊂ nilpotent, so E5 covers it; direction checked). (2) The Γ–Spec plumbing
  (AlgHom ↔ over-`R` scheme map for the affine `yOne`): `ΓSpec.adjunction` + `isoSpec` —
  standard, budgeted. (3) *Is `Smooth` the right mathlib target?* — the held statement uses
  `AlgebraicGeometry.Smooth` (checked: `open AlgebraicGeometry` in the held file, class
  `Smooth` at `Morphisms/Smooth.lean:62`) ✓ same constant.
- **Discharge**: assembly (E2+E4+E5, mathlib dictionary). **LOC ~120**.

### Y1-F1 `representableBy_smooth_isAffineHom`
- **Source**: the held T-E7 statement's `∀ X` conjunct (its docstring: "General `R` follows …
  (`Smooth`, `IsAffineHom` stable)"); mathematically: representing objects are unique up to
  iso — Loeffler's "eq. classes" functor language, p. 14.
- **Match**: `Functor.RepresentableBy.uniqueUpToIso` (verified, `CategoryTheory/Yoneda.lean:343`)
  gives `X ≅ yOneEllObj` in `Ell/R`; an `Ell/R`-iso has `baseHom` an isomorphism of schemes
  (inverse from the inverse morphism; `IsIso` from the iso structure) commuting with
  `structMap` (the `base_w` field); `Smooth`/`IsAffineHom` respect isos
  (`MorphismProperty.RespectsIso`, both mathlib instances) ⟹ transport from Y1-E6 + Y1-E3.
- **Attacks**: (1) Is `baseHom` of an `Ell/R`-iso really an iso? — `(e.hom ≫ e.inv).baseHom =
  𝟙` by functoriality of the `baseHom` projection (a functor `EllObj R ⥤ Scheme` exists
  implicitly; 5-line proof). (2) `structMap` compatibility direction: `base_w : baseHom ≫
  Y.structMap = X.structMap` — precisely `MorphismProperty.cancel_left_of_respectsIso` shape ✓.
  (3) Both conjuncts transported through the same iso — no mixing of different representing
  data.
- **Discharge**: mathlib + E3/E6/D3. **LOC ~45**.

### Y1-MASTER `gammaOneNaive_representable_assembly` — NO OWN SORRY (already assembled)
- Statement byte-identical to the held `gammaOneNaive_representable` conclusion; proof term
  `⟨⟨⟨yOneEllObj R N, yOne_representableBy R N hN hinv⟩⟩, fun X hX =>
  representableBy_smooth_isAffineHom R N hN hinv X hX⟩` — type-checked in the green build.
  Once the leaves land, the held theorem closes by
  `exact gammaOneNaive_representable_assembly R N hN hinv` (a one-line edit for whoever holds
  Representability.lean).

---

## 5. Definitions and their opaque interfaces (v10.24(b) discipline)

| heavy def | interface shipped in the same file |
|---|---|
| `tateUniversal` (choose of gate T-A6b) | `tateUniversal_geom` (geometry pin) |
| `tatePoint` (choose of Y1-B2) | `tatePoint_nowhereGeomOrderLEThree`, `tatePoint_classifies` |
| `killedLocus` (concrete pullback) | `killedLocusπ_isClosedImmersion`, `killedLocus_spec`, `mem_killedLocus_range_iff` |
| `yOne` (concrete `Opens.toScheme`) | `factors_yOne_iff` (the `_spec`), `yOne_isAffine` |

No `maxHeartbeats` anywhere; the two `choose`-defs are exactly the LevelSpaces (T-W8) pattern.

## 6. Provability audit summary (per binding discipline (6))

- **mathlib-discharged** (names verified to exist in the pinned mathlib): Y1-A2, Y1-A3, Y1-C3,
  Y1-C4, Y1-C5, Y1-E3 — 6 leaves. Key verified names:
  `Algebra.FormallySmooth.lift` (nilpotent form), `RingHom.Smooth`,
  `HasRingHomProperty.Spec_iff`, `Functor.RepresentableBy.uniqueUpToIso`,
  `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`,
  `Flat.epi_of_flat_of_surjective`, `IsFinite extends IsAffineHom`,
  `HasAffineProperty @IsAffineHom`, `FormallyUnramified → IsOpenImmersion (pullback.diagonal)`,
  `Etale → Smooth` instance, `isAffine_of_isAffineHom`.
- **project-discharged** (cited decl verified sorry-free): Y1-B1 (from
  `universalCurve_localModel`, WeierstrassAtlas.lean — 0 sorries), Y1-C1 (pattern
  `torsionι_isClosedImmersion`, proven), Y1-C2 (`point_smul_eq_comp_mulBy`, `Point.pull_zsmul`,
  `asSection_zsmul` — all proven), Y1-E4 (`FinitePresentationCancel` pattern of the proven
  `mulByHom_locallyOfFinitePresentation`). T-E1/T-E2 chains verified sorry-free
  (TateNormalForm.lean: 0 sorries; Representability.lean's sorries are only at lines
  204/212/225/250/264 — none in T-E1/T-E2).
- **API-GAP with sub-tree**: Y1-B2 (subtree §4/B2-i…vi; gates T-W7, T-A6b), Y1-D2 (gate
  T-E4-family), Y1-E1 (gate BB-DIFF + one bounded sub-leaf), Y1-E5 (gate BB-DIFF), and the
  assemblies Y1-D1/D3/E2/E6/F1 which are gap-free but consume the above.

## 7. Named gates (cited, tracked, NOT rebuilt)

| gate | decl (file:line) | discharges | consumed by |
|---|---|---|---|
| **[T-A6b]** | `abelEnrichment_exists` `GroupLaw.lean:75` (sorry) | canonicity/purity stream (Abel; or T-W7 chart group law lands a constructive enrichment) | `tateUniversal` |
| **[T-W7]** | `pointedIso_exists_variableChange` `Comparison.lean:126`, `projModelVCIso_injective` `:139` (sorries; A-lane in flight) | A-lane T-W7.1b | Y1-B2 subtree (iii), (v) |
| **[BB-DIFF]** | `mulByHom_formallyUnramified` `Torsion.lean:228` (sorry; MASTER route `mulByHom_formallyUnramified'` in `MulByHomUnramified.lean` = L-A ∘ L-BC, L-A proven-route in flight) | T-B5D stream | Y1-E1, Y1-E5 (via proven-modulo-gate `torsionπ_etale`) |
| **[T-E4-family]** | `EllHom.pullSection_add` `Representability.lean:204` + `map`-membership sorries `:212` (held file) | GME 2.2.5 canonicity chain (A6.δ) | Y1-D2 (coordinate the discharge: prove the transport once, close both) |

Deliberately NOT gates: KM 2.3.1 boxes BB-QF/BB-FLAT (dodged by §2δ), T-D6b/T-D6c (dodged by
§2β), T-D33/T-W8 level-space machinery (alternative route, not consumed).

## 8. Build evidence

```
$ lake build ModularCurves.ModularCurve.YOneAssembly     # 2026-07-08, repo root
⚠ [3093/3093] Built ModularCurves.ModularCurve.YOneAssembly (3.5s)
Build completed successfully (3093 jobs).
# warnings: exactly the 19 sorried leaves of this file + pre-existing upstream sorries; the
# MASTER bridge produced no sorry warning (term-assembled).
```
Module registered in `projects/ModularCurves/ModularCurves.lean`
(after `ModularCurves.ModularCurve.YRho`). Nothing committed (per stream instructions).
