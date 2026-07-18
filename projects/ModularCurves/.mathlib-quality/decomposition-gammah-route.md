# Decomposition — STREAM-GH: Γ_H relative representability (T-H4) and the route to T-H6

*(/develop --decompose planning pass, 2026-07-08, stream-GH worker. Sources read IN FULL:
Loeffler `modcurvesnotes.pdf` §3.6–3.8 (Prop 3.8.2 + proof, Fact 3.8.1, Prop 3.8.3, Prop
3.6.1, the Y₀(N) ι_S discussion, Thm 3.7.4); KM `katz-mazur-arithmetic-moduli-FULL.pdf`
(PDF = print + 11): Ch. 7 pp. 186–189 (7.1.1, 7.1.2, THEOREM 7.1.3 — the quotient-problem
formalism Loeffler's one-sentence quotient step compresses), Ch. 4 pp. 111–112 (4.6.2,
SCHOLIE 4.7.0 + engine), pp. 116–117 (COROLLARY 4.7.1, 4.7.2), Ch. 3 pp. 104–105
(THEOREM 3.7.1 + proof head — the KM analogue of the H = 1 half).
Skeleton: `ModularCurves/Moduli/GammaHRepresentability.lean` (NEW). Held files
`Moduli/GammaH.lean`, `Moduli/Representability.lean`, `ForMathlib/InvariantTorsor.lean`
were read but NOT touched; all bridges live in the new file.)*

---

## 0. THE ADVERSARIAL FINDING OF RECORD (F1) — the held T-H4/T-H6 statements are FALSE for H ≠ ⊥

**This supersedes the 2026-07-06 attack-file verdict** (`decompose-attacks-2026-07-06/
levels-stack.md`, "`gammaHNaive_relativelyRepresentable` … [FALSITY] As stated: TRUE"),
which audited source fidelity and the étale-conjunct drift but did not run the
disjoint-base attack. **B2 statement event — owner + H-lane holder decision required;
nothing in the held file was edited.**

**The defect.** `gammaHNaiveProblem R N H` (GammaH.lean:379) has
`obj X := Quotient (X.unop.curve.hOrbitSetoid H)` — H-orbits of *global* full level
structures under a *single* group element (`hOrbitSetoid`: `L ≈ L' ↔ ∃ g ∈ H, glSmul g L
= L'`). A representable functor on `Sch/S` is a Zariski sheaf; in particular restriction
to the two components of `T = T₀ ⊔ T₀` is *jointly injective* on `Hom(T, Z)`. The naive
orbit presheaf is not separated for that cover:

> Take any `X : EllObj R` with `Nonempty X.base` carrying a naive full level structure
> `L` (such `X` exist for every nontrivial `R` with `N` invertible — e.g. the tautological
> point over `levelSpaceΓ` itself), and `γ ∈ H`, `γ ≠ 1`. Over `T = X.base ⊔ X.base` the
> classes `[(L, L)]` and `[(L, γ·L)]` restrict equally to both components (`[γ·L] = [L]`!)
> but are distinct: `h·(L,L) = (L,γL)` forces `h·L = L`, and the `H`-action on full level
> structures over a nonempty base is **free** (a fixed structure pins a basis of
> `E[N](k̄) ≅ (ℤ/N)²` at a geometric point, forcing `h = 1` — here `hinv` enters), so
> `h = 1 = γ`. Contradiction with `RelativelyRepresentable`'s naturality clause.

The **second conjunct** of the held T-H4 (finite étale, objectwise `Nonempty (≃)`, no
naturality) dies by counting: for `X` over `Spec k̄` (`N` invertible in `k̄`),
`|Lev(k̄)| = |GL₂(ℤ/N)|` and the `H`-action is free, so over `m` disjoint copies the
naive problem has `|GL₂|^m / |H|` elements while any scheme's `Hom`-side has `c^m`;
`m = 1, 2` force `|H| = 1`. The held **T-H6** asserts `.Representable` of the same naive
functor, which fails the same attack (representables on `Ell/R` split over
disjoint-base objects, since `EllHom`s out of a coproduct-base object split
componentwise); refuting the *theorem* T-H6 additionally needs one rigid nontrivial `H`
(e.g. `N = 4`, `H` = upper unipotent, over `ℂ` — Loeffler 3.8.3), which is T-H5
machinery, so T-H6-held is recorded as *defective by inheritance*, not separately
refuted in Lean.

**The sources agree — this is not a source discrepancy but a transcription bug.**
Loeffler *never defines* `P_H(E/S)` as naive orbits. Fact 3.8.1 (verbatim): "**There
exists a moduli problem** `P_H` on Ell/ℤ[1/N] **such that if `k̄` is algebraically
closed**, `E/k̄ ∈ Ob(Ell/ℤ[1/N])`, then `P_H(E/k̄) = {H-orbits of isomorphisms
(ℤ/N)² ≅ E[N]}`" — the orbit description is pinned *only over `k̄`*. His §3.6 (the Y₀(N)
construction) makes the mechanism explicit for the map from naive pairs, verbatim: "In
general, this is **neither injective nor surjective**, but if `S = Spec(k̄)` for `k̄`
algebraically closed, then it is bijective". KM define the general-H problem as the
KM 7.1.2 *quotient problem* `𝒫/G`, pinned by (Q1)+(Q2) below — sections of the quotient
*scheme*, not naive orbits of sections.

**Consequence for this stream.** The corrected development formalises KM 7.1.2/7.1.3
(which is exactly what Loeffler's sentence "For general H just take the quotient of this
by H" *means*), states the corrected T-H4/T-H6 against the quotient problem in the NEW
file, keeps the naive `gammaHNaiveProblem` as the *source of the H-action* and bridges
it by (i) the `⊥`-instance (where the held statement IS true and is discharged), (ii)
the comparison map + its geometric bijectivity (= Loeffler Fact 3.8.1, now a theorem),
(iii) an explicit refutation lemma [GHC4] recording F1 in Lean.

---

## 1. Prose proof of record (Loeffler 3.8.2, his structure preserved; KM 7.1 filling his second sentence)

**Statement (Loeffler Prop 3.8.2, verbatim).** "P_H is relatively representable and
étale over Ell/ℤ[1/N] (i.e. for all E/S ∈ Ob(Ell/ℤ[1/N]), the functor T ↦ P_H(E ×_S T)
is represented by an étale S-scheme)." *(The module docstring of the held GammaH.lean
also quotes "… finite étale"; KM 3.7.1's conclusion is "a finite etale S-scheme", and
KM 4.7.1's hypothesis is "affine and etale over (Ell)". We carry `IsFinite ∧ Etale`.)*

**Loeffler's proof, verbatim and complete.** "For H = {1}, for E/S ∈ Ob(Ell/ℤ[1/N]), we
can find an explicit S-scheme representing P_H on Sch/S; it is an open subscheme of
E[N] ×_S E[N] given by non-vanishing of Weil pairings. For general H just take the
quotient of this by H."

### Step 1 (H = 1): the level scheme `Lev = levelSpaceΓ E N` is finite étale and relatively represents `[Γ(N)]`-naive.

A naive full level structure on `E_T/T` is a pair of `N`-torsion sections generating
`E[N]` fibrewise (Fact 3.8.1's `Γ(N)` row, verbatim: "pairs of sections P, Q ∈ E[S]
generating E[N] in every fibre"). Pairs of killed points over `t : T → S` are exactly
`T`-points of `E[N] ×_S E[N]` (the project's `pointToTorsion` dictionary). The project
already has the *Drinfeld* full-level locus as a closed subscheme
`levelSpaceΓ E N ⊆ E[N] ×_S E[N]` with classifying property `levelSpaceΓ_spec`
(T-D18/T-W8, PROVEN modulo registered boxes), and over `N`-invertible bases Drinfeld =
naive (`isFullLevel_iff_naive`, T-D8). So `{h : T → Lev over S} ≃ {naive full level
structures on E_T}`, naturally in `T` — relative representability.

Finiteness: `Lev → E[N] ×_S E[N]` is a closed immersion and `E[N] → S` is finite
(KM 2.3.1 = the registered T-B4 boxes `torsionπ_isFinite`), so the composite is finite.

Étaleness is the *only* place the Weil pairing enters, exactly as in Loeffler.
Unramifiedness is free (closed immersion into the étale `E[N]² / S` — `torsionπ_etale`,
T-B5′, PROVEN); the content is *flatness/openness*: `Lev` is the preimage under
`e_N : E[N] ×_S E[N] → μ_N` (DS4 `weilPairing`) of the *primitive* locus
`μ_N^× ⊆ μ_N`, which over `ℤ[1/N]` is open and closed (`μ_N = ⊔_{d ∣ N} μ_d^prim`
étale-locally); a clopen subscheme of the finite étale `E[N]²` is finite étale over
`S`. [KM's route to the same clopen-ness, THM 3.7.1's proof: "Because N is invertible
on S, the group-scheme E[N] is finite etale over S, locally (etale) isomorphic to
(ℤ/Nℤ)² (cf. 2.3.1). The assertion for Γ(N) … results immediately from 1.6.7" — the
condition is clopen on the étale-locally constant form and descends. Both routes are
recorded on the leaf.]

### Step 2 (general H): the KM 7.1 quotient. *(Loeffler: one sentence; KM 7.1.1–7.1.3 is the actual content.)*

- **The action** (KM 7.1.1): `H ≤ GL₂(ℤ/N)` acts on the full-level problem by
  precomposition (Fact 3.8.1; the project's `glSmul`, whose action law `glSmul_mul` is
  a *right* action — the homomorphism into `Aut` is `γ ↦ (glSmul γ⁻¹)`), compatibly
  with all cartesian squares (KM diagram 7.1.1.1 — in this project precisely the T-H3
  orbit-compatibility of `pullSection`, gated on `pullSection_add`). KM 7.1.1's closing
  sentence: "If 𝒫 is relatively representable, then for every E/S, the group G acts on
  the S-scheme 𝒫_{E/S}" — the action transports through the representing data.
- **Freeness** (needed for the étale conjunct and base-change): `H` acts freely on
  naive full level structures over any nonempty base — a fixed structure pins a basis
  of `E[N](k̄) ≅ (ℤ/N)²` at a geometric point (here `N` invertible enters), forcing
  `γ = 1`. This is KM 7.1.3(2)'s hypothesis "G operates freely on 𝒫, in the sense that
  for every E/S/R, G operates freely on the set 𝒫(E/S)" (honest Lean form: over
  nonempty bases).
- **The quotient scheme**: `Lev_{E/S} → S` is affine (finite), so the pulled-back
  affine opens of `S` are an `H`-stable affine atlas and the T-Q3/T-Q5 machinery
  (`SchemeAction.quotient`, sorry-free) produces `Lev/H`, the finite projection `π`
  (KM 7.1.3(4)), and the descended structure map `f₀ : Lev/H → S`
  (`existsUnique_quotientπ_lift`). Loeffler's own quotient tool is Prop 3.6.1
  (quasiprojective X; "for X = Spec(A) affine, Spec(A^G) works, and one can show that
  these patch nicely") — our affine-over-base case is exactly the patching case.
- **Torsor + base change** (the crux): freeness makes `π : Lev → Lev/H` a finite étale
  `H`-torsor (KM 7.1.3(2); A7.1.1 = SGA III Exp. V Thm 4.1 = the InvariantTorsor
  layer: torsor iso PROVEN, étale gated on [A711-FP], noetherian version PROVEN), and
  makes quotient formation commute with arbitrary base change `T → S`
  (KM 7.1.3(3c): the natural map "(𝒫_{E/S})/G → (𝒫/G)_{E/S} … is an isomorphism if
  … c) G operates freely on 𝒫"; algebra core = A7.1.2 =
  `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`, SORRIED, [A711-BC]).
- **The quotient problem** (KM 7.1.2): `P_H := [Γ(N)]/H` is *defined* by (Q1) trivial
  `H`-action + (Q2) "for every modular family of elliptic curves E/S/R, the quotient
  scheme (𝒫_{E/S})/G exists, and maps isomorphically to (𝒫′)_{E/S}". Base-change
  compatibility is what makes `T ↦ (Lev/H ×_S T-sections)` a *functor on Ell/R* at
  all; KM 7.1.3(1) gives existence + the universal property ("any G-equivariant map
  𝒫 → 𝒫′ [𝒫′ relatively representable, trivial action] factors uniquely through
  𝒫 → 𝒫/G"). `f₀ : Lev/H → S` is finite étale: descend both properties along the
  faithfully flat finite étale surjection `π`.
- **Geometric fibres** (Loeffler Fact 3.8.1's pin; KM 7.1.3(3) "bijective on geometric
  points"): over `Spec k̄` every `H`-torsor is trivial, so sections of `Lev/H` over
  `k̄` are exactly `H`-orbits of `k̄`-points of `Lev` — `P_H(E/k̄) = {H-orbits of full
  level structures}`.

### T-H6 (corrected route, unchanged shape): T-E5 + T-H4.

`P_H` relatively representable by *finite* (hence affine) étale morphisms gives
`P_H.AffineOverEll`; the amended T-E5 (`representable_iff`, KM SCHOLIE 4.7.0 verbatim,
B2 2026-07-08) then gives `P_H representable ↔ rigid`. This is KM 4.7.1's shape:
"Any relatively representable moduli problem 𝒫 which is affine and etale over (Ell),
and rigid, is representable by a smooth affine curve over ℤ" and 4.7.2: "For N ≥ 3, the
naive level N moduli problems of 4.6 is representable, by a smooth affine curve Y(N)
over ℤ[1/N]. Proof. This results from 4.7.1 above, thanks to the rigidity 2.7.2 and the
relative representability 3.7.1 of naive level N structures." The smooth-affine-curve
conjunct of the held T-H6 is NOT reproduced here (it needs KM 4.7.1's smoothness
argument, a separate chain); the drift is recorded, matching the 2026-07-06 attack
file's fidelity note.

---

## 2. Ordered decomposition (skeleton = `Moduli/GammaHRepresentability.lean`; every leaf `:= by sorry` unless marked def/no-sorry)

Naming: `GH0x` vocabulary/action · `GHAx` H = 1 (Loeffler sentence 1) · `GHBx` quotient
(Loeffler sentence 2 / KM 7.1) · `GHCx` Γ_H conclusions + bridges + refutation.
Gates legend: ⛩[A711-FP], ⛩[A711-BC] (InvariantTorsor sorries), ⛩[DS4/T-C1]
(weilPairing layer, CHARTER-P2), ⛩[T-E4a] (`pullSection_add`, parked behind T-W7.8;
loc-noetherian version PROVEN), ⛩[T-E5-engine] (representable_iff ⇐, T-Q6e/T-E14/15).

### PART 0 — vocabulary and the action

**[GH0a] `ModuliProblem.FreeAction`** (def, no sorry). KM 7.1.3(2) verbatim: "G operates
freely on 𝒫, in the sense that for every E/S/R, G operates freely on the set 𝒫(E/S)".
Lean: `∀ X, Nonempty X.base → ∀ γ ≠ 1, ∀ a, (φ γ).hom.app (op X) a ≠ a`.
*Lean ↔ source*: KM quantify over all E/S; over the empty base every action fixes the
(unique or empty) value set, and KM never meet ∅ — the nonempty-base guard is the
honest transcription (same adjudication as T-H7's DEF-1 and
`simulSchemeAction_free_of_rigid`'s `IsEmpty T` convention).
*Attacks*: (1) ∅-base: unguarded form is unsatisfiable for our instance (singleton value
set over ∅ is fixed) — guard necessary. (2) "free on orbits" vs "free pointwise": KM say
free on the *set* 𝒫(E/S) — pointwise ✓. (3) quantifying `a` before `γ` vs after:
equivalent; order as stated matches "operates without fixed points".
*Provability*: definition. **LOC 10.**

**[GH0b] `EquivariantRelRepData`** (structure, no sorry) extends
`ModuliProblem.RelRepData` (QuotientProblem.lean, T-Q6, PROVEN vocabulary) by:
`σZ : SchemeAction G Z`, `over_base : σZ.hom γ ≫ f = f`, `equivariant` (the same field
shape as `TorsorData.equivariant`, T-Q6 attack-adjudicated convention), `finite :
IsFinite f`, `etale : Etale f`. This is `TorsorData` *minus* `surjective`/`torsor` —
those two are the *torsor* axioms (true only for the full `GL₂`-action on `Lev`, false
for `H ⊊ GL₂`), while ours is the "𝒫 relatively representable, G acts, 𝒫_{E/S} finite
étale" package of KM 7.1.1 + 3.7.1.
*Verbatim (KM 7.1.1)*: "If 𝒫 is relatively representable, then for every E/S, the group
G acts on the S-scheme 𝒫_{E/S}."
*Attacks*: (1) reuse TorsorData? — REJECTED: its `torsor` field is FALSE for proper
subgroups (a `|GL₂/H|`-sheeted quotient is not an `H`-torsor over `S`). (2) drop
`finite`, keep only étale (Loeffler's bare statement)? — kept: KM 3.7.1 concludes finite
étale, and T-H6 needs affineness (KM 4.7.0's hypothesis; the v10.27 amendment's whole
point). (3) equivariance convention (pre- vs post-composition): copied verbatim from
`TorsorData.equivariant` (attack-adjudicated in q-lane.md) so the two structures stay
interoperable. **LOC 25.**

**[GH0c] `QuotientProblemData`** (structure, no sorry) — the KM 7.1.2 quotient problem,
bundled: `prob : ModuliProblem R`, `proj : Q ⟶ prob`, `proj_invariant` (Q1-side:
`(φ γ).hom ≫ proj = proj`), `relRep : ∀ X, ∃ d : RelRepData prob X, IsFinite d.f ∧
Etale d.f` (7.1.3(1) + the étale conjunct), `couniversal` (7.1.3(1) verbatim: "For any
relatively representable 𝒫′, with trivial G-action, any G-equivariant map 𝒫 → 𝒫′
factors uniquely through the projection 𝒫 → 𝒫/G" — the rel-repr restriction on `𝒫′` is
KM's, kept), `geom_surjective` + `geom_orbits` (7.1.3(3) "bijective on geometric
points" + Loeffler Fact 3.8.1's `k̄`-pin, split into surjectivity and
fibres-are-orbits at objects over `Spec k̄`).
*Verbatim (KM 7.1.2)*: "(Q1): G operates trivially on 𝒫′. (Q2): For every representable
moduli problem δ on (Ell/R) which is etale over (Ell/R), the quotient scheme 𝕸(δ,𝒫)/G
exists, and it maps isomorphically to 𝕸(δ,𝒫′). [Equivalently: for every modular family
of elliptic curves E/S/R, the quotient scheme (𝒫_{E/S})/G exists, and maps
isomorphically to (𝒫′)_{E/S}.]"
*Lean ↔ source*: (Q1) is implied by `proj_invariant` + geometric surjectivity on the
image but is not needed as a separate field for any consumer — the couniversal field is
the working handle (it is what pins `prob` up to canonical iso, which is what "'the'
quotient" means). (Q2)'s quotient-scheme identification is not a *field* — it is
delivered by the assembly theorem [GHB7] whose construction takes `prob`'s representing
data to *be* the quotient schemes; carrying it as data would force the field to name a
chosen quotient construction, freezing T-Q5 internals into the public structure.
*Attacks*: (1) is `couniversal` false at non-sheafy `P'`? — the restriction to
`P'.RelativelyRepresentable` is verbatim KM and dodges exactly that. (2) geometric
clauses at `Spec k` non-closed: twists break bijectivity (Loeffler §3.6 verbatim:
"There exist obstructions coming from quadratic twists") — clauses require
`IsAlgClosed k` ✓. (3) should `geom_orbits` state a `Quotient`-equiv instead of the
two clauses? — the two-clause form avoids `Quotient` plumbing and is what consumers
(GHC3, rigidity-transfer) actually use. **LOC 45.**

**[GH1] `gammaHAut : ↥H →* Aut (gammaFullNaiveProblem R N)`** (DATA-SORRY, register
entry **DS-GH1**, + spec `gammaHAut_app_val` sorried) — the Fact 3.8.1 action, `γ`
acting by `glSmul (γ⁻¹ : GL₂)` on values (inverse because `glSmul_mul` is a RIGHT
action law — the 2026-07-06 adversarial fix in the held file — and `Aut`-valued
homomorphisms are left actions).
*Verbatim (Loeffler Fact 3.8.1)*: "P_H(E/k̄) = {H-orbits of isomorphisms (ℤ/N)² ≅ E[N]}"
— the H-set structure on full level structures. *(KM 7.1.1)*: "G operates on 𝒫 if for
every … E/S, the group G operates on the set 𝒫(E/S) in such a way that for every
morphism in (Ell/R) … the obvious diagram of actions below commutes" (7.1.1.1).
*Lean ↔ source*: naturality of the component maps = diagram 7.1.1.1 = compatibility of
`glSmul` with `pullSection` — literally the same content as the two `by sorry`s inside
the held `gammaHNaiveProblem.map` (T-H3), gated the same way.
*Attacks*: (1) hom vs anti-hom: `glSmul_mul : (g*h) • L = h • (g • L)`, so `γ ↦ glSmul γ`
is an anti-hom; `γ ↦ glSmul γ⁻¹` is a hom — pinned in the spec, checked against
`Aut`'s group structure at discharge. (2) membership preservation (glSmul lands in
level structures): already proven in the held file (`glSmul`'s construction). (3) the
naturality needs `pullSection` additive — ⛩[T-E4a]; the loc-noetherian
`pullSection_add_of_isLocallyNoetherian` (Moduli/PullSectionAdd.lean, PROVEN) covers
every geometric consumer of this stream when T-W7.8 lags.
*Provability*: gated ⛩[T-E4a]. **LOC 60 (with spec).**

**[GH2] `gammaFullNaive_freeAction`** — `hinv : IsUnit (N : R)` ⟹
`FreeAction (gammaHAut R N H)` (for the induced `↥H`-action; equivalently stated for
the full `GL₂`).
*Verbatim (KM 7.1.3(2) hypothesis)* as in GH0a; the mathematical content is the
standard "a `GL₂(ℤ/N)`-matrix fixing a basis of `(ℤ/N)²` is 1".
*Lean ↔ source*: fixed structure `glSmul γ⁻¹ L = L` over nonempty base; take the
geometric point (`EllObj.exists_geometricPoint`, held file, PROVEN), where
`E[N](k̄) ≅ (ℤ/N)²` (`torsion_geometricFibre_rank_two`, PROVEN) and the pulled pair
generates by the level clause; a generating pair of `(ℤ/N)²` killed by `N` is a basis
(counting: `Fintype.card` of the closure), and the fixing equations
`(γ₁₁−1)P + γ₂₁Q = 0`, `γ₁₂P + (γ₂₂−1)Q = 0` (from `Subtype.ext` on `glSmul`) pull to
the fibre and kill the columns of `γ − 1` mod `N`.
*Attacks*: (1) `N = 1`: `GL₂(ℤ/1)` is trivial so every `H` is `⊥` and freeness is
vacuous ✓. (2) char `p ∣ N` fibres would break the rank-2 count — excluded by `hinv`
(this is why the leaf carries it; the held T-H4 carries the same). (3) nonempty-base
guard necessary (GH0a attack 1) ✓. (4) generating-pair-is-basis needs killed-by-`N`
(else `(1, P)` generates without being a basis) — the level clause supplies killing ✓.
*Provability*: NOW — all inputs PROVEN in-repo (`exists_geometricPoint`,
`torsion_geometricFibre_rank_two`, `glSmul` arithmetic lemmas, mathlib `ZMod`/`Fintype`
counting). **LOC 150.**

### PART A — H = 1: Loeffler's "open subscheme of E[N] ×_S E[N]" (in-repo: the T-D18 locus, étale-upgraded)

**[GHA1] `levelSpaceΓπ`** (def, no sorry): the structure morphism
`levelSpaceΓ E N ⟶ S` := `levelSpaceΓι ≫ pullback.fst ≫ torsionπ`.
*Attacks*: (1) fst vs snd branch — symmetric over `S`, pin fst. (2) matches
`levelSpaceΓ_spec`'s classifying convention (`pullback.lift (pointToTorsion P) …`) ✓.
(3) definitional transparency wanted by GHA2 — keep an `abbrev`-grade `@[simp]` unfold
lemma. **LOC 8.**

**[GHA2] `levelSpaceΓπ_isFinite`** — `IsFinite (levelSpaceΓπ E N)`.
*Verbatim (KM 3.7.1 conclusion)*: "Each is represented by a finite etale S-scheme."
*Route*: `subschemeι` is a closed immersion (mathlib `IdealSheafData` API) ⟹ finite;
`pullback.fst` of the finite `torsionπ` is finite (stability under base change);
`torsionπ_isFinite` (T-B4 registered box); composition.
*Attacks*: (1) axiom provenance: inherits `sorryAx` through the registered T-B4/T-D3
boxes ONLY — same profile as the whole T-D17/T-D18 chain, acceptable and tracked. (2)
mathlib names: `IsFinite` stability instances exist (`MorphismProperty` framework —
verified present by TorsorData's use). (3) no `hinv` needed (finiteness is
characteristic-free) ✓ — matches KM 1.5/1.6 loci being defined over anything.
*Provability*: NOW. **LOC 25.**

**[GHA3] `levelSpaceΓπ_etale`** ⛩[DS4/T-C1] — `NIsInvertible S N → Etale (levelSpaceΓπ E N)`.
**The Weil-pairing leaf — the only leaf where Loeffler's named device enters.**
*Verbatim (Loeffler 3.8.2 proof)*: "it is an open subscheme of E[N] ×_S E[N] given by
non-vanishing of Weil pairings." *(KM 3.7.1 proof)*: "Because N is invertible on S, the
group-scheme E[N] is finite etale over S, locally (etale) isomorphic to (ℤ/Nℤ)²
(cf. 2.3.1). The assertion for Γ(N) … results immediately from 1.6.7 applied to
E[N]/S."
*Lean ↔ source*: our `levelSpaceΓ` is KM's *closed* Drinfeld locus; over `ℤ[1/N]` it
coincides with Loeffler's *open* Weil-pairing locus, i.e. it is CLOPEN in the finite
étale `E[N] ×_S E[N]`; clopen-in-finite-étale ⟹ finite étale over `S`. Unramifiedness
is already free (closed immersion into étale); the pairing supplies OPENNESS (⟺
flatness here).
*Routes (both recorded, either discharges)*: (a) **Loeffler**: `Lev = (weilPairing)⁻¹
(μ_N^×)` where `μ_N^× ⊆ μ_N` is the primitive-root clopen over `ℤ[1/N]` — consumes DS4
`weilPairing` + `weilPairing_over` + a new primitivity-locus lemma on `muN` (μ_N
étale: `muNπ_etale_iff` exists) + the fibrewise "pair generates ⟺ e_N(P,Q) primitive"
(KM 2.8.x; fibrewise from `weilPairingEval_nondegenerate`). (b) **KM 3.7.1**:
étale-local trivialisation `E[N] ≅ (ℤ/N)²` (the T-W7-scale input named by
CharZeroDescent.lean's header) + the locus is a union of components of the constant
form + étale descent of clopen-ness. Route (a) is the source-of-record;
(b) is the fallback if the primitivity API outpaces DS4's discharge.
*Attacks*: (1) closed-subscheme-of-étale is NOT étale in general (non-flat examples
over `Spec ℤ`) — openness is genuine content, correctly gated. (2) `NIsInvertible S N`
vs `hinv : IsUnit (N : R)`: implied along `structMap` (unit pushes forward) — the leaf
takes the scheme-level form, the Part C assembly converts. (3) route (a)'s
"non-vanishing" is *primitivity* (`e(P,Q)^{N/p} ≠ 1 ∀ p ∣ N`), not mere `≠ 1` — for
non-prime `N` mere non-vanishing is too weak; the leaf name and statement must say
primitive. (4) is the locus really CLOSED-and-open rather than just open? — closed by
T-D18's construction (incidence EQ-locus), open by the pairing; both needed for
finiteness of the composite. ✓.
*Provability*: GATED (CHARTER-P2 / T-C1). Named gate of record for PART A. **LOC 250
(route a: ~80 primitivity locus + ~120 fibre dictionary + ~50 assembly).**

**[GHA4] `gammaFullNaive_relRepData`** — `∀ X : EllObj R` (with `hinv`):
`∃ d : RelRepData (gammaFullNaiveProblem R N) X, d.Z = levelSpaceΓ … ∧ IsFinite d.f ∧
Etale d.f` — stated as `Nonempty`-existence with the finite/étale conjuncts (the
`d.Z`-pin dropped in the skeleton: the *data* is enough for all consumers).
*Verbatim (Loeffler 3.8.2 proof)*: "we can find an explicit S-scheme representing P_H
on Sch/S". *(KM 3.7.1)*: "Consider the four functors on (Sch/S) given by T ↦
{Γ(N)-structures on E_T/T, …}. Each is represented by a finite etale S-scheme."
*Lean ↔ source*: the equivalence chain
`{h : T → Lev // h ≫ π = g} ≃ {(P,Q) killed T-points, Drinfeld-full-level}`
(`levelSpaceΓ_spec` + `pointToTorsion` dictionary) `≃ {naive full level structures on
E ×_S T}` (`isFullLevel_iff_naive` — needs `NIsInvertible T N`, supplied from `hinv`
along `g ≫ X.structMap`) `= (gammaFullNaiveProblem R N).obj (op (X.pullbackAlong g))`
(the `asSection`/`Section`-of-base-change dictionary, `isNaiveFullLevel_pullAlong`
territory of the held file), plus the `nat` field: restriction along `k : T' → T` on
both sides (naturality of `levelSpaceΓ_spec`'s classifying maps = `pullback.lift`
functoriality; the moduli side is `pullbackAlongMap`-functoriality).
*Attacks*: (1) the spec quantifies over KILLED point pairs with `hP hQ` as *morphism*
equations (`P.1 ≫ mulByHom N = t ≫ zero`) while the moduli side kills via
`(N:ℤ) • P = 0` — the dictionary `fullLevelLocusAux_killed`-style conversions exist
in-repo (Incidence.lean) both ways; a genuine but mechanical seam (the T-D16/18
"asSection/baseChange defeq-straddling" trap notes apply — budget for raw-typed
aliases). (2) naturality is NOT in `levelSpaceΓ_spec`'s statement (it is a per-`t`
iff) — it must be *proven* from `pullback.lift`-uniqueness; this is real work, not a
transcription. (3) which curve does the moduli side see: `X.pullbackAlong g` has curve
`X.curve.baseChange g` — the spec's `E.baseChange t` with `t = g` matches on the nose ✓.
(4) universe: all in `Type u` ✓.
*Provability*: NOW modulo GHA2/GHA3 conjuncts (which it merely repackages) — the
equivalence itself consumes only PROVEN/boxed in-repo API. **LOC 300 (the seam-heavy
leaf of PART A).**

**[GHA5] `gammaFullNaive_equivariantRelRepData`** — upgrade GHA4's data to
`Nonempty (EquivariantRelRepData (gammaHAut R N H) X)` via the generic transport
[GHB1]. *(Assembly-only leaf.)*
*Attacks*: (1) the action on `Z` induced by transport vs the "obvious" geometric
`glSmul`-on-points action: transport is canonical and all consumers use only its spec —
no comparison needed. (2) `Finite ↥H` instance must synthesize (`ZMod` finite ⟹
matrices ⟹ units ⟹ subgroup) — verify at build. (3) `↥H : Type 0` against
`SchemeAction (G : Type*)` — SchemeQuotient's `G` is universe-polymorphic ✓ (checked;
`TorsorData`'s `Type u` pin is NOT inherited since we don't use it).
*Provability*: NOW given GHB1 + GHA4. **LOC 30.**

### PART B — the quotient step (Loeffler: "For general H just take the quotient of this by H"; content = KM 7.1.3)

**[GHB1] `RelRepData.exists_equivariant`** (generic transport; KM 7.1.1 closing
sentence) — for `φ : G →* Aut Q` and `d : RelRepData Q X` with `IsFinite d.f`,
`Etale d.f`: `Nonempty (EquivariantRelRepData φ X)`. The action of `γ` on `d.Z` is the
classifying map of `(φ γ)·(universal element)`: `σγ := (d.eqv d.f).symm ((φ γ).hom.app
_ (d.eqv d.f ⟨𝟙 Z, id_comp⟩)).1 ≫ …` — the relative mirror of T-Q6d's
`RepresentableBy.transportHom/autMulHom` (ForMathlib/RepresentableAut.lean, PROVEN at
the absolute level).
*Verbatim (KM 7.1.1)*: "If 𝒫 is relatively representable, then for every E/S, the
group G acts on the S-scheme 𝒫_{E/S}."
*Attacks*: (1) hom vs anti-hom AGAIN at the transport (values are contravariant in
`T`): the cocycle check `σ(γδ) = σγ ≫ σδ` must be verified against `SchemeAction`'s
convention `hom_mul : hom (g*h) = hom g ≫ hom h` — if it lands anti, absorb by `γ ↦
γ⁻¹` INSIDE this leaf, keeping the public field a genuine `SchemeAction`. (2) the
equivariance field must come out in exactly `TorsorData.equivariant`'s orientation —
derived from `d.nat` at `k := σγ`; if orientation flips, fix here, never in consumers.
(3) `over_base`: from the subtype constraint of the transported universal point ✓
(free). *Provability*: NOW (pure diagram algebra on `d.eqv`/`d.nat`; the absolute
version is already in-repo). **LOC 180.**

**[GHB2] `EquivariantRelRepData.free_on_points`** (final Lean spelling — the
scheme-level form, house shape of `simulSchemeAction_free_of_rigid`'s conclusion:
`t ≫ σZ.hom γ = t → IsEmpty T`; instance-free to state) — moduli freeness (GH0a) +
equivariant data ⟹ no `γ ≠ 1` fixes a `T`-point of `d.Z`, `T` nonempty. The
chart-level Chase–Harrison–Rosenberg form — each stable affine chart ring of GHB3's
atlas satisfies KM A7.1.1's hypothesis, verbatim (InvariantTorsor.lean docstring):
"for any non-zero R-algebra R′, and any element g ≠ id of G, g operates without fixed
points on the set Hom_{R-alg}(A, R′)" (`IsFreeAlgebraAction`) — is DERIVED FROM THIS
inside GHB4/GHB5's proofs (an `R'`-point of a chart is a nonempty-`T`-point of `Z`).
*Lean ↔ source*: an `R'`-algebra point of the chart with `R'` nontrivial is a
`Spec R' ≠ ∅`-point of `Z`, hence (via `d.eqv` at `g := its base composite`) an element
of `Q(E ×_S Spec R')` fixed by `γ` — moduli freeness (nonempty base ⟸ `Nontrivial R'`)
kills it. The equivariance field aligns the two fixings.
*Attacks*: (1) chart-points vs `Z`-points: a chart is an open subscheme; its `R'`-points
ARE `Z`-points ✓ (compose with the open immersion). (2) `SMulCommClass` side conditions
of `IsFreeAlgebraAction` must be produced from the `SchemeAction`-induced
`gammaMulSemiringAction` (SchemeQuotient.lean provides the action; commutation with the
base `ℤ`- resp. `Γ(S,U)`-structure is by construction — check the exact class shape at
execution; InvariantTorsor works over `R := ℤ` in the T-Q3 pattern, dodging the
`Γ(S,U)`-algebra subtlety). (3) fixed algebra point vs fixed Spec-point orientation
(`φ ∘ (γ•)` vs `(γ⁻¹)•`-precompose): pin by unfolding `specSMul`/`gammaMulSemiringAction_smul_def` (both PROVEN, SchemeQuotient). *Provability*: NOW. **LOC 160.**

**[GHB3] `exists_quotient_over_base`** — for equivariant data with `IsAffineHom d.f`
(⟸ `finite`): existence of `(Z₀, π : Z ⟶ Z₀, f₀ : Z₀ ⟶ X.base)` with `π ≫ f₀ = d.f`,
`σZ.hom γ ≫ π = π`, `π` epi (`quotientπ_hom_ext` form), and the descent property
(`∀ F : Z ⟶ Y invariant, ∃! q, π ≫ q = F`).
*Verbatim (Loeffler 3.6.1)*: "for X = Spec(A) affine, Spec(A^G) works, and one can show
that these patch nicely. (One needs quasiprojectiveness and finiteness of G here.)"
*(KM 7.1.3(3))*: "For any E/S/R, the quotient scheme 𝒫_{E/S}/G exists".
*Lean ↔ source*: our patching datum is the `IsAffineHom`-pullback atlas `V x :=
f⁻¹(affine open ∋ f(x))` — stable (`over_base`) and affine (`IsAffineHom.isAffine_preimage`)
— fed to `SchemeAction.quotient/quotientπ/hom_quotientπ/quotientπ_hom_ext/
existsUnique_quotientπ_lift` (ForMathlib/SchemeQuotient.lean, T-Q5, ALL SORRY-FREE);
`f₀` := the unique descent of `d.f` (invariant by `over_base`). Loeffler's
quasiprojectivity is replaced by affine-over-base — strictly weaker demand on the
machinery, already built.
*Attacks*: (1) `quotient` needs `hVmem : ∀ x, x ∈ V x` — the preimage atlas satisfies
it since affine opens cover `X.base` ✓. (2) the machinery's `[IsAffineHom
(pullback.diagonal (terminal.from X))]`-style side instances (seen in SchemeQuotient's
`omit` lines) — check which instance arguments `quotient` actually takes at build; if
an affine-diagonal instance is required, `Z` finite over a scheme is separated hence
affine-diagonal... over `X.base` arbitrary: `Z` itself need not have affine diagonal in
general?? — `Z → X.base` affine ⟹ `Z`'s diagonal factors as affine over `X.base`'s
diagonal; if the hypothesis is literally about `terminal.from Z` this is a REAL check
at execution; mitigation: the atlas route (`quotient` over an explicit `V`) does not
appear to need it (the `omit` in SchemeQuotient suggests it is only used for
`exists_isStableOpen_isAffineOpen`, which we bypass by supplying the atlas). (3)
uniqueness of `f₀` matters for functoriality in [GHB7] — carried via `∃!`. 
*Provability*: NOW. **LOC 140.**

**[GHB4] `quotientπ_finite_etale_torsor`** ⛩[A711-FP] — freeness ⟹ `π : Z ⟶ Z₀` is
finite étale (and, per KM, an `H`-torsor; the skeleton states finite + étale +
surjective, the exact consumption of GHB6).
*Verbatim (KM 7.1.3(2))*: "If G operates freely on 𝒫 … then 𝒫 is an etale G-torsor
over 𝒫/G; for every E/S/R … 𝒫_{E/S} is an etale G-torsor over (𝒫/G)_{E/S}". *(KM
7.1.3(4))*: "The morphism 𝒫 → 𝒫/G is finite."
*Lean ↔ source*: chart-local: `A := Γ(V)`, `Aᴳ → A` with GHB2's `IsFreeAlgebraAction`:
finite+projective (`Module.Finite/Projective.of_isFreeAlgebraAction` — PROVEN),
torsor iso (`torsorMul_bijective_of_isFreeAlgebraAction` — PROVEN, v10.31), étale
(`Algebra.Etale.of_isFreeAlgebraAction` — **SORRIED**, [A711-FP]; the noetherian
`…_of_isNoetherianRing` is PROVEN and covers every `Y(N)`-pipeline consumer — the
T-E4a-noeth scaffold precedent applies if the general gap outlives this stream);
globalize over the atlas (étale/finite are local on the target; the local quotients
are `Spec Aᴳ` by construction).
*Attacks*: (1) surjectivity of `π`: faithful flatness of `Aᴳ → A` (projective + …) —
from the PROVEN trace/projective layer; record as part of this leaf. (2) local-to-
global: `Z₀`'s charts are literally the glue pieces (`localQuotient`), so locality is
by `openCover` of the glue data — no hidden descent. (3) `Finite G` needed everywhere ✓
(carried by GH0b). *Provability*: gated ⛩[A711-FP]; noetherian fallback PROVEN.
**LOC 200.**

**[GHB5] `quotient_baseChange_comparison`** ⛩[A711-BC] — freeness ⟹ for every
`g : T ⟶ X.base`, the canonical map `(Z ×_{X.base} T)/G ⟶ Z₀ ×_{X.base} T` is an
isomorphism — equivalently the `T`-point description `{h : T ⟶ Z₀ // h ≫ f₀ = g} ≃
[the quotient problem's value]` needed by (Q2).
*Verbatim (KM 7.1.3(3))*: "there is a natural S-morphism (𝒫_{E/S})/G → (𝒫/G)_{E/S},
which is bijective on geometric points. It is an isomorphism if any of the following
conditions hold: a) …flat over (Ell/R); b) the order of G is invertible on S; c) G
operates freely on 𝒫." — we take (c); note (b) would ALSO apply for `H ≤ GL₂(ℤ/N)`
whose order divides a power… NO: `|H|` need not be invertible when `N` is (e.g. `p ∣
|GL₂(ℤ/N)|` with `p ∤ N`), so (c) is the honest hypothesis. 
*Lean ↔ source*: chart-local algebra core: `(Aᴳ) ⊗_B B' ≅ (A ⊗_B B')ᴳ` — this is
`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` (InvariantTorsor.lean,
**SORRIED**, tracked [A711-BC], KM A7.1.2 "∗(A, G, R, R′) for every R′"; KM's own proof
note: "extend scalars of the étale torsor and use (A ⊗ R′)^G = A^G ⊗ R′ for
trivializable torsors"), plus affine-local gluing over `T`'s preimage atlas.
*Attacks*: (1) the chart-base mismatch — A7.1.2 is stated over the ring `R`, our base
change is `B := Γ(U) → B' := Γ(U')` along arbitrary `T → X.base`: instantiate KM's
`(A, G, R, R')` at `(Γ(V), G, Γ(U), Γ(U'))` for affine `U' → U` — shape matches the
sorried statement's `(R, A, R')` ✓. (2) non-affine `T`: glue the affine case (both
sides are Zariski-local on `T`; the comparison map is global by `∃!`-descent) — real
but standard plumbing. (3) without freeness the statement is FALSE (KM's (3) lists it
as a *sufficient* condition; quotients don't commute with base change for non-free
actions — e.g. `μ_p ↪` char-`p` fibres) — hypothesis correctly carried. *Provability*:
gated ⛩[A711-BC]. **THE crux gate of the quotient step.** **LOC 260.**

**[GHB6] `quotient_structMap_finite_etale`** — `f₀ : Z₀ ⟶ X.base` is finite étale
(given `d.f` finite étale, GHB4's `π` finite étale surjective).
*Verbatim (KM 7.1.3(6))*: "If 𝒫 is finite over (Ell/R), and R is noetherian, then 𝒫/G
is finite over (Ell/R)." — KM's noetherian guard is for finiteness WITHOUT freeness;
with freeness both properties descend along the faithfully flat finite `π`
(Stacks-style: `g ∘ f` finite/étale + `f` finite étale surjective ⟹ `g`
finite/étale), no noetherian needed.
*Attacks*: (1) mathlib coverage of "descend along ff": check
`MorphismProperty`-descent (`IsFinite`/`Etale` descend along surjective+flat+…) — if
mathlib has only *morphism* descent for these (the fable-P4 gate-2 audit precedent:
"mathlib has morphism descent only" was about OBJECT descent — property-descent may
exist; verify with loogle at execution) — if absent, this leaf grows an explicit
[GH-DESC-GAP] sub-cut (algebraic: `B → C` with `C → A` ff and `B → A` finite étale ⟹
`B → C` finite étale — ring-level, provable from flatness + finiteness transfer).
(2) alternative route avoiding descent entirely: chart-local `B → Aᴳ`: finite =
`Module.Finite B Aᴳ` from `Aᴳ ⊆ A` direct summand (projective ⟹ summand, PROVEN
layer) of the finite `B`-module `A` — cleaner, noetherian-free; étale similarly via
summand-flatness + unramified-quotient — RECORD as primary route. (3) degree jumps:
none needed — no rank constancy is claimed. *Provability*: NOW (route 2), modest gap
risk. **LOC 180.**

**[GHB7] `exists_quotientProblemData`** ⛩[A711-FP]⛩[A711-BC] — THE ASSEMBLY (generic
KM 7.1.2+7.1.3 for finite étale equivariant data): `FreeAction φ` + (∀ X,
`Nonempty (EquivariantRelRepData φ X)`) ⟹ `Nonempty (QuotientProblemData Q φ)`.
Constructs the functor `prob` (values: chosen `{h : T ⟶ Z₀ // …}` along chosen data;
functoriality from GHB3's `∃!` + GHB5's comparison — the standard
choice-then-uniqueness construction), `proj` (compose the classifying map with `π`),
and all fields: `relRep` (GHB5 + GHB6), `couniversal` (KM 7.1.3(1): descend a
`G`-invariant `ν'` through `π` chart-wise by GHB3's `∃!`), `geom_*` (over `k̄` a
`k̄`-point of `Z₀` lifts to `Z` — `π` finite étale surjective + `k̄` separably closed;
fibres of `π` on `k̄`-points are `G`-orbits — the torsor iso GHB4).
*Verbatim (KM 7.1.3(1))*: "The quotient 𝒫/G exists as a relatively representable
moduli problem, affine over (Ell/R). For any relatively representable 𝒫′, with trivial
G-action, any G-equivariant map 𝒫 → 𝒫′ factors uniquely through the projection
𝒫 → 𝒫/G".
*Attacks*: (1) the choice-dependence of `prob`: two X-choices give canonically
isomorphic values via GHB3-uniqueness — functor laws hold *strictly* because values
are defined as Hom-subtypes of ONE chosen family and `map` is defined by the
comparison, not by re-choosing (the T-Q6c `simulRepresentableBy` pattern; its
"mixed-defeq-spelling" GOTCHA note applies verbatim — budget erw/term-mode). (2) does
`prob` need values at ALL `X` including empty-base? — yes and fine: everything is
Hom-sets, no freeness used in the *definition*. (3) `geom_surjective` genuinely needs
`IsAlgClosed` (finite étale covers of `Spec k` split only for separably closed;
`IsAlgClosed` ⟹ separably closed ✓); a mere field breaks it (twists — Loeffler §3.6
verbatim) ✓ guarded. *Provability*: gated on GHB4/GHB5 (⛩); the construction itself is
NOW-grade diagram plumbing once they land. **LOC 400 (the largest single leaf; split
further at execution if it exceeds budget: value-functor / proj / couniversal /
geometric).**

### PART C — Γ_H: corrected T-H4/T-H6, bridges to the held file, the refutation

**[GHC1] `gammaH_relativelyRepresentable`** (T-H4-corrected) — `hinv` ⟹
`Nonempty (QuotientProblemData (gammaFullNaiveProblem R N) (gammaHAut R N H))`.
Assembly: GHA5 (per-X equivariant fin-étale data) + GH2 (freeness) + GHB7.
*Verbatim*: Loeffler 3.8.2 statement + proof (both above) — with "P_H" now the honest
KM 7.1.2 quotient problem `prob`, whose (Q2)/geometric clauses recover Fact 3.8.1.
*Attacks*: (1) `hinv : IsUnit (N : R)` placement matches the held T-H4 ✓ and feeds
GH2/GHA3 (each needs it, none weaker suffices per their attack lines). (2) `H = ⊥`
degenerate: `Finite ↥⊥` ✓, action trivial, freeness vacuous, GHB7 still applies
(quotient by trivial group: `prob ≅ Q` via couniversal — GHC2 consumes this). (3)
`N = 1`: everything trivial ✓ (`GL₂(ℤ/1)` trivial).
*Provability*: gated through its parts. **LOC 60.**

**[GHC2] `gammaHNaive_relativelyRepresentable_bot`** (bridge, discharges the HELD
statement at `H = ⊥`) — the held `gammaHNaive_relativelyRepresentable`'s FULL
conclusion (both conjuncts, for `H = ⊥`): the naive problem at `⊥` has singleton
orbits (`gammaHNaive_bot`, held, PROVEN), so it is iso to `gammaFullNaiveProblem`, and
GHA4 supplies both conjuncts directly (no quotient needed).
*Attacks*: (1) `gammaHNaive_bot` is `Nonempty (≅)` — enough to transport
`RelativelyRepresentable` (a Prop) across; write the transport lemma
(`relativelyRepresentable_of_iso`) as part of this leaf (generic, 15 lines). (2) the
transport must also carry the naturality clause — isos of functors do ✓. (3) this
leaf is the ONLY place the held T-H4 statement is provable — consistent with F1
(`H ≠ ⊥` refuted). *Provability*: NOW given GHA4. **LOC 80.**

**[GHC3] `gammaHNaive_toQuotient` + `gammaHNaive_toQuotient_geom_bijective`**
(bridge = Loeffler Fact 3.8.1 as a THEOREM) — the comparison
`θ : gammaHNaiveProblem R N H ⟶ pkg.prob` (descend `pkg.proj` through
`Quotient (hOrbitSetoid H)` — well-defined by `proj_invariant` + `gammaHAut_app_val`),
and: at every object over `Spec k̄`, `θ.app` is bijective (from `geom_surjective` +
`geom_orbits`).
*Verbatim (Loeffler Fact 3.8.1)*: "if k̄ is algebraically closed … P_H(E/k̄) =
{H-orbits of isomorphisms (ℤ/N)² ≅ E[N]}." *(Loeffler §3.6, the mechanism)*: "we get a
G-orbit of elements … By a scary lemma (étale descent of morphisms) this gives an
S-point … In general, this is neither injective nor surjective, but if S = Spec(k̄) …
bijective."
*Attacks*: (1) `Quotient.lift` needs the setoid-respect in the RIGHT variance
(`glSmul γ` vs `(gammaHAut γ⁻¹)`) — the inverse twist of GH1 lands exactly here; pin
via `gammaHAut_app_val`. (2) naturality of `θ`: componentwise `Quotient.lift` of a
natural map is natural — needs `Quotient.ind` plumbing only. (3) the bijectivity claim
must NOT extend beyond `k̄`-objects (F1!) — statement quantifies exactly the
`geom_*` object class ✓. *Provability*: NOW given a package. **LOC 120.**

**[GHC4] `gammaHNaiveProblem_not_relativelyRepresentable`** (the F1 refutation record)
— `H ≠ ⊥` + `hinv` + a witness `X : EllObj R` with `Nonempty X.base` and a naive full
level structure `L` ⟹ `¬ (gammaHNaiveProblem R N H).RelativelyRepresentable`.
*Source*: none — this is the adversarial pass's own finding (F1 §0 above), consistent
with the sources' refusal to define P_H naively (quotes in §0).
*Route*: `T := X.base ⨿ X.base` (mathlib scheme coproducts), `g := codiag ≫ 𝟙…`; the
section/level-structure sets over a coproduct split componentwise (coproduct universal
property through the `Section` subtype + `IsNaiveFullLevel`'s fibrewise clauses, each
geometric point factoring through one component); `[(L,L)] ≠ [(L, γL)]` by freeness
(GH2's core argument, reused); equal restrictions along both `pullbackAlongMap`
inclusions; `RelativelyRepresentable`'s naturality + `Hom`-gluing over coproducts
forces equality — contradiction.
*Attacks*: (1) the split of `Section (E.baseChange (codiag))` over the coproduct —
elliptic-curve total spaces pull back to coproducts componentwise (pullback along
`ι₁` of the base-changed curve ≅ component curve) — mechanical but seam-heavy
(pullback-of-pullback isos); budget it. (2) `glSmul` commutes with the component
identification (it is built from `zsmul`/`+` of sections, all categorical) ✓. (3) do
NOT try to refute the second conjunct in Lean (cardinality argument needs a finiteness
count over `k̄` — extra machinery for no extra board value; the doc records it). (4)
hypotheses are satisfiable (non-vacuous refutation): over `R = ℂ`… any `X` with a
level structure — e.g. produced from GHA4's universal point over `levelSpaceΓ` of any
curve with nonempty level scheme; the *statement* takes the witness as hypothesis
precisely so the skeleton does not need to construct one. *Provability*: NOW (real
work, gate-free). **LOC 350.**

**[GHC5] `quotientProblemData_affineOverEll`** — a package gives
`pkg.prob.AffineOverEll` (`IsFinite ⟹ IsAffineHom`, repackage `relRep`'s `∃ d` into
the `∃ Z f, IsAffineHom f ∧ ∃ eqv…` shape of EllCategory's `AffineOverEll`).
*Verbatim (KM 4.7.1 hypothesis)*: "affine and etale over (Ell)". *Attacks*: (1)
mathlib's finite⟹affine instance name/shape (verify at build; TorsorData precedent).
(2) `RelRepData` ↔ `AffineOverEll`'s inline-∃ shape: pure unpacking
(`relativelyRepresentable_iff_nonempty_relRepData` precedent). (3) nothing else.
*Provability*: NOW. **LOC 40.**

**[GHC6] `gammaH_representable_of_rigid`** (T-H6-corrected) ⛩[T-E5-engine] — for a
package `pkg` (from GHC1) with `hrig : pkg.prob.Rigid`: `pkg.prob.Representable`.
Proof: GHC5 + `representable_iff pkg.prob (GHC5)` (EllCategory.lean, statement of
record after the B2 amendment; its ⇐ is the T-Q6e-gated engine).
*Verbatim (KM 4.7.2)*: "For N ≥ 3, the naive level N moduli problems of 4.6 is
representable, by a smooth affine curve Y(N) over ℤ[1/N]. Proof. This results from
4.7.1 above, thanks to the rigidity 2.7.2 and the relative representability 3.7.1 of
naive level N structures." — ours is the arbitrary-`H` form (KM 4.7.1 + 7.1) with
rigidity as hypothesis.
*Attacks*: (1) the held T-H6's `hrig` is rigidity of the NAIVE problem; ours is of
`pkg.prob` — the transfer (naive rigid ⟺ quotient-problem rigid) is genuinely
nontrivial (needs `θ`'s étale-local orbit-surjectivity to pull a fixed value back) —
cut as the FUTURE ticket **[GH-RIGID-XFER]**, consuming GHC3 + fppf descent of
morphism-equality; T-H5 (Loeffler 3.8.3) should target whichever side [GH-RIGID-XFER]
prefers — board decision. (2) smooth∧affine-base conjunct of the held T-H6:
deliberately NOT reproduced (needs KM 4.7.1's smoothness proof — inspection of
Legendre/naive-level-3 equations + étale invariance — a separate future cut
**[GH-SMOOTH]**). (3) `Nontrivial R` not needed (implication, not iff — same
adjudication as the held T-H6's attack line). *Provability*: gated ⛩[T-E5-engine].
**LOC 30.**

### Order of execution (respects gates; NOW-lane first)
1. GH0a/b/c, GHA1 (defs) → 2. GHA2, GHB1, GHB3, GHC5 (NOW, independent) →
3. GH2, GHB2 (NOW, freeness pair) → 4. GHA4 → GHA5 (NOW, seam-heavy) →
5. GHC4, GHC2 (NOW bridges; C4 is the B2 evidence) → 6. GHB6 (NOW modulo gap-check) →
7. ⛩ GHB4 ([A711-FP] or noetherian scaffold), ⛩ GHB5 ([A711-BC]) →
8. GHB7 → GHC1 → GHC3 → 9. ⛩ GHA3 ([DS4/T-C1], parallel to 7–8) →
10. ⛩ GHC6 ([T-E5-engine]) — plus GH1 (⛩[T-E4a]) whenever its gate flips (it blocks
3's `gammaHAut`-shaped statements only *as proofs*; statements stand).

### Gate table (what the H-quotient step consumes, precisely)
| Gate | Decl (file) | State | Consumed by |
|---|---|---|---|
| [A711-BC] | `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` (ForMathlib/InvariantTorsor.lean:496) | SORRIED | GHB5 (base-change of quotients — (Q2)'s crux) |
| [A711-FP] | `Algebra.Etale.of_isFreeAlgebraAction` (InvariantTorsor.lean:376); noetherian version :593 PROVEN | SORRIED (general) | GHB4 (π étale) |
| — | `torsorMul_bijective_of_isFreeAlgebraAction` (InvariantTorsor.lean:400) | **PROVEN** (v10.31) | GHB4/GHB7 (orbit fibres) |
| — | `SchemeAction.quotient/quotientπ/hom_quotientπ/quotientπ_hom_ext/existsUnique_quotientπ_lift` (ForMathlib/SchemeQuotient.lean) | **PROVEN** (T-Q5) | GHB3 |
| — | `RelRepData`/`TorsorData` vocabulary + `simulRepresentableBy` pattern (Moduli/QuotientProblem.lean) | **PROVEN** (T-Q6a–c) | GH0b/c, GHB1, GHB7 |
| [DS4/T-C1] | `weilPairing` + specs (WeilPairing/Basic.lean) | DATA-SORRY (CHARTER-P2) | GHA3 route (a) |
| [T-E4a] | `EllHom.pullSection_add` (Moduli/Representability.lean:204; loc-noeth version PROVEN in Moduli/PullSectionAdd.lean) | SORRIED (parked T-W7.8) | GH1 (the action's naturality) |
| [T-E5-engine] | `representable_iff` ⇐ (Moduli/EllCategory.lean:274; = T-Q6e engine) | SORRIED (gated T-Q6e/T-E14/T-E15) | GHC6 |
| boxes | `torsionπ_isFinite/flat` (T-B4), `fullLevel_divisor_iff_naive_gen` (T-D8-bridge), T-D3/T-D1 | REGISTERED BOXES | GHA2/GHA4 (axiom-provenance only) |

**LOC totals**: PART 0 ≈ 245 · PART A ≈ 613 · PART B ≈ 1320 · PART C ≈ 680 ·
**≈ 2860 Lean LOC** against ≈ 9 source pages (Loeffler 3 sentences + Fact 3.8.1; KM
7.1.1–7.1.3 pp. 186–189 + construction-proof; KM 3.7.1 p. 104–105; A7.1.1–2 excerpts)
— consistent with the project's observed ~300 LOC/source-page on quotient/descent
material (T-Q3/T-Q5/T-Q6 track record).

---

## 3. Board-facing notes

- **B2 EVENT (F1)**: held T-H4 (`gammaHNaive_relativelyRepresentable`, GammaH.lean:432)
  and held T-H6 (`gammaHNaive_representable_of_rigid`, :460) are false for `H ≠ ⊥` as
  stated (naive-orbit presheaf is not a Zariski sheaf). Fix belongs to the H-lane
  holder + owner: repoint both at the KM 7.1.2 quotient problem (this stream's
  `QuotientProblemData`), keep the naive problem for the action/geometric bridges.
  Refutation evidence = [GHC4] (stated, provable-now); corrected statements = [GHC1],
  [GHC6]. The 2026-07-06 levels-stack attack file's T-H4 "[FALSITY] TRUE" verdict is
  superseded.
- **New future cuts surfaced**: [GH-RIGID-XFER] (rigidity transfer naive ↔ quotient,
  feeds T-H5's consumer story), [GH-SMOOTH] (KM 4.7.1's smooth-affine-curve conjunct),
  [GH-DESC-GAP] (only if mathlib lacks finite-étale property-descent along ff finite
  étale — check at GHB6 execution).
- **Loeffler cites no KM number at 3.8.2**; the KM analogues used as sources of record:
  KM 3.7.1 (H = 1), KM 7.1.1–7.1.3 (quotient), KM 4.7.1/4.7.2 (T-H6 shape) — all read
  from the full text this session, quotes above.
