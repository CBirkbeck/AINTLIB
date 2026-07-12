# Worker decomposition — KM Chapter 1 (complete; proofs read 2026-07-05)

*Source: Katz–Mazur Ch. 1 §§1.1–1.9, ALL PROOFS READ (preview, book pp. 3–39). Every
entry below transcribes the source's actual proof and turns it into Lean steps. Workers:
follow the steps; if a step fails, B2-report — do not invent an alternative route.
Cross-file: statements live in `LevelStructure/{CartierDivisor,ExactOrder,Basic,Incidence}.lean`.*

**Standing hard bits (read first — these recur in almost every proof):**

- **HB-NOETH (noetherian reduction).** KM reduce finite-presentation statements to
  noetherian bases via EGA IV 8.9.1 + 11.2.6.1 on nearly every page (1.2.2, 1.2.3,
  1.7.2, 1.8.1). Mathlib candidates: `AlgebraicGeometry/SpreadingOut.lean`,
  `AffineTransitionLimit.lean` (verify coverage — ticket T-NOETH0 scoping). WORKERS:
  when a KM proof says "reduce to R noetherian", first try to prove the statement
  directly without the reduction (often possible for our uses since our divisors come
  with finite-locally-free data by construction); only if that fails, invoke T-NOETH.
  Never silently strengthen a statement to noetherian hypotheses — that is target
  drift (B2).
- **HB-FLF (finite flat f.p. = finite locally free).** KM 1.8.1: "the standard
  reduction to the noetherian case shows that, equivalently, Z/S is finite locally
  free". Mathlib: finite + flat + f.p. over a ring ⟹ `Module.Free` locally:
  `Module.free_of_flat_of_isLocalRing` (Stacks 00NZ) + finite presentation descent —
  mostly PRESENT. Ticket T-D12a packages: `IsFinite f → Flat f → LocallyOfFinitePresentation f
  → (affine-locally the pushforward algebra is finite free)`.
- **HB-FIBCRIT (fibre-by-fibre flatness).** KM's Prop 1.1.5.1 IS the criterion, cited
  as [A-K 1, V 3.6] (Altman–Kleiman LNM 146), stated for S loc. noetherian, X lft, F
  coherent S-flat: F is O_X-flat ⟺ F⊗k(s) flat on each geometric fibre. This IS the
  FLAT stream (T-FLAT1); survey: absent from mathlib and unclaimed — we build it.

---

## Block D-official: relative effective Cartier divisors (KM 1.1)

### D-off.1 = T-D11 official definition + affine-local form (KM 1.1.1)
Definition (verbatim essentials): closed `D ⊆ X`, `D` flat over `S`, ideal `I(D)`
invertible; affine-locally `D = V(f)`, `f` a nonzerodivisor, `A/fA` flat over `R`.
- Lean: predicate `IsOfficialCartier` on `IdealSheafData` (already sketched in
  CartierDivisor.lean per plan): affine-local ∃-form. Equivalence with invertibility of
  the ideal MODULE (needs AG-LB) recorded as the (L,ℓ)-half, T-D19.
- Steps: (1) define affine-local predicate; (2) prove Zariski-locality of the predicate
  (mathlib `IsLocalAtTarget`-style plumbing on affine opens); (3) equivalence with the
  working (finite-locally-free) definition in smooth curves = D-curve.2 below.

### D-off.2 = T-D3-core: sums (KM 1.1.2, proof p. 4 — transcribed)
`D + D′` defined locally by `fg`. TWO verifications, both one-liners in the source:
1. `fg` is a nzd: compose the injections `A →×f A →×g A` ("one notes the commutative
   diagram"). Lean: `mul_mem_nonZeroDivisors` ✓ mathlib.
2. `A/fgA` is `R`-flat: the SES `0 → A/gA →×f A/fgA → A/fA → 0` "exhibits A/fgA as an
   extension of flat R-modules". Lean steps: (a) exactness of the sequence — the
   injectivity of `×f : A/gA → A/fgA` needs `f·x ∈ fgA → x ∈ gA`, i.e. `f` nzd; (b)
   `Module.Flat` closed under extensions: mathlib `Module.Flat.extension?` — VERIFY
   name (`Module.Flat` of middle from outer two in SES: search
   `Flat.of_shortExact`/`flat_of_flat_of_flat`; if absent it is Tor-characterisation
   one-liner once Tor available, or direct via `Module.Flat.iff_rTensor_injective` +
   snake — sub-ticket T-D3a′ if missing).
- HARD BIT: globalising the local products to an `IdealSheafData` product. Sub-plan
  (T-D3b): define `IdealSheafData.mul` via `(I * J).ideal U := I.ideal U * J.ideal U`
  on affine opens + compatibility (mathlib `IdealSheafData` is specified on
  `affineOpens` with a gluing condition — multiply ideal-wise, prove the condition via
  localization-commutes-with-products `Ideal.map_mul` ✓). Upstream candidate.
- Then `sectionsDivisor P := ∑ᵢ [Pᵢ]` = fold of `mul` over `sectionDivisor` (D-curve.1).

### D-off.3 = T-D12: base change + flat pullback (KM 1.1.4, proofs p. 5–6)
1. Arbitrary base change `T → S`: apply `⊗_R R′` to `0 → O_X →ℓ→ L → L/O_X → 0`;
   stays exact because `L/O_X` is `R`-flat ("this sequence stays short exact after
   ⊗R′"); last term is `R′`-flat. Lean (working form, as set up in Incidence.lean):
   the base-changed closed immersion `pullback.snd D.ι fst` with ideal `.ker`; prove
   `finite/flat/lfp` fields via mathlib base-change instances (`IsFinite`, `Flat`,
   `LocallyOfFinitePresentation` are all stable — instances present ✓), plus
   `(pullback of subscheme) ≅ subscheme of ker` (mathlib `IsClosedImmersion` ↔
   `Hom.ker` dictionary: `Scheme.Hom.ker`-API, check `subschemeι`-factorisation lemma).
2. Flat pullback `f : Y → X` flat over `S`: ideal is `f*(I(D))` since SES stays exact
   by flatness of `f`. (Needed for D-curve.4 pullback-degree.)

### D-off.4 = T-FLAT1-consumer: fibrewise recognition (KM 1.1.5.1–1.1.5.2, pp. 6–7)
Cor 1.1.5.2 (proof transcribed): D closed, S-flat, X flat lft/S loc-noeth: ECD ⟺
geometric-fibrewise ECD. Proof: necessity = base change; sufficiency: `I(D)` is S-flat
from the SES (`O_X`, `O_D` both S-flat); `I(D)⊗k ≅ I(D⊗k)` (compare first terms after
⊗k — exactness by S-flatness of O_D); invertible on fibres ⟹ `O_{X⊗k}`-flat ⟹ [FIBCRIT]
`I(D)` is `O_X`-flat; + coherent ⟹ locally free; rank 1 by restriction to fibres.
- DEPENDS: T-FLAT1 (HB-FIBCRIT). This is the ONLY Ch. 1 result that needs it — every
  other Ch. 1 proof uses only 1.1.5.2 through Lemmas 1.2.2/1.2.3. Board note: T-D11's
  equivalence ticket carries this dependency; the *working-definition* development
  (everything in streams D/H) does NOT block on FLAT.

## Block D-curve: divisors in smooth curves (KM 1.2, proofs pp. 7–12)

### D-curve.1 = sections give divisors (KM 1.2.2)
Proof: reduce to `R` noetherian (HB-NOETH), then 1.1.5.2 to `k̄`, "in this case the
assertion is obvious". Lean plan AVOIDING the reduction (allowed — stronger route,
same statement): a section of a *separated smooth* curve is a closed immersion
(mathlib: section of separated morphism is closed immersion ✓ pattern exists —
`isClosedImmersion_of_comp_eq_id` seen in mathlib Group/Abelian); its ideal is
invertible because the section lands in the smooth locus and the diagonal of a smooth
rel-dim-1 morphism is regularly immersed of codim 1 — HARD BIT HB-REGIMM: "section of
smooth rel-dim-1 ⟹ ideal locally principal nzd". Sub-decomposition (T-D22, new):
  (a) local model: smooth of rel dim 1 ⟹ étale-locally `𝔸¹_R` (mathlib
      `IsStandardSmoothOfRelativeDimension` gives presentations ✓);
  (b) for `𝔸¹_R = Spec R[t]` and the zero section: ideal = `(t)` — principal, `t` nzd,
      `R[t]/(t) = R` flat ✓ (explicit computation);
  (c) descend local-principality along the étale cover (ideal invertibility is
      fppf-local — for the WORKING definition, instead descend "finite locally free of
      rank 1", which is fpqc-local via mathlib module descent ✓).
  GME's §2.1.4-end (p. 107, read): "I(P) is generated by T and therefore free" — same
  route, quotable.
- Deliverable: `sectionDivisor (z : section) : RelEffCartierDiv π` REAL (upgrade of the
  DS4a piece for single sections), `degree = 1` (D-curve.3).

### D-curve.2 = T-D11-equivalence: finite flat ⟺ proper ECD (KM 1.2.3 + Rmk 1.2.4)
Proof (transcribed): (⇐, i.e. finite flat f.p. closed ⟹ ECD): HB-NOETH + 1.1.5.2 to
k̄, "obvious" there [over k̄: a finite closed subscheme of a smooth curve is cut by one
equation locally — DVR local rings! Lean: local ring at a closed point of a smooth
curve over a field is a DVR — mathlib: smooth ⟹ regular local of dim 1 ⟹ DVR: check
`IsDiscreteValuationRing` from regularity — likely needs assembling: T-D23 sub-ticket];
properness from finiteness. (⇒): D proper: reduce to R noeth; D proper + affine-fibred
(finite fibres: ECD in a curve over a field is finite) ⟹ finite — mathlib ZMT
`IsFinite.of_isProper_of_locallyQuasiFinite` ✓ PRESENT. Quasi-finiteness of D/S: fibres
of an ECD over a field are finite (degree bound) — via D-curve.3's local freeness.
- Remark 1.2.4: over a PROPER smooth curve, every ECD is automatically proper —
  one-liner (closed in proper).

### D-curve.3 = degree theory (KM 1.2.5–1.2.6, proofs pp. 9–10)
Definitions + additivity. KM's degree = rank of the locally free R-module `O_D`;
`H⁰(C, L/O) = H⁰(C, I⁻¹(D)/O)` is locally free of rank deg D (used by incidence!).
Additivity proof (1.2.6, transcribed): snake lemma on the `×ℓ₂ / ×ℓ₁⊗ℓ₂` diagram gives
`0 → L₂⊗O_{D₂} → (L₁⊗L₂)⊗O_{D₁+D₂} → (L₁⊗L₂)⊗O_{D₁} → 0`; "taking Euler
characteristics" = ranks add in a SES of finite locally free modules (mathlib
`Module.rank_eq` additivity over local rings; finrank additive in SES of f.g. flat ✓
`FiniteDimensional`-style lemma over local base then glue).
- Lean plan (working-definition route, avoids (L,ℓ)): `degree` is already `finrank` of
  the structure map (skeleton ✓). Additivity: affine-locally `O_{D₁+D₂} = A/fgA` sits
  in the SES of D-off.2(2) with outer terms `A/gA`, `A/fA` — finrank additivity in SES
  of finite free R-modules (mathlib `Module.finrank` additive on split/flat SES over
  local rings — localize at primes: T-D24 small lemma). NOTE this is the (L,ℓ)-free
  proof; the source's Euler-characteristic argument is the (L,ℓ)-half (T-D19).
- 1.2.7 (degree-1 proper divisors = sections; proof: the diagonal arrow D → S is an
  iso because the affine ring is an invertible R-module, "i.e., into R itself"):
  Lean: rank-1 locally free algebra with... the KEY content: an R-algebra which is
  invertible (rank-1 locally free) as an R-module is R (structure map is iso) —
  mathlib: `Algebra` + `Module.Free` rank 1 ⟹ `algebraMap` bijective: sub-ticket
  T-D25 (algebra lemma: unital rank-1 ⟹ iso; proof: 1 generates locally).
- 1.2.8 (deg f* D = deg f · deg D) and 1.2.9 (base change preserves degree; proof =
  the cartesian "finite locally free of deg(D)" square): rank multiplicativity /
  stability — mathlib `Scheme.Hom.finrank` base-change lemma (check; else via module
  rank ⊗).

## Block D-inc: incidence (KM 1.3, proofs pp. 12–16) — statements in Incidence.lean

### D-inc.1 = difference divisors (KM 1.3.1/1.3.3)
`D′ ≤ D ⟺ I(D) ⊆ I(D′) ⟺ ∃ D″, D = D′ + D″`; local form `g | f`, `h = f/g` unique nzd;
`D″` flat via `0 → A/hA →×g A/fA → A/gA → 0`. Lean: our `IsSubdivisor` is the
subscheme-factorisation form = ideal containment (mathlib `IdealSheafData` order —
verify `≤` exists; else state via containment on affine opens); the local `h` and the
SES re-use D-off.2 machinery mirrored. Deg subtraction (1.3.3) from additivity.

### D-inc.2 = T-D14/T-D15: the incidence loci (KM 1.3.4/1.3.5 — THE KEY LEMMA)
Proof (1.3.4, fully transcribed): local on S = Spec R. `D′ ≤ D ⟺ ℓ` (section of L
representing D) `vanishes identically in L|D′ = L⊗O_{D′}`. `H⁰(D′, L|D′)` is locally
free of rank d′ = deg D′ (from D-curve.3). Choose local basis `e₁,…,e_{d′}`;
`ℓ = Σ rᵢeᵢ`, `rᵢ ∈ R`; `Z := V(r₁,…,r_{d′})`. Universality: for `t : T → S`,
`D′_T ≤ D_T ⟺ t^#(rᵢ) = 0 ∀i` — by base-change compatibility of the whole display
(1.2.9 + module base change). Locally d′ equations; formation commutes with base
change.
- Lean plan (working-definition translation — the (L,ℓ) can be ELIMINATED):
  `ℓ vanishes in L|D′` ⟺ the composite `I(D) ↪ O_C ↠ O_{D′}` is ZERO ⟺
  `I(D) ⊆ I(D′)` after restriction — concretely, affine-locally with `D = V(f)`:
  `f ↦ f mod I(D′) ∈ B′ := A/I(D′)`, and `B′` is finite locally free of rank d′ over
  R; condition = "image of f in B′ is 0 after base change". So: **the incidence locus
  = zero locus of the element `f̄ ∈ B′` of a rank-d′ locally free module** — EXACTLY
  `sectionVanishingIdeal R B′ f̄` from Incidence.lean, glued over an affine cover of S
  (+ the f-choice independence: two local equations differ by a unit — unit×f has the
  same vanishing locus: small lemma `sectionVanishingIdeal_unit_smul`).
  Steps: (a) T-D13 `sectionVanishingIdeal_spec` (free case: coordinates w.r.t. a
  basis; `f ⊗ 1 = Σ (f-coords) eᵢ`; kill ⟺ coords die — direct); (b) localize-and-glue
  to `IdealSheafData` on S (pattern of D-off.2's glueing); (c) universality from (a) +
  base-change of B′ (D-off.3); (d) equation count = rank ✓ by construction.
- 1.3.5 (EQ): same-degree ⟹ `≤` iff `=` (via 1.3.3: D″ has degree 0 and degree-0
  effective proper divisor is empty — small lemma T-D26: deg 0 ⟹ ideal = ⊤, from
  rank-0 locally free algebra = 0). Locus = the LE locus.

### D-inc.3 = T-D16: subgroup locus (KM 1.3.6/1.3.7, proof pp. 15–16, transcribed)
Conditions: (1) `[e] ≤ D` — ONE incidence-locus of a degree-1 divisor (1 equation);
(2) `D = inv*(D)` — inv is an S-automorphism of E, `inv*(D)` is a divisor of the same
degree (pullback along iso — D-off.3 flat pullback with f = inv), EQ-locus (deg D
equations); (3) over `W = D ×_S D` (finite locally free of rank (deg D)² — product of
f.l.f.), the universal pair `(P₁,P₂)` (tautological sections of `C_W`), condition
`[m(P₁,P₂)] ≤ D_W` — an incidence-locus ON W, which by [KM: "the vanishing on W of a
single function is equivalent to the vanishing on S of its (deg D)² coordinates"]
descends to (deg D)² equations on S. Z = intersection of the three loci.
- Lean plan: (a) define `inv*D`, `m(P₁,P₂)` as divisor/section data: the universal
  points `P₁ P₂ : W → C_W` are `pullback` legs composed with `D.ι` — REAL constructions;
  `m(P₁,P₂)` = their sum under the group law (Point-group of `E.baseChange (W→S)`);
  (b) three applications of D-inc.2 (+ for (3): `sectionVanishingIdeal` over the
  f.l.f. pushforward from W to S — the "coordinates" descent, which is
  `sectionVanishingIdeal` composed with the trace-free module identification
  `H⁰(W,M) = H⁰(S, push M)`: T-D27 small lemma: zero-locus over W of a module =
  zero-locus over S of its pushforward when W/S is f.l.f.);
  (c) equivalence with our `IsSubgroup` (functor-of-points form): KM's own reduction
  "(1) = contains identity; (2) = stable by inversion; (3) = stable by multiplication"
  — prove `IsSubgroup D ⟺` the three divisor conditions hold after every base change
  ⟺ (by universality) factoring through Z. The (⟸) direction needs: divisor conditions
  ⟹ D(T) subgroup — pointwise: `P ∈ D(T), Q ∈ D(T) ⟹ (P,Q) ∈ W(T) ⟹ m(P,Q) ∈ D(T)`
  via (3)'s universality — this is where the tautological-pair formulation pays.

### D-inc.4 = T-D17/T-D18: exact-order and full-level loci (KM 1.6 instances)
From KM 1.6 (proofs pp. 22–25, transcribed in decomposition-gme2 §L for the Hom-scheme
side): `Hom_{S-gp}(ℤ/N, E) = E[N]` and `Hom((ℤ/N)², E) = E[N] ×_S E[N]` (1.6.1 —
kernel-pullback squares, already REAL in our skeleton via `pointToTorsion`); A-Str
locus = subgroup-locus of the universal divisor `Σ [φ_univ(a)]` over the Hom-scheme
(Prop 1.6.2, "the asserted result now follows from (1.3.7)"); A-Gen locus (1.6.5) =
EQ-locus `D_univ = G` (1.3.5, #A equations). Étale cases: 1.6.4 formal-étaleness
proof transcribed — nilpotent thickening T₀ ⊆ T; φ₀ factors through C[N](T₀); C[N]
étale ⟹ unique lift; A-structure condition tested on geometric points ("T and T₀ have
precisely the same geometric points").
- Lean plan: universal divisor over `E.torsion N` (resp. the product): sections
  `a ↦ a-th multiple of the universal point` — universal point = `pullback.fst?` NO:
  the universal T-point of E[N] over T := E[N] itself is `𝟙 (E.torsion N)`
  transported: `⟨torsionι, rfl-ish⟩ : E-point over torsionπ` — REAL; its multiples via
  Point-group; `orderDivisor` of it; apply T-D16 over base `E.torsion N`. Then the
  characterisation ⟺ our `HasExactOrder` after base change: by T-D16's universality +
  "pointToTorsion P hP is exactly the classifying map of P" (pullback.lift uniqueness).
- 1.7 factorization (proofs pp. 26–31, transcribed): CRT projectors split G;
  [De-Ga IV §3 5.3-9] rank-divisibility input → **stream OT companion statement**
  (T-OT2: rank of a p-group scheme is a p-power — statement now, GME 1.6-1.7/DG
  source); translation-disjointness argument for `G = ∐ Trans(φ(a₁))*(D₂)`;
  connected-T argument. Ticket T-D28 (phase 2): A-Str ≅ ∏ Aᵢ-Str.

## Block D-full: full sets of sections (KM 1.8–1.9, proofs pp. 32–39)

- **1.8.1** char-poly `det(T−f)` of mult-by-f on rank-N locally free B — mathlib:
  `LinearMap.charpoly` (free case ✓), `Algebra.norm/trace`. HB: locally-free (not
  free) globalisation — define via localisation glue or restrict statements to free
  covers (KM do everything "locally on S").
- **1.8.2** the two definitions + equivalence (transcribed): (1)⟹(2) at T=0;
  (2)⟹(1): apply (2) over R[T] to T−f: "the characteristic polynomial of f ∈ B is
  just the norm of T−f relative to B⊗R[T]/R[T]" — **T-D29 charpoly-as-norm lemma**
  (mathlib check: `Algebra.charpoly`? likely absent as such — provable:
  `LinearMap.charpoly f = Algebra.norm (R[T]) (T•1 − f⊗1)` via det of the same matrix
  over R[T]; clean self-contained lemma, good early ticket).
  Our skeleton's `IsFullSetOfSectionsAlg` = form (2) quantified over algebras ✓
  faithful. Add the (1)-form + equivalence as statements (T-D30).
- **1.8.3** étale case ⟺ ∐S ≅ Z ⟺ fibrewise distinct (proof: distinct-values function
  f, factor char poly): feeds T-D6's (3)⟺(4).
- **1.8.4/1.8.5/1.8.6** ∐ and ×ₛ lemmas (proofs transcribed: Norm multiplicative on
  B₁⊕B₂; f₁⊗1 char-poly = (char-poly)^{N₂} + monic-root extraction over k̄; norm
  transitivity in towers): feeds Γ(N) ⟺ pairs-generate arguments (T-D8). Mathlib:
  `Algebra.norm_norm` (transitivity ✓ exists for towers with conditions — verify).
- **1.9.1/1.9.2** universal norm-equation subscheme + reduced-base criterion (proofs
  in hand; already the source for T-D2): the (2N−1 choose N)-coefficients comparison of
  two degree-N homogeneous forms in `R[T₁..T_N]` — Lean: coefficient-wise equality of
  `MvPolynomial` — direct; reduced case: values at geometric points detect equality in
  reduced rings (`MvPolynomial` over reduced R is reduced; evaluation-separating —
  mathlib `MvPolynomial.eval_injective`-adjacent, sub-ticket T-D31).

## KM 1.4.4 (T-D6/T-D7) — proof steps (pp. 18–19, transcribed)
(1)⟹(2) base change ✓ trivial from definitions. (2)⟹(3): G := rank-N subgroup
generated over k̄; N invertible in k ⟹ G finite étale ⟹ N distinct points; divisor
equality forces {aP_k} to exhaust them. (3)⟺(4): D = Σ[aP] f.l.f. of rank N; étale ⟺
disc(tr(eᵢeⱼ)) invertible ⟺ geometric fibres étale ⟺ (3) [mathlib: étale ⟺ finite +
unramified + flat; unramified ⟺ fibres étale-algebras: `Etale` fibre criterion —
verify; disc route optional]. (3)⟺(5): the map `ℤ/N → D` between f.l.f. rank-N:
matrix over R locally; iso ⟺ det unit ⟺ iso on geometric fibres ⟺ points distinct
[Lean: `IsIso ⟺ ∀ geometric fibre iso` for a map of f.l.f. modules — det-unit-locus
lemma T-D32: `LinearMap.det` unit ⟺ unit in every residue field ✓ `IsUnit.map` +
local-global]. (5)⟹(1): "Σ[aP] is endowed with the structure of subgroup" — transport
the constant group structure along the iso; our `IsSubgroup` from the constant
scheme's evident one (T-B2's `constZModGrpObj` + transport lemma).
