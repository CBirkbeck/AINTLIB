# HRW sub-campaign decomposition — head-localization reducedness (BGR 7.3.2/10)

Opened 2026-07-28 on user authorization ("open the BGR work").  Adjudication and
route analysis: `chatgpt-review-2026-07-28.md` § "The wall" (4-lemma structure,
counterexamples to the shortcut routes, char-2 truth confirmation).  Goal: discharge

  `HeadLocsReduced K w : ∀ N (DH : RationalLocData (WPHead K w N)), DH.IsRational →
    IsReduced (presheafValue DH)`

— the quarantined hypothesis of endpoints (3).  Classical source: BGR 7.3.2/10 via
the completed-local comparison + analytic unramifiedness; we follow the reviewer's
head-specific plan, with the graph model `QHead` as the concrete localization.

## Skeleton
`projects/AdicSpaces/Adic spaces/WP/HeadReduced.lean` (statements sorried, builds).

## The four lemmas (reviewer-adjudicated structure)

### HRW-L2 `isReduced_of_forall_completedLocal_reduced` (mathlib-grade; EASIEST — start here)
Noetherian `R` with all completed local rings at maximal ideals reduced is reduced.
Prose: let `x` be nilpotent.  For each maximal `𝔪`, its image in `R_𝔪` is nilpotent;
the map `R_𝔪 → (R_𝔪)^` (adic completion at the maximal ideal) has kernel
`⋂ (max)ⁿ = 0` by Krull intersection (`Ideal.iInf_pow_eq_bot_of_isLocalRing`,
VERIFIED in mathlib, Filtration.lean:34/426 area; `R_𝔪` noetherian local), so the
image of `x` in the reduced completion is 0 forces `x/1 = 0` in `R_𝔪`; vanishing at
all maximal localizations forces `x = 0` (`Ideal.mem_of_localization_maximal` at
`J = ⊥`, VERIFIED LocalProperties/Basic.lean:539).
Leaves: (i) kernel-of-completion = ⋂ powers (state as: `x ∈ ⋂ 𝔪ⁿ` from vanishing
image — via `AdicCompletion.of` and its coefficientwise characterization; if the
kernel lemma is absent, prove membership in every `𝔪ⁿ` directly from the completion
vanishing at level `n`); (ii) the two cited mathlib lemmas.  All-mathlib; no WP
dependence.  Sizing: reviewer gives the proof in 3 sentences; expect ~80 LOC.

### HRW-L1 `qHead_completedLocal_comparison` (deps: W15, W16 — the QHead layer)
For a head datum `DH` and a maximal `𝔮 ⊂ QHead DH` with `𝔭 := 𝔮.comap (headToQ DH)`:
`((WPHead)_𝔭)^ ≅ ((QHead DH)_𝔮)^` (completed local rings at the maximal ideals of
the localizations).  Reviewer's sketch: "Prove this first for the graph
presentation, using that the denominator becomes a unit and that modulo every power
of the maximal ideal the restricted-series variables evaluate uniquely.  Then pass
to inverse limits."  Decomposition:
- L1.a `headToQ` (the canonical hom head → QHead = quotient ∘ polyToP ∘ C) + `𝔭`
  maximal (Tate-scope: the fibre argument — s ∉ 𝔮 since s is a unit; standard).
- L1.b mod-𝔮ⁿ evaluation: `(QHead DH)/𝔮ⁿ ≅ (WPHead)_𝔭-side/𝔭ⁿ`-comparison: in the
  quotient by `𝔮ⁿ` the variables `T_i` are determined (`T_i = f_i/s`, `s` invertible
  mod every power since `s ∉ 𝔮`), and restricted series collapse to polynomials mod
  each power (coefficients below any ϖ-power vanish in the artinian quotient —
  uses that `ϖ ∈ 𝔮`?? NO — ϖ is a UNIT; the collapse is: mod 𝔮ⁿ the ideal 𝔮 is
  nilpotent and the graph relations make T_i integral-rational — the honest leaf is
  the surjectivity + kernel computation of `(head-polynomials in T)/(graph,𝔭ⁿ-side)
  → QHead/𝔮ⁿ`; state carefully at skeleton refinement).
- L1.c inverse limits: `AdicCompletion` functoriality along the compatible tower.
Frontier flag: L1.b is genuinely new mathematics (no mathlib precedent for
Tate-graph completed-local comparisons); it is however finite-level COMMUTATIVE
ALGEBRA (artinian quotients), not analysis.

### HRW-L3 `head_completedLocal_reduced` (THE frontier)
Every completed local ring of the head at a maximal ideal is reduced.  Case split
on `WaHead ∈ 𝔭`:
- **L3.a, `W ∉ 𝔭`** (Z-elimination): in `(WPHead)_𝔭`, `W` is a unit and
  `Z_i = W^{−2w i}·Y_i²`, so the local ring is a localization of (the head with the
  Z's eliminated) = the FULL Tate algebra `K⟨W, U_{≤N}⟩` localized at the pulled-back
  maximal (`A_N[1/W] = K⟨W,U_{≤N}⟩[1/W]`, an equality of subrings of the ambient —
  provable by the support model: `U_n = W^{−w n}·Y_n`).  The leaf becomes: completed
  locals of the FULL Tate algebra `K⟨X_0,…,X_N⟩` at maximals are reduced — classical
  regularity of Tate algebras.  Sub-frontier with a standard route: residue fields
  of maximals are finite over `K` (affinoid Nullstellensatz — CHECK the 828b layer's
  7.51/7.52 artifacts first: `exists_hSpa_points_*` machinery may contain the needed
  finiteness) and the completed local is then a formal power-series ring over a
  finite extension (Cohen-style, but constructible by hand here: regular system of
  parameters `X_i − a_i` after base change... state the leaf as
  `tateAlgebra_completedLocal_reduced` and sub-decompose when reached).
- **L3.b, `W ∈ 𝔭`** (the quadratic tower at the singular point): then every
  `Y_i ∈ 𝔭` (from `Y_i² = W^{2w i}Z_i ∈ 𝔭`, primality).  The completed local ring
  is the `(W,Y,…)`-adic completion of the local quadratic tower; reviewer: "one must
  analyze the formal relations themselves" (char-2-safe).  Plan of attack when
  reached: the explicit monomial model gives the completed local ring an explicit
  description as a sub-power-series ring (the support condition localized); reuse
  the Φ-style embedding into a formal domain to kill nilpotents — the analogue of
  `isReduced_tailC0` one level down.  This is the deepest leaf of the whole
  campaign; expect its own decomposition round when its ticket opens.

### HRW-L4 `headLocsReduced` (assembly; deps L1+L2+L3 + W16 headLocEquiv)
`P := presheafValue DH ≅ QHead DH` (W16); `QHead` noetherian (W15 layer + 828b
machinery); by L2 it suffices that all completed locals of `QHead` are reduced; by
L1 those agree with completed locals of the head; by L3 the latter are reduced.
Then endpoints: `weightedParity_chainReduced_unconditional` etc. in Main.lean (NEW
theorems; the conditional forms stay).

## Adversarial notes
- L2 attack (composition): does reducedness really localize upward? — yes:
  `x/1 = 0` in ALL `R_𝔪` ⇒ `x = 0` is exactly mem_of_localization_maximal at ⊥;
  and nilpotents localize to nilpotents (ring-hom images).  SURVIVED.
- L1 attack: is `𝔭 := comap` maximal (not just prime)?  For Tate rings the
  localization map is NOT finite; maximality of the contraction is a genuine claim —
  in rigid geometry it holds for affinoid subdomain maps (max-spec functoriality,
  BGR 7.2.2/1-ish).  FLAGGED: L1.a must not assume it silently; if hard, weaken L2
  to "completed locals at all PRIMES pulled from maximals" or restate L1/L3 over
  the primes that occur.  The decomposition keeps `𝔭` as *the contraction* and L3
  quantifies over ALL maximals of the head PLUS (if needed) the contracted primes —
  L3's statements therefore take `[𝔭.IsPrime]` with local-ring completion, NOT
  IsMaximal, wherever the proof allows.  (Krull intersection needs only
  noetherian-local ✓ works at primes.)
- L3.a attack: `A_N[1/W] = K⟨W,U⟩[1/W]` is an ALGEBRAIC localization statement —
  fine — but the completed local comparison then needs the two rings' localizations
  at the SAME maximal to agree: they do, as the rings agree after inverting W ∉ 𝔭.
  SURVIVED (as algebra; the Tate-regularity leaf remains).

## Ticket chain (appended to the main board)
HRW-1 (L2) → HRW-2 (L1.a headToQ + maximality-or-primality) → HRW-3 (L1.b/c
comparison) → HRW-4 (L3.a Z-elimination + Tate-local leaf) → HRW-5 (L3.b tower) →
HRW-6 (L4 assembly + unconditional endpoints).  HRW-1 is dispatchable immediately
(pure mathlib); HRW-2+ gated on W15/W16 (the QHead layer) which sit on the main
board's critical path anyway.


## L1.b refined statement draft (2026-07-30, HRW-3 opening round)

Fix DH rational over the head H := WPHead K w N, the model Q := QHead DH =
H⟨T⟩/(graph), 𝔮 ⊂ Q maximal, 𝔭 := 𝔮.comap (headToQ DH) (prime, HRW-2; s ∉ 𝔭).

Observation that SIMPLIFIES the plan: DH.s is a GLOBAL unit of Q
(isUnit_headToQ_s, HRW-2) — so "s invertible mod every power" is just
IsUnit.map; no nilpotent-lifting needed.

Proposed finite-level statement (level n ≥ 1):
  `finiteLevel_comparison n :
     (Localization.AtPrime 𝔭) ⧸ (𝔭·loc)^n ≃+* Q ⧸ 𝔮^n`
via: the composite H → Q → Q/𝔮ⁿ kills 𝔭-powers?? NO — the honest route per the
reviewer: build the map H/𝔭ⁿ-side → Q/𝔮ⁿ from headToQ (functoriality), show:
(i) SURJECTIVITY: Q is generated over headToQ(H) by the T_i, and mod 𝔮ⁿ each
    T_i is the image of f_i · s⁻¹-lift: T_i·s = f_i in Q ⇒ T_i = f_i·s⁻¹
    GLOBALLY in Q (s unit!) ⇒ Q = headToQ(H)[s⁻¹]-image — Q is generated by
    the image of H and s⁻¹ alone. Mod 𝔮ⁿ: s⁻¹-image is the inverse of the
    image of s — lands in the SUBRING generated by H-image iff the inverse is
    hit; use Localization.AtPrime 𝔭 (s ∉ 𝔭 ⇒ s already invertible there):
    so the natural map (AtPrime 𝔭) → Q_(𝔮-local data) hits everything.
    CLEANER TARGET: `Localization.AtPrime 𝔭 →+* Localization.AtPrime 𝔮`-INDUCED
    map is SURJECTIVE-after-completion... Honest statement chosen:
      φ : Localization.AtPrime 𝔭 →+* Localization.AtPrime 𝔮
      (headToQ-localized; s, and everything outside 𝔭, invertible on the right
       since (headToQ)⁻¹(𝔮) = 𝔭)
    with (I) φ SURJECTIVE (generators: T_i = f_i·s⁻¹ ∈ image; Q-elements are
    H⟨T⟩-classes = limits… NO — algebraically Q's elements are RESTRICTED
    SERIES classes, not polynomial classes: surjectivity of φ is NOT purely
    algebraic — it needs the mod-𝔮ⁿ collapse: restricted series ≡ polynomials
    mod 𝔮ⁿ — the ORIGINAL L1.b frontier, restated as:
      (I') for every n, the composite AtPrime 𝔭 → AtPrime 𝔮 → (AtPrime 𝔮)/𝔪ⁿ
      is surjective  [the reviewer's "mod every power the variables evaluate
      uniquely"; content: a restricted series in T with coefficients in H,
      viewed mod 𝔪_𝔮ⁿ, equals a POLYNOMIAL in T over (localized) H — because
      high ϖ-adic tails die: ϖ ∈ 𝔪_𝔮?? FALSE (ϖ unit). The genuine mechanism:
      T_i − f_i/s ∈ ker(Q → Q) is ZERO in Q — T_i IS f_i/s in Q itself!! So Q
      = closure of headToQ(H)[f_i/s] = closure of (AtPrime-image); the
      SUBRING-image of AtPrime 𝔭 is DENSE, and mod 𝔮ⁿ...
      REFRAME (II): Q as a MODULE/ALGEBRA: Q = (H-image)·closure; the quotient
      Q/𝔮ⁿ is a FINITELY GENERATED H-module?? If Q/𝔮ⁿ is noetherian-artinian
      with the H-image DENSE in a topology that Q/𝔮ⁿ sees discretely, density
      ⇒ surjectivity — the route: Q/𝔮ⁿ is a finite-dimensional-like quotient
      in which the ϖ-adically-dense subring maps onto: needs "𝔮ⁿ is OPEN in
      Q" (a cofinite-topology fact: maximal ideals of Tate-algebra-like rings
      are closed, powers open?? — 𝔮 open ⟺ Q/𝔮 discrete ⟺ ϖ-image
      invertible-with-small-inverse… PLAUSIBLE via: Q/𝔮 is a FIELD receiving
      a Tate ring map; the image of the topologically-nilpotent unit ϖ has
      ϖⁿ → 0; in a field with the quotient(-discrete?) topology…
      HONEST FLAG: openness of maximal ideals in strongly-noetherian Tate
      rings = Wedhorn 7.45-adjacent (the SAME 7.45 whose repo-artifact retains
      a sorry!). CHECK: the repo's `_aux_nonOpen_hSpa_points…` sorry is about
      NON-open primes; for MAXIMAL ideals of A⟨T⟩-quotients openness might be
      exactly BGR's Nullstellensatz-adjacent statement.)
    ⇒ ADJUDICATION NEEDED (queued for the next ChatGPT round, after L3):
      is "every maximal ideal of a strongly noetherian Tate ring is open
      (equivalently: the residue field is discrete??)" true/false, and is
      there a Nullstellensatz-free proof for the specific Q = QHead?
(ii) KERNEL: ker(AtPrime 𝔭 → (AtPrime 𝔮)/𝔪ⁿ) = 𝔪_𝔭ⁿ-related — via flatness
     of φ?? or directly: 𝔮 ∩ H-image = 𝔭-image (definition of contraction) +
     unit-denominators. Statement shape:
      (II') φ⁻¹(𝔪_𝔮ⁿ) = 𝔪_𝔭ⁿ  — needs φ FLAT or the graded argument
      gr(φ) injective. FLAG: this is where "genuinely new math" concentrates.
(iii) then AdicCompletion functoriality (mathlib AdicCompletion.map along the
      level tower) gives the completed comparison.

Bottom line: L1.b decomposes into (I'-openness/surjectivity mod powers) +
(II'-kernel) + (iii-limits); (I') hinges on OPENNESS OF 𝔮 — adjudicate before
any Lean is written.


## L3 REARCHITECTED (2026-07-30 ChatGPT-5.6-xhigh adjudication — supersedes the L3.a/L3.b chart split)

**The finite-embedding shortcut**: P := WPHead K w N embeds FINITELY into the
full Tate algebra Q := K⟨W, U_0..U_N⟩ via Y_i ↦ W^{w_i}·U_i, Z_i ↦ U_i²
(injective by the existing support argument; Q is P-module-finite with basis
{U^ε : ε ∈ {0,1}^{N+1}}). For 𝔪 maximal in P: A := P_𝔪, C := (P∖𝔪)⁻¹Q is
semilocal finite over A; noetherian completion exactness
(`AdicCompletion.map_exact` + `ofTensorProductEquivOfFiniteNoetherian`) gives
Â ↪ Ĉ^{𝔪C} ≅ ∏_j (C_{𝔫_j})^ (semilocal decomposition: Jacobson-radical
nilpotence mod 𝔪C + CRT for powers + completion-of-products — a modest
hand-build, ~500-1000 LOC). Each C_{𝔫_j} is a LOCAL RING OF THE FULL TATE
ALGEBRA Q ⇒ reduced (domain) by THE TATE LEAF. isReduced_of_injective closes.
NO chart split, NO char-2 special-casing (char-2: Q/P radicial over the
singular locus — one point above, giving DOMAIN there; char≠2: several points
= the genuine formal branches — reduced only, as it must be).

**THE TATE LEAF** (the one remaining analytic input): completed locals of
K⟨X_1..X_d⟩ at maximals are domains. Adjudicated least-work route
(~1350-2750 LOC, 6-11 sessions):
1. Affinoid Nullstellensatz (BGR 6.1.2/3): residue fields finite over K
   (500-1000 LOC — the big sub-leaf).
2. Scalar-extend to B := L⟨X⟩ (L := A/𝔪 finite); the point rationalizes:
   𝔫 = (X_i − x_i) maximal over 𝔪.
3. A_𝔪 → B_𝔫 faithfully flat local + cofinal adic topologies
   (𝔫^e ⊆ 𝔪B_𝔫 via the zero-dimensional finite fibre).
4. ⇒ Â_𝔪 ↪ B̂_𝔫.
5. B̂_𝔫 ≅ L⟦T_1..T_d⟧ by truncated Taylor at the rational point
   (B_𝔫/𝔫^r ≅ L[T]/(T)^r levelwise; inverse limits).
6. MvPowerSeries L is a domain (mathlib NoZeroDivisors) ⇒ done.
Explicitly AVOID: coefficient fields, Cohen structure, completion-of-regular-
is-regular, associated-graded theory (route (iii) is sound but costlier:
gr-domain ⇒ completion-domain via projection-kernel filtration + initial
forms — reusable infra if ever wanted; mathlib has NEITHER
gr(regular) ≅ Sym(m/m²) NOR the gr-criterion today).

**L3.b truth clarified**: at the ORIGIN the completed local IS a domain in
every characteristic (parity-support embedding into F⟦W,T⟧, Y_i ↦ W^{w_i}T_i,
Z_i ↦ T_i² — disjoint parity supports); at general singular points char ≠ 2
it is REDUCED with several branches (Y² − W^{2w}(c+T) splits); char 2 domain
after purely-inseparable rationalization (V := Y − W^w·d, V² = W^{2w}T).
The finite-embedding route makes all of this automatic.

**CM/Serre route (d) adjudicated AGAINST**: mathematically fine (W is a
non-zero-divisor mod the relations via the U^ε-free basis ⇒ minimal primes
avoid W ⇒ ∂/∂Z-Jacobian unit there, char-free) but mathlib has no
R_0+S_1/CM/unmixedness framework — 2500-5000 LOC. Rejected.

**Warning recorded**: "P is a domain" does NOT imply completed locals
generically reduced (noetherian local domains can have nonreduced
completions) — never shortcut via the global domain fact alone.

### Revised ticket map
- HRW-4 (retitled): THE TATE LEAF — open with its own decomposition round:
  N1 affinoid Nullstellensatz; N2 rationalization+flat-local-cofinal; N3 the
  L⟦T⟧-completion; N4 transport. Start with N1's decompose.
- HRW-5 (retitled): the finite-embedding semilocal reduction (P ↪ Q,
  module-finiteness, semilocal completed decomposition, assembly into
  head_completedLocal_reduced). Independent of N1-N4 except the final glue.
- HRW-3 (unchanged): the L1 comparison; the drafted openness-pivot question
  still needs its own adjudication round.


## HRW-5 subring-coding simplification (2026-07-30 recon)

In the PROJECT's coding the finite embedding is TRIVIAL to define:
- WPMem w t := wpWeight w t ≤ t 0, HeadMem w N := WPMem w ∧ support ≤ N.
- At w' := 0: wpWeight 0 t = 0 ≤ t 0 always ⇒ **WPHead K 0 N is the FULL
  restricted Tate algebra K⟨W, U_1..U_N⟩** (variable 0 = W).
- WPMem w t ⇒ WPMem 0 t ⇒ **wpHeadSupport K w N ≤ wpHeadSupport K 0 N and the
  embedding P ↪ Q is literally `Subring.inclusion`** (the W18 pattern
  `Subring.inclusion (wpHeadSupport_mono …)` — check the exact mono-lemma
  covers weight-comparison, else 3-line new mono lemma).
- The paper's presentation dictionary: W = X_0, Y_n = X_0^{w n}·X_n
  (weight-tight monomial), Z_n = X_n² — Y_n² = W^{2w n}Z_n automatic.
- MODULE-FINITENESS in this coding: every Q-monomial splits as
  (even part) × U^ε with the even part X^{2⌊t/2⌋}W^{t0} ∈ P (wpWeight of an
  even exponent is 0 ≤ t0) ⇒ **Q = Σ_{ε ∈ {0,1}^{[1..N]}} P·U^ε** — the
  parity-support decomposition ALREADY used by the domain/FormalReduced
  machinery. U_n² = X_n² ∈ P directly.
- Q is strongly noetherian Tate BY INSTANTIATION: isStronglyNoetherian_WPHead
  at (w := 0) — zero new analytic work.
- So HRW-5 = (i) the mono-inclusion (trivial), (ii) the finite module
  decomposition (parity-splitting, ~150-300 LOC using existing support
  machinery), (iii) the semilocal completed decomposition (the genuinely new
  ~500-1000 LOC commutative algebra: A := P_𝔪, C := (P∖𝔪)⁻¹Q finite over A,
  Ĉ^{𝔪C} ≅ ∏ (C_𝔫)^, AdicCompletion.map_exact-injectivity), (iv) glue with
  the Tate leaf (HRW-4) at w = 0.


## L1 ADJUDICATED (2026-07-30 ChatGPT-5.6-xhigh — supersedes the openness-pivot draft)

The openness pivot was WRONG: 𝔮ⁿ is CLOSED but NOT open (B/𝔮ⁿ is a
finite-dimensional K-Banach space — Hausdorff, never discrete; a discrete
nonzero K-vector space would force K discrete). The mod-power collapse has a
different mechanism:

**The correct L1 chain** (all before localization!):
1. A → B := 𝒪_A(D) is FLAT — this is Wedhorn 8.30 = the central audit-pass-2
   WIP (prop_8_30_flat_clean)! L1 therefore ALSO funnels through it.
2. TRIVIAL SPECIAL FIBRE (the analytic heart): B ⊗_A κ(𝔭) ≅ κ(𝔭) at a point
   of the rational subset — via affinoid base change
   B/𝔭B ≅ κ(𝔭)⟨T⟩/(s̄T−f̄) and continuous evaluation T_i ↦ f̄_i/s̄ ∈ κ(𝔭)
   (needs κ(𝔭) finite/normed — Nullstellensatz-adjacent). Corollaries:
   𝔭B = 𝔮, κ(𝔭) ≅ κ(𝔮).
3. FLAT-SPECIAL-FIBRE INDUCTION (elementary, NO noetherian): R→S flat,
   J = IS, R/I ≅ S/J ⇒ R/Iⁿ ≅ S/Jⁿ ∀n (five lemma on
   0 → Iⁿ/Iⁿ⁺¹ → R/Iⁿ⁺¹ → R/Iⁿ → 0 tensored).
4. Inverse limits: AdicCompletion.evalₐ / surjective_evalₐ / ext_evalₐ +
   a `adicCompletionEquivOfQuotientPowEquiv` wrapper (new glue).
5. Graph algebra: C := A[T]/(sT−f), 𝔮₀ := 𝔮 ∩ C: C_s ≅ A_s, C/𝔭C ≅ A/𝔭 ⇒
   𝔮₀ = 𝔭C and A_𝔭 ≅ C_𝔮₀ (ordinary commutative algebra).
WARNING recorded: NO "completion mod arbitrary J" descent —
k[x,y]^(x)/(y) = k⟦x⟧ ≠ k[x]; Artin–Rees does not give it. Also B is NOT the
I-adic completion of abstract C (ϖ is a unit in C; completion happens at C₀).

**Lean leaf list (ChatGPT-provided, mathlib-support enumerated)**:
- quotient_pow_equiv_of_flat (Module.Flat + lTensor_exact five-lemma induction)
- adicCompletionEquivOfQuotientPowEquiv (evalₐ-API wrapper)
- RationalLocalization.map_comap_maximal + residueFieldEquiv (the NEW analytic
  heart: 8.30-flatness + rational residue base change)
- graphAtPrimeEquiv (thin polynomial-elimination wrapper)
- completedAtMaximalEquiv (assembly)
Mathlib available: Module.Flat(.lTensor_exact), IsLocalization.flat/
instFlatAtPrime, AdicCompletion.evalₐ/surjective_evalₐ/ext_evalₐ/map_exact/
map_injective/map_surjective, LocalRing completion API.

**REVISED WALL BOTTLENECK MAP**: everything funnels into ONE analytic cluster:
{affinoid Nullstellensatz (HRW-4-N1), closedness of ideals, 8.30-flatness
(central WIP), trivial special fibre}. The algebra around it (L1 induction,
semilocal decomposition, parity finiteness) is elementary and can be built
NOW. Recommended execution order: HRW-5(i,ii) parity module decomposition →
L1's quotient_pow_equiv_of_flat + graphAtPrimeEquiv (no analytic deps) →
HRW-4-N1 Nullstellensatz decompose round (the long pole) → fibre + assembly.


## THE TATE LEAF DECOMPOSED (2026-07-30 ChatGPT-5.6-xhigh — the N1 round; NO Weierstrass)

The noetherian-unit-ball hypothesis makes 𝒪_K a DVR (noetherian valuation ring
dichotomy) — the affinoid Nullstellensatz then goes through the INTEGRAL MODEL,
avoiding Weierstrass division, Noether normalization, closed maximal ideals,
and Banach-field machinery entirely. Polynomial-density and Berkovich routes
ADJUDICATED AGAINST (density gives a subRING not subfield — the maximality of
the polynomial contraction IS the hard analytic content; spectrum routes just
reformulate the Zariski lemma).

**The 11-leaf plan (total ~500-850 LOC)** for `Module.Finite K (T_d/𝔪)`:
1. DVR bridge: noetherian 𝒪_K + nontrivial norm ⇒ IsDiscreteValuationRing,
   uniformizer π (‖π‖<1, not unit). [Mathlib IsDiscreteValuationRing.TFAE +
   small normed-field bridge, 15-40 LOC]
2. T° := unit ball of T_d = restricted series with 𝒪_K coefficients
   (mem ↔ ∀ n, ‖coeff n‖ ≤ 1). [project-available, 10-30]
3. T°[1/π] ≃ T_d (∀f ∃N, π^N f ∈ T°). [new plumbing, 40-80]
4. T°/πT° ≅ k[X_1..X_d] (restricted coefficients die mod π cofinitely). [new, 50-100]
5. IsNoetherianRing T° — REUSE the vendored leading-term proof over the
   noetherian coefficient ring (NOT derivable from noetherianity of T!).
   [essential; check the Coram/vendored argument's generality, 50-200]
6. For maximal 𝔪: I := 𝔪 ∩ T°, B := T°/I: domain, noetherian, π ≠ 0,
   ¬IsUnit π in B (1−πg is a unit in T by geometric series!), B[1/π] ≅ T/𝔪.
   [assembly, 50-100]
7. **G-domain lemma** (the main algebra leaf, general): B noetherian domain,
   π ≠ 0 non-unit, B[1/π] a field ⇒ KrullDimLE 1 B ∧ KrullDimLE 0 (B/π):
   primes avoiding π are 0 (field localization); minimal primes over (π)
   finite + height ≤ 1 (principal ideal theorem:
   Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes); any nonzero prime
   gets trapped by finite prime avoidance (Ideal.subset_union_prime_finite).
   [new, 120-220]
8. C := B/πB: FiniteType k (via leaf 4) + KrullDimLE 0 (via 7). [25-50]
9. Module.Finite k C := Module.finite_iff_krullDimLE_zero. [Mathlib, 5-15]
10. **Topological Nakayama** (reusable): [IsPrecomplete J R] [IsHausdorff J M]
    [Module.Finite (R/J) (M/JM)] ⇒ Module.Finite R M — lift generators,
    coordinatewise precomplete R^n, surjective_of_mkQ_comp_surjective,
    Module.Finite.of_surjective. [new, 60-120]
11. IsPrecomplete (π) 𝒪_K (complete K, norm=π-adic) + IsHausdorff (π) B
    (Krull intersection, IsHausdorff.of_isDomain?) ⇒ Module.Finite 𝒪_K B ⇒
    localize: Module.Finite K (T/𝔪). [mixed, 50-100]

**Downstream (leaves 12-14, the completed-local step)**: finite scalar
extension T_L = L⟨X⟩ is FINITE FREE over T_K via a K-basis of L
(coefficientwise split; Basis ι T_K T_L; Free/Finite/Flat/FaithfullyFlat
instances all from mathlib generics); the L-rational point translates to the
origin (X ↦ X + a) and (T_L)_𝔫^ ≅ L⟦Y⟧ by Taylor; the caution: the completed
base-change needs AdicCompletion.ofTensorProductEquivOfFiniteNoetherian + the
"𝔪(T_L)_𝔫-adic = 𝔫-adic" cofinality (radicals agree). Faithful flatness +
domain L⟦Y⟧ ⇒ (T_K)_𝔪^ domain.

Mathlib inventory confirmed by the round: finite_of_finite_type_of_isJacobsonRing
(polynomial Zariski — NOT needed on this route but available),
Ideal.finite_minimalPrimes_of_isNoetherianRing,
Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes,
Ideal.subset_union_prime_finite, Ring.krullDimLE_zero_iff,
Module.finite_iff_krullDimLE_zero, IsPrecomplete/IsHausdorff API,
surjective_of_mkQ_comp_surjective, Module.Finite.of_isLocalization,
exists_finite_inj_algHom_of_fg (Noether normalization, theorem-form).

Execution note: leaf 7 (G-domain) + leaf 10 (topological Nakayama) are
GENERIC — build them first in a new generic file (TateAlgebraNullstellensatz.lean
or split); leaves 2-5 are the T°-plumbing block; leaf 5's noetherianity of T°
is the one leaf whose cost depends on the vendored argument's reusability —
probe it early.

## TATE LEAF execution state (2026-07-30 late)

DONE sorry-free + axiom-clean + committed:
- Leaves 1-11 COMPLETE ⇒ `module_finite_residue` (TateNullstellensatz.lean):
  **the affinoid Nullstellensatz** — Module.Finite K (P K m ⧸ 𝔪), via integral
  model + G-domain + topological Nakayama + K-scalar unit absorption.
- Leaf 12 COMPLETE (SpectralExtension.lean + TateScalarExtension.lean):
  spectral-norm package (extNormedField/extUltrametric/extCompleteSpace/
  ext_norm_algebraMap + ext_norm_le_one_of_monic_poly — direct ultrametric
  integrality bound, no minpoly descent) + P L m ≃ₗ[P K m] (ι → P K m)
  (scalarExtensionEquiv via bounded coordinate functionals) + finite/free.
- Leaf 13a COMPLETE (TatePointEval.lean): pointEval (mvEvalHomBounded ∘
  toTopRestricted bridge), constants/X laws, pointIdeal maximal, residue ≅ L.
- L1 ENGINE COMPLETE (FlatCompletion.lean): adicCompletionEquivOfFaithfullyFlat
  (faithfully flat + level-1 surjective ⇒ all levels bijective ⇒ completions
  iso). + AdicCompletion.congrLevel/congrPow (AdicNakayama.lean).

REMAINING:
- Leaf 13b: 𝔫_x = span(X_i − x_i) (division) + Taylor comparison ⇒
  AdicCompletion (pointIdeal x) (P L m) is a DOMAIN. ChatGPT adjudication of
  least-work shape pending (translation-to-origin vs direct division).
- Leaf 14: instantiate FlatCompletion at P K m → P L m (need FaithfullyFlat
  from free+nontrivial; level-1 surjectivity at 𝔪 → rationalized point;
  𝔪-cofinality) ⇒ (P K m)^𝔪-adic ↪ ∏-of-domains form.
- HRW-5(iii) semilocal decomposition; L1-specific leaves (graph flatness via
  prop_8_30_flat_clean — conditional on central audit-pass-2 trio;
  𝔪ₐB = 𝔪_B small lemma; level-1 graph evaluation).
