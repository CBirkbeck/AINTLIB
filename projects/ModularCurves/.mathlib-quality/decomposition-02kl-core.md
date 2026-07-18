# /develop --decompose — [02KL-CORE]: finite presentation reflects along a faithfully flat, finitely presented composite

**CLAIM (fable-FP, 2026-07-10, per v10.98 routing; board v10.99a).**
Target: `RingHom.FinitePresentation.of_comp_of_faithfullyFlat` — the sorried gate at
`ForMathlib/SmoothDescent.lean:127` (NEW-GH's file, read-only for me; my work lands in the new
`ForMathlib/FinitePresentationDescent.lean` and the gate is flipped to `exact` my theorem when done,
coordinated via board).

```
theorem RingHom.FinitePresentation.of_comp_of_faithfullyFlat
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {φ : R →+* S} {χ : S →+* T} (hff : χ.FaithfullyFlat) (hfp : χ.FinitePresentation)
    (h : (χ.comp φ).FinitePresentation) : φ.FinitePresentation
```

Consumers (all in SmoothDescent.lean, scheme layer PROVEN modulo this + [02KM-CORE], v10.99):
`lfp_of_precomp_of_isAffine` → `lfp_of_precomp_aux` → `LocallyOfFinitePresentation.of_precomp_of_surjective`
(Stacks 02KL) → `Smooth.of_precomp_etale_of_surjective` (Stacks 02KM) ⟹ [YF-QSM].
Arbitrary affine charts get plugged in ⟹ **full generality required; no noetherian escape.**

---

## 1. Source of record (verbatim, fetched 2026-07-08..10)

**Tag 02KK = Descent, Lemma 35.14.1** (the gate, verbatim):
> "Let $R \to A \to B$ be ring maps. Assume $R \to B$ is of finite presentation and
> $A \to B$ faithfully flat and of finite presentation. Then $R \to A$ is of finite
> presentation."

Dictionary: Stacks $(R, A, B)$ = gate's $(R, S, T)$; $A$ is the unknown-FP middle.

**02KK proof (fetched in full):** Set $C = B \otimes_A B$, $p(b) = b\otimes 1$, $q(b) = 1\otimes b$.
$R \to C$ is FP (base change + composition). To see $R \to A$ FP, apply Algebra 10.127.3 (Tag
00QO): for any directed colimit $S = \mathrm{colim}_\lambda S_\lambda$ of $R$-algebras and any
$A \to S$, factor through a stage. Set $B' = S\otimes_A B$, $C' = S \otimes_A C$; $S \to B'$ ffl+FP.
By Algebra 10.168.1 (Tag 02JO) part (2) there are $\lambda_0$ and a **flat** FP
$S_{\lambda_0}$-algebra $B_{\lambda_0}$ with $B' = S\otimes_{S_{\lambda_0}} B_{\lambda_0}$; set
$B_\lambda = S_\lambda \otimes_{S_{\lambda_0}} B_{\lambda_0}$, $C_\lambda = B_\lambda
\otimes_{S_\lambda} B_\lambda$. Faithful flatness of $S_\lambda \to B_\lambda$ for large
$\lambda$ via Morphisms 29.26.10 (Tag 01UA — flat+FP maps are open) / spectra surjectivity at a
stage. Since $B$, $C$ are FP over $R$, 10.127.3 yields $B \to B_\lambda$, $C \to C_\lambda$
**making the diagrams commute**; then $A \to B \to B_\lambda$ lands in the equalizer of
$p_\lambda, q_\lambda$, which is $S_\lambda$ by Lemma 35.3.6 (Tag 023M, Amitsur exactness). ∎

**Tag 00QO = Algebra, Lemma 10.127.3** (fetched): for $\varphi : R \to S$, TFAE: (1) FP; (2) for
every directed system $A_\lambda$, $\mathrm{colim}\,\mathrm{Hom}_R(S, A_\lambda) \to
\mathrm{Hom}_R(S, \mathrm{colim} A_\lambda)$ bijective; (3) same map surjective. (3)⟹(1) writes
$S$ as a directed colimit of FP algebras (10.127.2), factors $\mathrm{id}$, and concludes via
**retract-of-FP**.

**Tag 02JO = Algebra, Lemma 10.168.1** (fetched): $R \to S$ FP, $M$ FP $S$-module, $M$ flat over
$R$. Then (1) there is a finite-type-ℤ model $(R_0 \to S_0, M_0)$ with $M_0$ **flat over
$R_0$**; (2) for $R = \mathrm{colim} R_\lambda$ there exist a stage $\lambda$ and
$(S_\lambda, M_\lambda)$ FP+flat over $R_\lambda$ base-changing to $(S, M)$; (3) in any
compatible colimit presentation, $M_\lambda$ is flat over $R_\lambda$ for $\lambda \gg 0$. Proof
of (1): canonical ℤ-model system (10.127.18), per-prime flatness at a large index
(10.127.13, 10.128.3, 10.129.4 — noetherian stages: local criterion + openness of the flat
locus), quasi-compactness of $\mathrm{Spec}(S)$ for a uniform index.

**Tag 023M = Descent, Lemma 35.3.6** (fetched): for $R \to A$ faithfully flat, the extended
Amitsur cochain complex of any module is exact; degree-≤1 part = "the equalizer of
$A \rightrightarrows A\otimes_R A$ is $R$".

**Erratum on file docstrings** (boarded v10.99a): SmoothDescent.lean's "Stacks 02KG + 02KH"
locators are mispointed (cohomology flat-base-change 30.5.1/30.5.2). And the v10.75
"EXECUTION-READY" step 5 misreads `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`:
`CodescendsAlong` (RingHomProperties.lean:239) is the **pushout** form
`Q(algebraMap R R') → P(algebraMap R' (R'⊗[R]S)) → P(algebraMap R S)` — ffl leg *under the
common base* — and cannot be instantiated at the composite-reflection shape (the ffl leg here
sits over $S$). No cheap exit exists; verified against the definition.

## 2. Substrate scoreboard (pin-verified 2026-07-10)

| Leg | Status | Pin |
|---|---|---|
| Amitsur equalizer (023M, ring degree ≤ 1) | **FREE, in-project** | `Module.FaithfullyFlat.mem_range_algebraMap_iff_tmul_eq` (`ForMathlib/FaithfullyFlatEqualizer.lean`) |
| Stage-factoring of FP algebra into filtered colimit (00QO (1)⟹(2) surjectivity) | **FREE, mathlib** | `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` (`Algebra/Category/Ring/FinitePresentation.lean`) — categorical `IsColimit` interface; reproved concretely as [KL-5a] against my system predicate (cheaper than cocone transport; decision below) |
| Stage-agreement of two maps from an EssFT algebra (00QO injectivity) | **FREE, mathlib** (same file, `exists_comp_map_eq_of_isColimit`) — concrete twin = [KL-5b] |
| Chevalley (constructible image) | **FREE** | `PrimeSpectrum.isConstructible_range_comap` (needs FP ✓) |
| Patch-topology compactness | **FREE** | `compactSpace_withConstructibleTopology` (`Topology/Spectral/ConstructibleTopology.lean`) |
| Lazard / equational criterion of flatness | **FREE** | `Mathlib/RingTheory/Flat/EquationalCriterion.lean` (for [KL-3] internals) |
| FP cancellation | **FREE** | `RingHom.FinitePresentation.of_comp_finiteType` (FinitePresentation.lean:443) |
| FP base change, composition, quotient by FG, MvPolynomial | **FREE** | `Algebra.FinitePresentation.{baseChange?, trans, quotient, mvPolynomial}` |
| ffl base-change descent of FP/FT/Finite + `Ideal.FG.of_FG_map_of_faithfullyFlat` | **FREE** (wrong shape for the gate, machinery reusable) | `RingTheory/Finiteness/Descent.lean` (Merten 2026) |
| Retract-of-FP | ABSENT → **[KL-0]** |
| Canonical FP-approximation system (10.127.2) | ABSENT → **[KL-1]** |
| FP-algebra spreading over a system (02JO(2), flatless part) | ABSENT → **[KL-2]** |
| **Flat-at-stage (02JO(1)+(3))** | ABSENT (= A's ledger §8 gap) → **[KL-3] THE BOSS** |
| ffl-at-stage / Spec-surjectivity at a stage (01UA-leg) | ABSENT → **[KL-4]** |
| Composite assembly (02KK proper) | ABSENT → **[KL-5]** |

## 3. Architecture decision — "ENDING-1", concrete systems

**Key structural insight (removes two whole phases).** The stage map $A \to B_\lambda$ equalizes
$p_\lambda, q_\lambda$ **not** by factoring maps out of $A$ (impossible: $A$'s finiteness is the
conclusion!), but because $p \circ \chi = q \circ \chi$ holds *on the nose at the limit* (it is
the definition of $\otimes_A$: $\chi(a)\otimes 1 = 1 \otimes \chi(a)$ in $B\otimes_A B$), and the
finitely many commuting-square fixups are equalities of maps out of $B$ and $C$ — both FP.
Consequently:
- **No FT-prestep** (Stacks 35.14.2 never needed);
- **No maps-from-$A$ factoring**, hence no circularity;
- The only place $A$ enters is as the colimit of its canonical presentation system, consumed by
  the retract trick at the very end.

**Specialize the probe to $\theta = \mathrm{id}_A$**: run the entire argument on the single
system $\mathcal{S}_\lambda$ = canonical FP-approximations of $A$ (10.127.3's (3)⟹(1) only ever
uses this one system). Then $B' = B$, $C' = C$ — no auxiliary base change.

**Concrete over categorical.** Banked lesson (GRASS campaign, elaboration-stall memory):
mathlib's `IsColimit`/`Under R` transport is a stall-trap; bespoke concrete directed systems
with three-field colimit predicates build and rewrite cleanly. So: define
`IsFilteredAlgColimit` (compat + functoriality + joint surjectivity + eq-at-a-later-stage) and
prove the two Yang–Merten-shaped lemmas concretely against it ([KL-5a/b], ~140 lines total,
same proof shapes as the file's — presentations + relations dying at stages). The mathlib
categorical forms stay as cross-checks, not dependencies.

**ℤ-model reuse.** [KL-1] and [KL-2] are stated over an arbitrary base ring; [KL-3]'s
noetherian-model reduction re-instantiates them at base ℤ (stages are FT-ℤ = FP-ℤ by Hilbert
basis, and noetherian). Build once, use twice.

## 4. The proof, prose (assembly = [KL-5])

Let $\varphi : R \to A$, $\chi : A \to B$ ffl + FP, $\psi = \chi\varphi$ FP. All algebras via
`toAlgebra` + towers.

1. **[KL-1]** Let $(\mathcal{S}_i, t_{ij}, u_i)_{i \in I}$ be the canonical presentation system
   of $A$ over $R$: $I = \{(s, J)\}$, $s \in \mathrm{Finset}\,A$, $J$ an FG ideal of
   $R[x_s] := \mathrm{MvPolynomial}\,s\,R$ with $J \le \ker(\mathrm{aeval})$; stage
   $\mathcal{S}_{(s,J)} = R[x_s]/J$, FP over $R$; directed; joint surjectivity and
   eq-at-a-later-stage hold; colimit $A$.
2. **[KL-2]** $B$ is FP over $A$: descend a presentation $B \cong A[y_1..y_m]/(\bar g_1..\bar g_k)$
   to a stage $i_0$ (lift the finitely many coefficients jointly, at a common stage): get
   $g \in \mathrm{MvPolynomial}\,(\mathrm{Fin}\,m)\,\mathcal{S}_{i_0}$ and set, for $i \ge i_0$,
   $B_i := \mathrm{MvPolynomial}\,(\mathrm{Fin}\,m)\,\mathcal{S}_i / (t_{i_0 i}(g))$ — FP over
   $\mathcal{S}_i$, base-change-compatible, with $(B_i)_{i \ge i_0}$ again an
   `IsFilteredAlgColimit` over $R$ with colimit $B$, and $B \cong A \otimes_{\mathcal{S}_i} B_i$.
3. **[KL-3]** (BOSS) There is $i_1 \ge i_0$ with $B_{i_1}$ **flat** over $\mathcal{S}_{i_1}$
   (hence $B_i$ flat over $\mathcal{S}_i$ for all $i \ge i_1$ by base change). Internals: ℤ-model
   reduction ([KL-1]+[KL-2] at base ℤ under $\mathcal{S}_{i_0}$), noetherian local criterion of
   flatness per prime at a large stage, openness of the flat(=free) locus at noetherian stages,
   quasi-compact glue; then transport back along stage factoring. Sub-decomposed on reach
   (tickets [KL-3a..d] registered, statements in §5).
4. **[KL-4]** There is $i_2 \ge i_1$ with $\mathcal{S}_{i_2} \to B_{i_2}$ **faithfully** flat:
   fibre nonvanishing $B_{i}\otimes\kappa(\mathfrak p) = B_{i_1}\otimes_{\mathcal{S}_{i_1}}\kappa(\mathfrak p')$
   depends only on the contraction $\mathfrak p'$; $W := \mathrm{range}(\mathrm{comap}(\mathcal{S}_{i_1}\to B_{i_1}))$
   is constructible (Chevalley, $B_{i_1}$ FP ✓) hence patch-open; the stage images
   $I_i := \mathrm{range}(\mathrm{comap}(\mathcal{S}_{i_1} \to \mathcal{S}_i))$ are patch-closed
   (patch-compact source, patch-continuous comap, patch-T2 — small glue lemmas);
   $\bigcap_i I_i \subseteq W$ by the 1≠0-at-a-stage fibre-colimit argument + ffl of $A \to B$;
   patch-compactness of the directed family forces $I_{i_2} \subseteq W$ for some $i_2$, which is
   exactly Spec-surjectivity of $B_{i_2} \to \mathcal{S}_{i_2}$; flat + Spec-surjective = ffl.
5. **[KL-5]** Assembly. $C := B\otimes_A B$, $C_i := B_i \otimes_{\mathcal{S}_i} B_i$ ($i \ge i_0$),
   with $p_i, q_i : B_i \to C_i$ the two inclusions; $(C_i)$ is an `IsFilteredAlgColimit` with
   colimit $C$ ([KL-5c], tensor of systems). $B$ and $C$ are FP over $R$ ($B$: hypothesis;
   $C$: base change of $\chi$ FP over $B$ FP over $R$, cancellation-free composition). Factor
   $\mathrm{id}_B$ through a stage: $\beta : B \to B_{i_3}$ with $v_{i_3}\beta = \mathrm{id}$
   ([KL-5a] on the $B$-system). Fix up the two squares
   $p_{i}\beta \sim \gamma p$, $q_i\beta \sim \gamma q$ at a later common stage using [KL-5a]
   (factor $C \to C$ id) + [KL-5b] (two maps from FP $C$, resp. $B$, agreeing in the colimit
   agree at a stage) — finitely many conditions, directedness. At the resulting stage
   $i_* \ge i_2$: $\varepsilon := \beta_{i_*}\circ\chi : A \to B_{i_*}$ satisfies
   $p_{i_*}\varepsilon = q_{i_*}\varepsilon$ **on the nose** (transport of $p\chi = q\chi$).
   By Amitsur at base $\mathcal{S}_{i_*}$ (ffl ✓, project lemma), $\varepsilon$ lands in
   $\mathrm{range}(\mathrm{algebraMap}\ \mathcal{S}_{i_*}\ B_{i_*})$, which is injective (ffl),
   so $\varepsilon$ factors as $\sigma : A \to \mathcal{S}_{i_*}$ with
   $(\mathrm{algebraMap})\circ\sigma = \varepsilon$. Then $u_{i_*}\sigma = \mathrm{id}_A$
   (compose with the injective $\chi$ and chase: $\chi u_{i_*}\sigma = v_{i_*}\varepsilon =
   v_{i_*}\beta_{i_*}\chi = \chi$). So $A$ is a retract of the FP algebra $\mathcal{S}_{i_*}$;
   **[KL-0]** concludes $A$ FP over $R$; unwind `toAlgebra` for the `RingHom` form. ∎

## 5. Leaves (ordered; statements as in the skeleton)

- **[KL-0]** `Algebra.FinitePresentation.of_retract`: $\sigma : A \to_{\!\!R} B$,
  $\rho : B \to_{\!\!R} A$, $\rho\sigma = \mathrm{id}$, $B$ FP ⟹ $A$ FP.
  *Sketch*: $B$ FT ⟹ finite generators $b_j$; $\ker\rho = ({b_j - \sigma\rho(b_j)})$ (⊇ by
  $\rho\sigma=\mathrm{id}$; ⊆ since $q\circ\sigma\rho = q$ on generators ⟹ everywhere, so
  $\rho b = 0 \Rightarrow qb = q(\sigma\rho b) = 0$); `FinitePresentation.quotient` + transport
  along `Ideal.quotientKerAlgEquivOfSurjective` ($\rho$ surjective from $\rho\sigma=\mathrm{id}$).
  Stacks: inside 00QO (3)⟹(1). ~60 lines. Mathlib-shaped; upstream candidate.
- **[KL-1]** `IsFilteredAlgColimit` predicate + `Algebra.PresentationSystem` (canonical system):
  index `Σ (s : Finset A), {J // J.FG ∧ J ≤ ker (aeval val)}`, stages `R[x_s]/J` FP, order/maps
  by `rename`-descent, colimit fields. Stacks 10.127.2 (Tag inside 00QO's section). ~300 lines.
- **[KL-2]** spreading: FP $A$-algebra descends to presentations over a cofinal tail of stages,
  with colimit recovery and base-change identifications. Stacks 02JO(2), flatless half. ~300 lines.
- **[KL-3]** flat-at-stage (scoped 02JO(1)+(3)). Sub-tickets on reach:
  [KL-3a] ℤ-model reduction (reuse KL-1/2 at ℤ); [KL-3b] noetherian per-prime flatness at a
  stage (local criterion; Tor/ideal-form via `EquationalCriterion` or
  `Module.FinitePresentation` + free-locus); [KL-3c] openness of the flat locus at noetherian
  stages (`FreeLocus` bridge); [KL-3d] quasicompact glue + transport. Stacks 10.168.1,
  10.127.13, 10.128.3, 10.129.4. ~800–1600 lines. THE BOSS.
- **[KL-4]** ffl-at-stage: patch-glue lemmas (T2, comap patch-continuity, compact-image
  closedness — ~60 lines), fibre-contraction collapse, `⋂ ⊆ W`, directed compactness, flat+surj
  ⟹ ffl bridge. Stacks 01UA-leg of 02KK. ~400 lines.
- **[KL-5]** assembly: [KL-5a] concrete stage-factoring (FP source), [KL-5b] concrete
  stage-agreement (FT source), [KL-5c] tensor-of-systems colimit, then the chase of §4. ~500 lines.

## 6. Adversarial notes

- **Why no circularity**: maps out of $A$ are never factored; only $B$-, $C$-maps are. Checked
  against the fetched 02KK text ("since $B$ and $C$ are finitely presented over $R$... maps
  $B \to B_\lambda$ and $C \to C_\lambda$ making the diagram commute").
- **Why flat-at-stage is unavoidable**: the equalizer identification at stage $i$ *is* Amitsur
  at base $\mathcal{S}_i$, needing ffl of $\mathcal{S}_i \to B_i$; flatness cannot be replaced
  by a limit argument (equalizers don't factor through stages for non-FP subobjects — recorded
  failed shortcuts: pointwise landing gives no map; eq-of-colim = colim-of-eq needs the stage
  identification anyway; retract/module-splitting tricks all reduce to contraction-of-FG-ideals,
  false without flatness).
- **Why not Merten's base-change descent**: `CodescendsAlong` = pushout shape; there is *no* ffl
  $R$-algebra in the data. Verified at the definition.
- **Universe discipline**: gate is single-universe (`Type u`); all constructions stay in `u`
  (Finset-indexed MvPolynomial subtypes, Fin-indexed variables ✓).
- **Heartbeats**: no `set_option maxHeartbeats` anywhere (house rule); stall-risk mitigations
  per banked patterns (irreducible markers on coordinate-heavy defs if needed).
