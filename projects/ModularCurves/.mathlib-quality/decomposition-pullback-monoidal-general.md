# Decomposition (adversarial): D-PresPB′-general — the general-`f` pullback–tensor gate

**Goal.** The one math gate of the GME (2.16) functoriality chain (board v10.98):
`sh_Y(f^*ᵖ(P ⊗ Q)) ≅ sh_Y(f^*ᵖ P ⊗ f^*ᵖ Q)` for a **general** morphism of schemes `f : Y ⟶ X`
(`nonempty_sheafify_presheafPullback_tensor`, PullbackTensorMonoidal.lean, sorried), upgraded to
the form the payoff machinery consumes: **`(f^*ᵖ ⋙ sh_Y).Monoidal`** (full functor-monoidal), so
that `functorMonoidalOfComp` (Localization/Monoidal/Functor.lean:134, hypotheses verified: monoidal
localization `L`, `[G.Monoidal]`, `[Lifting L W G F]`) hands `(Modules.pullback f).Monoidal`, then
`Skeleton.monoidHom` (Monoidal/Skeleton.lean:111) gives `Pic(f) : Pic X →* Pic Y`.

**Worker.** fable-PIC0. **Mode.** `/develop --decompose` (adversarial, planning-only, no tickets).
**Prior state.** v10.78 decompose refuted presheaf-level strong monoidality for general `f`
(inverse-image left Kan extension) — the sheafified comparison is the true statement. The ι-case
(open immersions) is PROVED (v10.95); this pass sizes the general case.

---

## Step 0 — Route adjudication (three candidates, each attacked)

### Route S — stalkwise. **REJECTED (unbounded gap).**
The comparison is a stalkwise iso (stalk of inverse image = stalk at image; ⊗ commutes with
stalks). ATTACK: requires stalk API for the *abstract* presheaf pullback
(`pullback φ := (pushforward φ).leftAdjoint`, Pullback.lean:44) — stalk-of-Kan-extension for
`PresheafOfModules`. Grep-verified absent (no stalk machinery in `ModuleCat/Presheaf/`); building it
is its own sub-development of unknown depth. Prior sessions hit exactly this wall (the reason for
the ι-detour). REJECT as primary.

### Route L — Zariski-localize to the affine case. **VIABLE FALLBACK.**
(L1) `sh_Y`-invertibility (= local bijectivity) is Zariski-local on `Y` — elementary with the
ι-LOCBIJ toolkit (restriction preserves loc-bij; converse glue by sieve transitivity).
(L2) restriction-compat of the comparison map with `f|_V` — naturality grind, bounded.
(L3) the affine case `Spec B → Spec A`: reduces to tilde-compatibilities. ATTACK (grep-verified):
`Modules/Tilde.lean` has the functor, Γ, FF-embedding, stalks — but **no pullback-of-tilde and no
tensor-of-tilde**. `Γ(M~ ⊗ N~) ≅ M ⊗ N` is genuine quasi-coherence content — bounded (~2–3 leaves
of real algebra) but squarely in the future upstream QCoh lane → duplication risk. HOLD as fallback.

### Route G — construction-grain: agree on free-yoneda generators, extend by presentation. **CHOSEN.**
Rides mathlib's own construction of the pullback. Anchors (all grep/read-verified this pass):
- `freeFunctorCompPullbackIso : freeFunctor ⋙ pullback φ ≅ freeFunctor`
  (ModuleCat/Sheaf/PullbackFree.lean:145) and its presheaf-level ingredients — **the pullback of a
  free is free, in mathlib**.
- Generator.lean: `freeYoneda` (`:76`), `isSeparating` (`:86`), `isDetecting` (`:92`),
  `freeYonedaCoproductMk`/`fromFreeYonedaCoproduct` (`:156ff`) — **every presheaf of modules has an
  epi from a coproduct of free-yonedas** (and hence a two-step free presentation; the category is
  abelian, `Presheaf/Abelian.lean`).
- **The lattice miracle (the decisive arithmetic):** on an Opens-site, `yoneda U₁ × yoneda U₂` is
  representable by `U₁ ⊓ U₂` (`Hom(V,U₁) × Hom(V,U₂) = [V≤U₁]×[V≤U₂] = [V≤U₁⊓U₂]`), so the
  pointwise tensor of free-yonedas is again a free-yoneda:
  `freeYoneda U₁ ⊗ freeYoneda U₂ ≅ freeYoneda (U₁ ⊓ U₂)`
  (pointwise: `free(S) ⊗ free(T) ≅ free(S × T)` for the free-module functor). And the pullback
  matches: `f⁻¹(U₁ ⊓ U₂) = f⁻¹U₁ ⊓ f⁻¹U₂`. **The two composites literally agree on generators,
  including the tensor-interaction.**
- Colimit preservation: `sh_Y`, `f^*ᵖ` are left adjoints; presheaf-⊗ is pointwise with
  `ModuleCat`-⊗ cocontinuous in each variable (monoidal closed pointwise); colimits of presheaves
  of modules are computed pointwise (`Presheaf/Colimits.lean`, `ColimitFunctor.lean`). All four
  relevant functors are cocontinuous in each variable.

## Step 1 — Prose proof (Route G)

1. **The comparison map, globally (leaf B1).** Give `PresheafOfModules.pushforward φ` its lax
   monoidal structure (`ε`, `μ` sectionwise from `ModuleCat.restrictScalars.LaxMonoidal` +
   `pushforward₀OfCommRingCat.Monoidal`; the file-level model is PushforwardZeroMonoidal.lean).
   Then `Adjunction.leftAdjointOplaxMonoidal (pullbackPushforwardAdjunction φ)` hands `f^*ᵖ` its
   oplax structure; its `δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` is natural and coherent by
   construction. (This was route (A) of v10.78; the map-half was never the gap.)
2. **Agreement on generators (leaf G1).** For `P = freeYoneda U₁`, `Q = freeYoneda U₂`: both sides
   of `δ` are free-yonedas (`freeYoneda (f⁻¹U₁ ⊓ f⁻¹U₂)` after the lattice identification and
   `freeFunctorCompPullbackIso`), and `δ` matches the canonical identification (check on the
   universal element via `freeYonedaEquiv`; a finite `simp`-calculation, not new math). Hence `δ`
   is an **iso on free-yoneda pairs** — before sheafifying.
3. **Extension by presentation (leaf G3).** Fix `Q`; both `P ↦ sh_Y(f^*ᵖ(P⊗Q))` and
   `P ↦ sh_Y(f^*ᵖP ⊗ f^*ᵖQ)` are cocontinuous (composites of cocontinuous functors; `sh_Y ∘ −`
   lands in the abelian `SheafOfModules`). Present `P` as a cokernel of a map of coproducts of
   free-yonedas (Generator.lean machinery). `sh_Y.map δ` is a natural transformation between
   right-exact coproduct-preserving functors that is an iso on the presenting objects **when `Q`
   is free-yoneda** (step 2); the five lemma in the abelian `SheafOfModules` gives
   `IsIso (sh_Y.map (δ_{P, freeYoneda U₂}))` for all `P`. Repeat in the `Q`-variable (with `P` now
   arbitrary, using the just-proved case as the generator input): `IsIso (sh_Y.map δ_{P,Q})` for
   all `P, Q`. (Two single-variable passes — no bifunctor-density abstraction needed.)
4. **Packaging (leaf A).** `μIso := asIso`-family from 3 assembles `(f^*ᵖ ⋙ sh_Y).CoreMonoidal`
   (naturality/coherence: δ's oplax coherences + `sh_Y`'s monoidal structure — mechanical);
   `Lifting`-instance from `sheafificationCompPullback`; `functorMonoidalOfComp` ⟹
   `(Modules.pullback f).Monoidal`; `Skeleton.monoidHom` ⟹ `Pic(f) : Pic X →* Pic Y`; naturality
   `Pic(f ≫ g) = Pic(g) ∘ Pic(f)` from `pullbackComp` (mathlib) — the GME (2.16) functor.

## Step 2 — Leaves (ordered; skeleton in `ForMathlib/PullbackTensorGeneral.lean`)

| # | Leaf | Content | Size | Risk |
|---|------|---------|------|------|
| B1 | `instance (pushforward φ).LaxMonoidal` | sectionwise `restrictScalars_μ` + naturality | ~80–120 ll | elaboration-grind only (v10.95 recipes apply) |
| B2 | `def pullbackOplax := leftAdjointOplaxMonoidal …` | one-liner + `δ`-elementwise lemmas | ~30 ll | none |
| G1 | `freeYonedaTensorIso` + `δ`-on-frees | lattice miracle + `freeYonedaEquiv` chase | ~60–100 ll | the pointwise `free(S)⊗free(T)≅free(S×T)` lemma may need building (`ModuleCat.free` monoidal — CHECK: `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean` has `(free R).Monoidal`? — verified pattern exists for `Type ⥤ ModuleCat` free functor, `free.Monoidal`-style) |
| G2 | cocontinuity bookkeeping | instances, mostly `inferInstance` | ~20 ll | low |
| G3 | presentation five-lemma, two passes | abelian-category comparison | ~100–150 ll | the real grind; all ingredients standard |
| A | packaging → `(pullback f).Monoidal` → `Pic(f)` | CoreMonoidal + Lifting + monoidHom | ~80 ll | coherence-`simp`s |

**Total honest estimate: ~400–500 ll across 6 leaves, no absent-from-mathlib deep facts.** Compare
route L: fewer leaves but (L3) is genuine QCoh content with upstream-collision risk; route S:
unbounded. **Route G confirmed.**

## Step 4.5 — Attacks on the chosen route (survivors)

- *G1-attack: is `free(S) ⊗ free(T) ≅ free(S × T)` actually available pointwise?* `ModuleCat.free R`
  is left adjoint to `forget`; its monoidality over a CommRing (`Type` with products → `ModuleCat`
  with ⊗) is the classical `Finsupp.tensorProduct`-style iso — mathlib has
  `finsuppTensorFinsupp`/`TensorProduct.finsuppLeft` machinery; if the categorical packaging is
  absent it is a bounded wrapper, not new math. SURVIVES (named check at build time).
- *G3-attack: five lemma needs the comparison to be between EXACT functors — is `sh_Y ∘ (f^*ᵖ − ⊗ f^*ᵖ Q)`
  right-exact in `P`?* All factors preserve colimits (left adjoints / pointwise-⊗ / sheafification);
  right-exactness = preservation of finite colimits ✓ subsumed. SURVIVES.
- *G3-attack: coproducts are not finite — five lemma alone insufficient?* Use cocontinuity for the
  (possibly infinite) coproducts of the presentation + five lemma for the cokernel step. Standard
  presentation argument; both categories abelian with exact coproducts (AB4-ish; SheafOfModules is
  Grothendieck — verify the coproduct-exactness instance at build; if AB4 packaging is thin, restate
  the presentation with the epi `fromFreeYonedaCoproduct` + kernel, still five-lemma-shaped). SURVIVES
  with a named build-time check.
- *A-attack: `functorMonoidalOfComp` needs `Lifting L W G F` — is `sheafificationCompPullback` in the
  right form?* Lifting is exactly "an iso `L ⋙ F ≅ G`" registered as an instance
  (`Lifting.iso`-consumed); `sheafificationCompPullback : sh_X ⋙ pullback f ≅ f^*ᵖ ⋙ sh_Y` is that
  iso verbatim. SURVIVES.
- *Scope-attack: does PIC0 need general `f` at all, or only `E_T → T` structure morphisms?* GME
  (2.16) pulls back along arbitrary `T' → T` and along `f_T : E_T → T`; both are general (not open
  immersions). General `f` is the honest target. SURVIVES.

## Feasibility

**FEASIBLE, bounded, construction-grain.** Six leaves, ~400–500 ll, no deep absent facts; the two
flagged build-time checks (categorical `free`-monoidality packaging; AB4/coproduct-exactness
instance for `SheafOfModules`) are wrappers if absent, not math. The payoff is the full GME (2.16)
chain: `(Modules.pullback f).Monoidal` → `Pic(f) : Pic X →* Pic Y` (+ `pullbackComp` functoriality).
Recommended build order: B1 → B2 → G1 → G3 → G2/A.

## Next step
Planning-only (no tickets). On build GO: work B1 first (the v10.95 elaboration recipes — literal
spellings, `AddEquiv.toLinearEquiv` idiom, `respectTransparency` set_options — apply directly).

## B1a build reconnaissance (banked 2026-07-10, two LSP-measured attempts)

Attempted B1a with components := mathlib's `Functor.LaxMonoidal.ε/μ (ModuleCat.restrictScalars
(ψ.app U).hom)`. FINDING: the `where`-fields elaborate (the pointwise defeq is accepted), but the
NATURALITY goals then mix the presheaf-clothed types (`((rs ψ P ⊗ rs ψ Q).obj V`) with the raw
ModuleCat-tensor spellings — "target not type-correct under instances transparency" — and neither
`dsimp` nor `simp only [restrictScalars_μ_tmul]` can fire (the dsimp%-decorated lemmas need the
raw spelling; the goal has the clothed one). Two measured failures; do NOT repeat this shape.

**The winning pattern for next session (v10.95-proven):** build the components as OWN defs in the
clothed types from the start —
- μ-app := `ModuleCat.ofHom (X := ((restrictScalars ψ).obj P ⊗ (restrictScalars ψ).obj Q).obj U)
  (Y := ((restrictScalars ψ).obj (P ⊗ Q)).obj U) (TensorProduct.mapOfCompatibleSMul …)-based`
  linear map with the v10.95 compHom/tower `letI`-chain. NOTE: the LAX direction
  (`M ⊗[R-down] N → M ⊗[S-up] N`, tmul↦tmul) needs `CompatibleSMul S-up R-down M N` only — the
  down-action slides because it factors through ψ — **NO bijectivity hypothesis** (unlike the
  v10.95 iso which needed it for the inverse). `mapOfCompatibleSMul_tmul` is rfl.
- ε-app := the ring map `ψ.app U` as a hint-typed `ofHom` linear map (`RestrictScalars.map'`-style
  `(X :=) (Y :=)` hints — the ChangeOfRings TODO-comment pattern).
- Then all naturality/coherence proofs are `tensor_ext` + own-rfl-tmul-lemmas (the
  restrictScalarsTensorIso_hom_tmul pattern that worked), never mathlib's dsimp%-forms.

## Build-progress ledger (2026-07-10, session 2)

**LANDED (axiom-clean):** B1a `restrictScalarsLaxMonoidal` (all five coherences by elementwise
`rfl` — everything tmul↦tmul); B1+B2 fused `nonempty_pullback_oplaxMonoidal` via
`pushforwardFactored` + componentwise-refl NatIso + **`Adjunction.ofNatIsoRight`** +
`leftAdjointOplaxMonoidal`. BANKED HARD RULE: never re-type a lax/monoidal STRUCTURE across
functor-spellings (kernel autoParam-wart — composite-vs-pushforward ascription rejected by the
kernel in both def- and theorem-form; native-spelling direct construction hit a 6-iteration
instance-flavor wall on the F.op-composites). **Transport the ADJUNCTION to the good spelling
instead** — one componentwise-`Iso.refl` NatIso, then the doctrinal machinery runs natively.

**G1 construction plan (banked, next session):**
- meet-equiv `e V : (V ⟶ U₁) × (V ⟶ U₂) ≃ (V ⟶ U₁ ⊓ U₂)` — Opens-homs are subsingletons;
  `homOfLE (le_inf ...)` / projections; proofs by `Subsingleton.elim`.
- component at `V` := `Functor.Monoidal.μIso (ModuleCat.free (R'.obj V)) _ _ ≪≫
  (ModuleCat.free _).mapIso (crossing ⊗-Type ≡ ×) (e V.unop).toIso` — anchors:
  `(ModuleCat.free R).Monoidal` (Adjunctions.lean:159), `μIso_hom_freeMk_tmul_freeMk` (:143),
  `εIso_inv_freeMk` (:129), `freeMk := Finsupp.single x 1` (:48);
  `PresheafOfModules.freeObj` pointwise (`Free.lean:42`).
- ⚠ the isoMk **naturality squares mix the ring-restriction with μ** (freeObj.map is
  `freeDesc (freeMk ∘ F.map f)` ACROSS the restricted ring — not a pure Type-functorial image,
  so μ-naturality-in-Type-args alone is insufficient). Expect elementwise
  `tensor_ext` + `Finsupp`-generator chases with `μIso_hom_freeMk_tmul_freeMk` +
  `restrictScalars_μ`-analogues (~100 ll, several LSP iterations).
- then δ-on-frees: identify `δ_{freeYoneda,freeYoneda}` with the canonical iso via
  `freeYonedaEquiv`-universal-element chase; `freeFunctorCompPullbackIso` matches the pullback side.

**G3 unchanged** (two single-variable presentation passes). **A unchanged** (CoreMonoidal +
Lifting + functorMonoidalOfComp). Chain state: B1 ✓ B2 ✓ | G1 → G3 → G2/A remaining.

## G1 build ledger (2026-07-10, session 3)

**GREEN (axiom-clean):** `meetHomEquiv` + `yonedaMeetIso` (the meet half — Equiv extracted
standalone so α/β stay raw before `toIso`; naturality via a Subsingleton-bridge haveI);
`freeTensorμ` (the pointwise component, hint-typed `LinearEquiv.toModuleIso
(X₁ :=)(X₂ :=)` of `finsuppTensorFinsupp'`) + its generator-behaviour
`freeTensorμ_hom_freeMk_tmul` / `freeTensorμ_inv_freeMk` — **the mathematical content of the
lattice miracle is proved**; the leaf-closure `nonempty_freeYoneda_tensor_iso'` chains through:

**[G1-NAT] — the focused residual (one naturality square), 10-iteration ledger:**
`free(F)⊗free(G) ⟶ free(F⊗G)` components vs restriction. Measured failure modes, in order:
(1) casting mathlib's `FreeMonoidal.μIso` into the isoMk-component slot → goal
"not type-correct under instances transparency", kabstract aborts (the banked B1-rule
generalizes: NEVER cast a structure/iso across spellings — hint-type it);
(2) with hint-typed `freeTensorμ`: `ModuleCat.free_hom_ext` REFRAMES the domain to
`(ModuleCat.free R).obj`-spelling → same type-incorrectness (use plain `ext`, which keeps the
presheaf spelling);
(3) `ext` gives a GENERAL Finsupp element → `Finsupp.induction_linear` descent WORKS
(cases fire; qualify `_root_.map_add/_smul/_zero` against `Functor.map_*` ambiguity);
(4) the single-case's `rw [hs, 4×map_smul]` then whnf-timeouts at the closed-arg
`freeTensorμ_inv_freeMk`-rw — the smul-rewrites re-clothe the applied terms.
**Next-session attack (fresh context):** in the single-case avoid the smul-shuffle — state
`hs : single a r = r • freeMk a` and instead of rw-chains do
`simp only [hs, _root_.map_smul]` then `congr 1` then the three closed-arg rewrites; OR
restate the naturality goal per-generator FIRST via `Finsupp.lhom_ext'`-applied with explicit
instances at the presheaf carriers; OR prove the square as `freeHomEquiv`-naturality
(Free.lean's adjunction machinery — `freeHomEquiv_comp` both ways, no elementwise work).
Estimated: 1 focused session-chunk.

## [G1-NAT] delta-ledger — freeHomEquiv-adjunction route, 4 measured iterations (2026-07-10, session 4; STOP-LINE honored)

**NET DELTA: the residual REDUCED.** [G1-NAT] (a ModuleCat naturality square mixing ring-restriction
with the tensor of free maps — the 10-iteration wall) is now **[G1-NAT′]: ONE Types-level square**
(the pairing `z ↦ freeMk z.1 ⊗ₜ freeMk z.2` vs restriction, inside `freeTensorPair`) — plain
functions, no module clothing. Everything else on the route LANDED GREEN:
- `clothedFree_hom_ext` — `ModuleCat.free_hom_ext` restated at the presheaf clothing (the mathlib
  form's reframing poisoned kabstract twice; the defeq crossing now happens once, at elaboration).
  **Reusable anti-reframing tool — add to the fleet recipe set.**
- `freeTensorPair` (modulo the one square) + `freeTensorDesc` (naturality via `freeObjDesc` — the
  universal property supplies it).
- The FULL IsIso-assembly: per-V identification `happ : Desc.app V = (freeTensorμ V).inv` (via
  `clothedFree_hom_ext` + generator-calc + closing `rfl`), per-V iso, transport to the underlying
  AddCommGrp NatTrans (`NatIso.isIso_of_isIso_app`), reflection along `toPresheaf` — so
  `nonempty_freeTensorIsoGeneric` is proved MODULO [G1-NAT′] only.

**Iteration log:** (1) show-pattern vs `↾`-composite `.toFun`-form mismatch; (2) clothedFree_hom_ext
breakthrough — happ reached generator-form; types_comp_apply/forget_map didn't distribute the
Types-composite; (3) show-retype still not defeq to the `.toFun`-form; (4) `simp [presheaf]`
(mathlib's own idiom for the unit's square) EXPOSED AddCommGrpCat.ofHom/AddMonoidHom.mk'-internals
and made the goal type-incorrect-at-instances. **The `.toFun`-composite normalization for
Types-valued presheaf squares is the one unsolved plumbing question.**

**Ranked next attacks for [G1-NAT′] (fresh session):** (a) prove the square as an equality of
Types-NatTrans-components via `NatTrans.ext`+`funext` FIRST, i.e. state `freeTensorPair` with a
naturality PROOF-TERM built as `funext (fun z => congr-chain)` in term mode (never enter the
`.toFun`-tactic-goal); (b) find/mimic how mathlib's `freeAdjunctionUnit` square elaborates
(`ext; simp [presheaf]` works THERE — diff the two goals to isolate what the ⊗-side adds);
(c) restate the pairing target through `(toPresheaf _).obj`+`forget` instead of
`.presheaf ⋙ forget` if the spellings differ. Budget: 3–4 iterations, same stop-line.

## ★ G1 COMPLETE + G3 design upgrade (2026-07-10, session 4 owner-directed continuation)

**G1 CLOSED, axiom-clean.** [G1-NAT′] fell to attack (a) in 4 further iterations: the funext-TERM
attempt type-checked the per-element proof and thereby REVEALED the exact evaluated goal-shapes;
`ext z` + that `show` + the closed chain (`tensorObj_map_tmul` → 2× new `freeObj_map_freeMk`
@[simp] helper → `tensor_apply` → `rfl`) closed it. METHOD NOTE (fleet-grade): when a `show`
keeps missing a tactic-goal's shape, run the equivalent TERM-mode proof first — its inferred
endpoint types are the ground truth for the `show`.

**G3 DESIGN UPGRADE (supersedes the hand-rolled two-pass five-lemma).** Mathlib's own pullback
construction (Presheaf/Pullback.lean:56–100) provides exactly the two tools:
- `pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X` — **`f^*ᵖ(freeYoneda X)` is
  corepresented by `freeYoneda (F.obj X)`**, with EXPLICIT homEquiv = `freeYonedaEquiv`-conjugation
  (the generator-chase substrate for δ-on-frees).
- `M.isColimitFreeYonedaCoproductsCokernelCofork` — the canonical free-yoneda presentation of any
  presheaf of modules, packaged as an `IsColimit` (mathlib derives the pullback's existence from it
  via `leftAdjointObjIsDefined_of_isColimit`).
**G3 route:** fix Q; `sh_Y ∘ f^*ᵖ(− ⊗ Q)` and `sh_Y ∘ (f^*ᵖ(−) ⊗ f^*ᵖQ)` are cocontinuous; `sh∘δ`
restricted to the presentation diagram is an iso once **[G3-pre]** (δ-on-free-pairs) is done; conclude
`IsIso (sh∘δ)_P` by colimit-comparison (`IsColimit.coconePointsIsoOfNatIso` + identify the induced
map with (sh∘δ)_P by naturality) — repeat in Q. **[G3-pre]:** δ-at-free-pairs is out of
`f^*ᵖ(freeY U₁ ⊗ freeY U₂) ≅ f^*ᵖ(freeY (U₁⊓U₂)) ≅ freeY (f⁻¹(U₁⊓U₂))` (G1 + corepresentability)
— determined by ONE generator via `freeYonedaEquiv`; compute δ's value on it from the B2 oplax
formula (δ := homEquiv.symm (unit ⊗ₘ unit ≫ μ) with μ = tmul↦tmul) and match the canonical iso.
Object-chain endpoints already agree (G1 both upstairs and downstairs + `f⁻¹(U₁⊓U₂) = f⁻¹U₁ ⊓ f⁻¹U₂`).
Estimated: [G3-pre] one chunk (generator-chase with the new tools), [G3] one chunk (colimit-comparison).

## ★ G3-pre CLOSED (2026-07-10, session 5)

**`isIso_pullback_δ_freeYoneda` proven, axiom-clean** (`ef173267d`). δ of the doctrinal oplax
structure is an isomorphism on free-yoneda pairs at PRESHEAF level (no sheafification):
δ = (pullback-map of lattice-miracle ≪≫ pullbackFreeYonedaIso ≪≫ downstairs-lattice-miracle.symm
≪≫ tensorIso of pullbackFreeYonedaIso.symm's).hom, by adj'-homEquiv injectivity + evaluation on
the ONE generator of freeY(U₁ ⊓ U₂).

**Infrastructure landed (all sorry-free, generic small-sites unless noted):**
- `pullbackFreeYonedaIso φ X : (pullback φ).obj (freeY X) ≅ freeY (F X)` — EXPLICIT hom/inv via
  the two corepresentability homEquivs (uniqueUpToIso abandoned: its simps-internals are
  preimageIso-opaque); char lemma `homEquiv_pullbackFreeYonedaIso_hom_comp`.
- `corepresentableBy_homEquiv_app_generator`, `freeYonedaEquiv_apply`, `unit_app_freeYoneda`,
  `freeYonedaEquiv_unit_app`, `app_freeMk` (morphism-out-of-freeYoneda on ANY generator =
  restriction of generator image — the one compute rule), `freeObj_map_freeMk'`,
  `free_map_app_freeMk`, `tensorHom_app_tmul`, `freeYonedaTensorIso_inv_app_generator`.
- `pushforwardIsoFactored_hom_app_app` (rfl), `factoredAdjunction_unit_app_app` (rfl),
  `pushforwardFactored_μ_app_tmul` (**rfl!** — push₀-μ is Iso.refl + restrictScalars-μ is
  mapOfCompatibleSMul), `factoredUnit_app_freeMk` (small+CommRingCat section).
- Data upgrades: `pullbackOplaxMonoidal` (B2 as def), `freeTensorIso` + `IsIso (freeTensorDesc)`
  instance + `freeTensorDesc_app`, `freeYonedaTensorIso` (G1 as def), scheme bridge
  `schemeRingPresheafHom := whiskerRight f.c forget₂` (defeq-accepted; keeps `T ⋙ forget₂`
  clothing on BOTH pullback sides — Opens.map lives in ?F, not the ring presheaf).

**METHOD NOTES (fleet-grade, new):**
1. **The instances-transparency wart**: `X.sheaf.obj` (Sheaf = FullSubcategory projection) makes
   every scheme-level element-goal "not type-correct under instances transparency" — `rw`/kabstract
   ABORTS even on syntactically-present patterns. `simp only` also misses. **`erw` fires** — but
   ONLY cheap on FULLY-CONCRETE equations (zero metavariables, e.g. an instantiated `have`);
   erw with lemma-metas whnf-explodes scanning the pullback machinery.
2. **congrArg₂-assembly**: when even concrete-erw is risky, `refine Eq.trans (congrArg _
   (congrArg₂ (fun a b => a ⊗ₜ b) h₁ h₂)) ?_` rewrites under an application with NO goal
   scanning; terminal cross-defeq (push-map vs pb-map clothing + proof-irrelevant Opens homs)
   closed by the final `exact`'s single defeq check.
3. Expected-type-driven elaboration PINS `freeYonedaEquiv`'s implicit (M, X) at the WRONG side
   across pushforward-defeq — always pin `(X := F.obj U) (M := ...)` explicitly in cross-typed
   statements; for `Equiv.trans`-composites pin BOTH factors.
4. `Iso.trans_hom`/`mapIso_hom`/`homEquiv_naturality_left`/`ofNatIsoRight`-simps all fire as
   plain `rw` even on wart-y goals — the abort depends on the abstraction position.

**Chain: B1 ✓ B2 ✓ G1 ✓ G3-pre ✓ │ next: [G3-η] (unit ≅ freeY ⊤ + same chase), then [G3-TC]
(tensorRight preserves colimits), [G3-EXT] (abstract iso-at-colimit), [G3-P]/[G3-Q] (two passes),
[A] (ofOplaxMonoidal + functorMonoidalOfComp descent → nonempty_pullback_monoidal → Pic(f)).**

## ★★★ [D-PresPB′-general] FULLY DISCHARGED (2026-07-10, session 5 continuation)

**THE CHAIN IS COMPLETE — every leaf closed, sorry-free, axiom-clean:**
B1 ✓ B2 ✓ G1 ✓ G3-pre ✓ **G3-η ✓** (`isIso_pullback_η`: unit ≅ freeY(⊤) via `unitDesc`
universal-property + `Finsupp.uniqueLinearEquiv` componentwise; both sides of the chase = 1,
`map_one` closes) **G3-TC ✓** (`preservesColimitsOfShape_tensorRight/Left` — pointwise via
`evaluationJointlyReflectsColimits` + ModuleCat monoidal-closed; `_aux` size-u packagings)
**G3-EXT ✓** (`isIso_app_of_isColimit`) **G3 ✓** (`isIso_pullback_δ_of_freeYoneda` — GENERIC
two-pass extension: `isIso_app_of_isIso_app_freeYoneda` reusable core = coproduct layer over
`Elements` + cokernel-cofork layer; `δRightNat`/`δLeftNat` via `δ_natural_left/right.symm`;
scheme corollary `isIso_pullback_δ`) **A ✓**:
- `pullbackMonoidal f : (pullback (schemeRingPresheafHom f)).Monoidal` — **the presheaf
  pullback of a scheme morphism is MONOIDAL** (Monoidal.ofOplaxMonoidal; NO sheafification).
- `nonempty_sheafPullback_monoidal` (GENERIC descent, small sites + CommRingCat literal):
  presheaf-level monoidal ⟹ sheaf-level monoidal via `functorMonoidalOfComp` +
  `Lifting := ⟨sheafificationCompPullback ⟨φ₀⟩⟩`. KEY ENGINEERING: state over the
  PRESHEAF-level φ₀ and form ⟨φ₀⟩ internally — one consistent spelling kills the whnf
  storm; an explicit `letI : (toMonoidalCategory …R-side…).Monoidal := inferInstance` probe
  is needed (the comp-instance search stalls without it).
- `nonempty_pullback_monoidal f : Nonempty ((Modules.pullback f).Monoidal)` — the PAYOFF
  SORRY CLOSED (thin wrapper; the Modules.pullback-vs-literal cast is pure defeq).
- **`Pic.map (f : Y ⟶ X) : Pic X →* Pic Y`** — THE GME (2.16) PICARD FUNCTOR
  (`Units.map (Skeleton.monoidHom)`), axiom-clean. **P2 headline delivered.**
- Registered leaf `nonempty_sheafify_presheafPullback_tensor` RELOCATED PTM→PTG (zero
  consumers; PTG must import PTM — its instances are load-bearing — so downstream-only
  closure), respelled at clean clothing, closed from μIso. **PullbackTensorMonoidal.lean
  is now sorry-free.**

**REMAINING (1 sorry in the stream):** `nonempty_pullback_tensorObj` (InvertibleSheaf:165)
— cannot import PTG (cycle: PTG → PTM → InvertibleSheaf). Resolution designed: NEW file
`Picard/PullbackTensorObj.lean` importing {InvertibleSheaf, PTG}, relocate the statement
(zero consumers), assemble: `sheafificationCompPullback.app (M.val ⊗ N.val)` ≪≫
`mapIso μIso.symm` ≪≫ double-sheafification collapse (PTM's proven ι-route e-chain at
340-358 is the template for the last leg). Also [PIC-P2-CMP] can now consume the landed
owner `Picard/Dual.lean` (dual-sheaf infrastructure) — coordinate with p2.

Method notes: `Monoidal.ofOplaxMonoidal`/`CoreMonoidal.ofOplaxMonoidal` are the mathlib
packagers (Functor.lean:710/733); `Adjunction.corepresentableBy` exists (Basic.lean:318);
Sheaf fields are now `.obj`/`.cond`→`.property` (deprecation incoming), Hom field `.hom`;
legacy `ringCatSheaf.obj`-spelled statements elaborate their ⊗ at
`(sheafToPresheaf …).obj`-clothing where NO monoidal instance matches — respell, don't fight.
