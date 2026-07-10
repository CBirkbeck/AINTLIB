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
