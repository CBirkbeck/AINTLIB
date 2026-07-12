# T-G4 `mulOver_assoc` transport — worked plan (c5β)

The last of the 4 Over-level group-axiom transports; NEW-CASCADE is parked on it.
Units + inverse are DONE (axiom-clean, committed e8bb22e9d / 74c6c48f3 / 63f87e656).

## Reduced goal (after `Over.OverMorphism.ext` + `simp only [Over.comp_left, mulOver_left,
## Over.whiskerRight_left, Over.whiskerLeft_left]`), at `W := universalWeierstrassLocU.map f`:

```
LHS.left = pullback.map (mo⊗mo).hom mo.hom mo.hom mo.hom  mulModelHom (𝟙 projModel) (𝟙 Spec R) ≫ mulModelHom
RHS.left = α.hom.left ≫ pullback.map mo.hom (mo⊗mo).hom mo.hom mo.hom  (𝟙 projModel) mulModelHom (𝟙 Spec R) ≫ mulModelHom
```
(`mo = modelOver W`; the ▷ whisker acts by `mulModelHom` on factor 1, id on factor 2;
the ◁ whisker acts id on factor 1, `mulModelHom` on factor 2; `α.hom.left` = pullback associator.)

## Transport = `isPullback_projModelBaseChangeOf … .hom_ext` on the codomain `projModel W`:

- **snd-leg (`≫ projModelπ W`)** — via `Over.w` on the two original Over morphisms
  `(mulOver ▷ mo) ≫ mulOver` and `α.hom ≫ (mo ◁ mulOver) ≫ mulOver` (both `⟶ mo`), exactly as in
  `mulOver_oneOver`/`invOver_mulOver`. EASY.

- **fst-leg (`≫ projModelBaseChangeOf`)** — the hard part. Both sides end `mulModelHom ≫ pBC`;
  push `hbc` (`mulModelHom ≫ pBC = pullbackMapBaseChangeOf ≫ mulModelHom_U`). Then need, with
  `X_triple : ((mo⊗mo)⊗mo).left ⟶ ((mo_U⊗mo_U)⊗mo_U).left` the triple base-change map:
    - `hnatL : (mulOver ▷ mo).left ≫ pullbackMapBaseChangeOf = X_triple ≫ (mulOver_U ▷ mo_U).left`
    - `hnatR : α.left ≫ (mo ◁ mulOver).left ≫ pullbackMapBaseChangeOf
                 = X_triple ≫ α_U.left ≫ (mo_U ◁ mulOver_U).left`
  then close by `raw` (atlas `mulOver_assoc_atlas`, `.left`):
    `(mulOver_U ▷ mo_U).left ≫ mulModelHom_U = α_U.left ≫ (mo_U ◁ mulOver_U).left ≫ mulModelHom_U`.

### `X_triple` construction
`(mo⊗mo)⊗mo).left = pullback (mo⊗mo).hom mo.hom`. So
`X_triple := pullback.map (mo⊗mo).hom mo.hom (mo_U⊗mo_U).hom mo_U.hom  X_double projModelBaseChangeOf (Spec.map f) _ _`
where `X_double := pullbackMapBaseChangeOf f uWLU (uWLU.map f) rfl` (the base change of `mo⊗mo`,
i.e. `pullback.map mo.hom mo.hom mo_U.hom mo_U.hom pBC pBC (Spec.map f)`).

### `hnatL` — ▷ whisker-BC
Mirror `mulOver_oneOver`'s hnat: `rw [Over.whiskerRight_left, pullbackMapBaseChangeOf, X_triple-def,
Over.whiskerRight_left]; simp only [modelOver_hom, modelOver_left, …]; erw [pullback.map_comp,
pullback.map_comp]; congr 1` — the three leg equalities: factor-1 leg = `mulModelHom` naturality
(itself an hbc/`mulModelHomBC_baseChange`-style fact — CHECK this closes; the whisker map's factor-1
map is `mulModelHom`, whose BC is hbc), factor-2 = id (`id_comp`/`comp_id`), base = `Spec.map f`.
NB the erw bridges the Over-vs-standard `HasPullback` instance diamond (proof irrelevance).

### `hnatR` — ◁ whisker-BC composed with associator-BC
`(mo ◁ mulOver).left ≫ pullbackMapBaseChangeOf = X_middle ≫ (mo_U ◁ mulOver_U).left` (◁ whisker-BC,
X_middle = base change of `mo⊗(mo⊗mo)`), then the **associator base-change naturality**
`α.left ≫ X_middle = X_triple ≫ α_U.left` (prove by `pullback.hom_ext` + the projection lemmas
`Over.associator_hom_left_fst / _snd_fst / _snd_snd` on both sides + the base-change map
projections `pullback.map ≫ fst/snd`). This associator-BC is the one genuinely new sub-lemma.

## Then of_eq (`subst h; exact of_map f`) + named (`… classifyRingHomU W … map_classifyRingHomU W`).
Estimated ~200–300 lines; the associator-BC sub-lemma is the crux.

## PROVEN sub-piece: e₁ (tensorObj base-change compat) — the X_triple first-leg obligation
`(mo⊗mo).hom ≫ Spec.map f = pullbackMapBaseChangeOf f uWLU (uWLU.map f) rfl ≫ (mo_U⊗mo_U).hom`
```lean
rw [Over.tensorObj_hom, Over.tensorObj_hom]; simp only [modelOver_hom]
have hmap : pullbackMapBaseChangeOf … ≫ pullback.fst (projModelπ uWLU) (projModelπ uWLU) =
    pullback.fst (projModelπ (uWLU.map f)) (projModelπ (uWLU.map f)) ≫ projModelBaseChangeOf … := by
  erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst]
have hw := (isPullback_projModelBaseChangeOf f uWLU (uWLU.map f) rfl).w
-- then a 5-step `calc` with explicit `Category.assoc _ _ _` / `.symm` terms (bare `rw [Category.assoc]`
-- does NOT match in these Scheme goals — use explicit terms or conv), steps: assoc → `rw [← hw]` →
-- assoc.symm → `rw [hmap]` → assoc.  (full proof landed green in tmp; ~30 lines)
```
e₂ is `mo.hom ≫ Spec.map f = projModelBaseChangeOf ≫ mo_U.hom` = `simp [modelOver_hom]; exact (…).w.symm`.
Remaining: X_triple (`set` with e₁,e₂), hnatL (mirror mulOver_oneOver hnat, leg-1=hbc), hnatR
(◁ whisker-BC + **associator-BC**: `pullback.hom_ext` + `Over.associator_hom_left_fst/_snd_fst/_snd_snd`
against the base-change-map projections), fst assembly, snd-leg `Over.w`, then of_eq+named.

## FINDING: hnatL (▷ whisker-BC) hits a `whnf` heartbeat timeout in the triple-tensor context
The map_comp+congr pattern that worked for the units' hnat times out at `whnf` (200k) when the
domain is the triple tensor `(mo⊗mo)⊗mo` (the tensor `⊗` structure maps force expensive whnf even
before the associator). e₁,e₂ (the X_triple obligations) are both green standalone. Next-pass fix
options (NO maxHeartbeats): (a) restructure hnatL to avoid whnf'ing the tensor `.hom` — pre-`simp
only [Over.tensorObj_hom]` to expose the pullback structure before map_comp; (b) do the fst-leg
directly by `pullback.hom_ext` on the codomain projModel rather than naming X_triple, reducing each
leg with `lift_fst`/`map`-`erw` (avoids constructing the triple pullback.map that triggers the whnf);
(c) prove hbc first as a top-level lemma so it isn't re-elaborated in the tensor context.
Likely (b) is cleanest — sidesteps X_triple entirely.
