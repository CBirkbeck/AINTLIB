# a5-P2 transport: prove hcart + hzero in curveAction_actionFamily

File: `/Users/mcu22seu/.claude5/jobs/dc627d4b/tmp/transp_agent.lean` — the statement + hmul are done; TWO `sorry`s remain (hcart, hzero). Make the whole file compile: NO errors, NO sorry, axiom-clean.

## Compile (standalone lean, NOT lake)
```
cd /Users/mcu22seu/Documents/GitHub/aintlib-modular-curves
timeout 500 env LEAN_PATH="$(~/.elan/bin/lake env printenv LEAN_PATH)" ~/.elan/bin/lean /Users/mcu22seu/.claude5/jobs/dc627d4b/tmp/transp_agent.lean 2>&1 | grep -iA4 "error" | head -30
```
You may put a COPY in the repo tree (e.g. `/Users/…/aintlib-modular-curves/_transp_scratch.lean`) to use lean-lsp MCP tools (lean_goal, lean_multi_attempt) — REMOVE it when done. Never put `2>/dev/null` next to lean.

## Setup
`act g := ((σ.pullbackChartAction σE hact.π_equivariant hŨs).transport e).hom g = e.inv ≫ (pcA.hom g) ≫ e.hom`, where `pcA := σ.pullbackChartAction σE hact.π_equivariant hŨs` (a `SchemeAction G (pullback C.π Ũ.ι)`), and `pcA.hom g = pullback.map C.π Ũ.ι C.π Ũ.ι (σE.hom g) ((σ.hom g).resLE Ũ Ũ _) (σ.hom g) _ _`.
The base ring is `R := Γ(X, Ũ)` with `MulSemiringAction G R := σ.gammaMulSemiringAction hŨs`.
CRUCIAL: `Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))` is DEFEQ to `specSMul g` (`AlgebraicGeometry.specSMul` def) — so the hcart/hzero base map is `specSMul g`; use `show … specSMul g …` or `SpecGroupAction`'s `specSMul` unfolds to it.

## hcart: `IsPullback (act g) (projModelπ W₀) (projModelπ W₀) (specSMul g)`
Square shape: `projModel W₀ --act g--> projModel W₀`, both legs `projModelπ W₀ : projModel W₀ ⟶ Spec R`, base `specSMul g`.

Two steps:
**(1) pcA.hom g is cartesian over the restricted base.** Prove:
`IsPullback (pcA.hom g) (pullback.snd C.π Ũ.ι) (pullback.snd C.π Ũ.ι) ((σ.hom g).resLE Ũ Ũ (hŨs.le_preimage g))`.
This is `IsCurveAction.cartesian g` (`IsPullback (σE.hom g) C.π C.π (σ.hom g)`) base-changed along `Ũ.ι`. Route: `pullback C.π Ũ.ι` sits in the pasting
`pullback C.π Ũ.ι --snd--> Ũ --Ũ.ι--> X` and `--fst--> C.E`. The map `pcA.hom g = pullback.map …` covers `(σE.hom g, resLE)` over `σ.hom g`. Use mathlib pasting (`IsPullback.paste_vert`/`paste_horiz`, `Mathlib/…/Pullback/Pasting.lean`, or `IsPullback.of_hasPullback` + `IsPullback.of_iso`): the base-change of `hact.cartesian g` (which is `IsPullback (σE.hom g) C.π C.π (σ.hom g)`) along `Ũ.ι : Ũ ⟶ X`. Concretely `(IsPullback.of_hasPullback C.π Ũ.ι)` gives `IsPullback (pullback.fst C.π Ũ.ι) (pullback.snd C.π Ũ.ι) C.π Ũ.ι`; paste with `hact.cartesian g` and use `resLE_comp_ι : (σ.hom g).resLE Ũ Ũ _ ≫ Ũ.ι = Ũ.ι ≫ σ.hom g` to identify the induced map with `pcA.hom g` (`pullback.map` characterised by `pullback.hom_ext` + `pullback.lift_fst/lift_snd`).

**(2) Transport by isos.** Apply `IsPullback.of_iso` to the step-(1) square with:
- `e₁ = e₂ = e₃ = e` (`pullback C.π Ũ.ι ≅ projModel W₀`), `e₄ = hŨa.isoSpec` (`Ũ ≅ Spec R`).
- The `fst'`/`snd'` compat: `projModelπ W₀ = e.inv ≫ (pullback.snd C.π Ũ.ι) ≫ hŨa.isoSpec.hom`, i.e. from `heπ` (`e.hom ≫ projModelπ W₀ = pullback.snd … ≫ isoSpec.hom`) rearranged with `e.inv`.
- The base compat: `specSMul g = isoSpec.inv ≫ (σ.hom g).resLE Ũ Ũ _ ≫ isoSpec.hom`, from `resLE_isoSpec_hom σ hŨs hŨa g` (`(σ.hom g).resLE ≫ isoSpec.hom = isoSpec.hom ≫ specSMul g`).
- `act g = e.inv ≫ pcA.hom g ≫ e.hom` matches `of_iso`'s transported `fst'` (with e₁=e₂=e).
Check `IsPullback.of_iso`'s exact hypotheses (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/CommSq.lean` — it takes e₁ e₂ e₃ e₄ and 4 compat equations `w₁ w₂ w₃ w₄` of the form `e₁.hom ≫ fst' = fst ≫ e₂.hom` etc.); supply each from heπ / resLE_isoSpec_hom / definitional (`act`, `transport_hom`).

## hzero: `projModelZero W₀ ≫ act g = specSMul g ≫ projModelZero W₀`
From `IsCurveAction.zero_equivariant g` (`C.zero ≫ σE.hom γ = σ.hom γ ≫ C.zero`) + the chart zero-compat `hez` + `act g = e.inv ≫ pcA.hom g ≫ e.hom`. Strategy: `projModelZero W₀ = (isoSpec.inv ≫ pullback.lift (Ũ.ι ≫ C.zero) (𝟙 _) _) ≫ e.hom` (that's `hez` backwards). Compose with `act g`, push through `pcA.hom g` (its action on the zero section via `pullback.lift`/`pullback.hom_ext` + `zero_equivariant` + `resLE`), and `resLE_isoSpec_hom`/`specSMul` for the base. Use `pullback.hom_ext`, `pullback.lift_fst/lift_snd`, `Scheme.Hom.resLE_comp_ι`, `gammaMulSemiringAction`/`specSMul` naturality. This is a morphism equation (not IsPullback) — likely a `pullback.hom_ext` + `cancel_mono`/`cancel_epi` grind.

## Relevant lemmas (all exist)
`SchemeAction.pullbackChartAction`, `SchemeAction.transport`, `SchemeAction.transport_hom`, `SchemeAction.pullbackChartAction`'s `hom` = `pullback.map …`; `IsCurveAction.cartesian`, `IsCurveAction.zero_equivariant`, `IsCurveAction.π_equivariant`; `resLE_isoSpec_hom σ hŨs hŨa g`; `specSMul` (= Spec.map(ofHom(toRingHom))) with `specSMul_mul`/`specSMul_one`; `Scheme.Hom.resLE_comp_ι`, `resLE_comp_resLE`; `IsPullback.of_iso`, `IsPullback.of_hasPullback`, `IsPullback.paste_vert`, `IsPullback.paste_horiz`; `pullback.map`, `pullback.lift_fst`, `pullback.lift_snd`, `pullback.hom_ext`, `pullback.map_fst`, `pullback.map_snd`.

Namespaces: file has `namespace ModularCurves.RouteA`, `open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve`, `open scoped Pointwise`. `IsCurveAction`/`resLE_isoSpec_hom`/`specSMul`/`gammaMulSemiringAction`/`pullbackChartAction` are all reachable.

## Report
When the file compiles clean (grep gives EMPTY), report the two proofs (the `intro g; …` bodies for hcart and hzero) verbatim. If stuck after real effort, report the exact remaining goal (from lean_goal) + what you tried.
