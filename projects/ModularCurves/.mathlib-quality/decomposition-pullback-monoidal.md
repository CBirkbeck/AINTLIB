# Decomposition (adversarial): [PIC-P1b-MONO] — pullback commutes with the sheafified tensor

**Goal.** `nonempty_pullback_tensorObj` (`Picard/InvertibleSheaf.lean:158`):
```
theorem nonempty_pullback_tensorObj (f : Y ⟶ X) (M N : X.Modules) :
    Nonempty ((Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N))
```
with `tensorObj M N := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val)`
(`InvertibleSheaf.lean:68`). This is the last GAP-1 content gating the Pic group law; it is a
`Prop` (`Nonempty`-iso), so no `sorryAx` reaches any monoidal DATA (v10.8 discipline).

**Worker.** fable-PIC0. **Mode.** `/develop --decompose` (adversarial, planning-only — no tickets).
**Skeleton.** `ForMathlib/PullbackTensorMonoidal.lean` — builds clean, 2 sorries (the 2 new leaves).
`lake build ModularCurves.ForMathlib.PullbackTensorMonoidal` ✓ (sorry warnings only).

---

## Step 0 — Route decision (adversarial): D over M

Two candidate routes for "the pullback functor is strong monoidal for `tensorObj`".

### Route M — mates / doctrinal adjunction. **REJECTED.**
Idea: `f^* ⊣ f_*`; if `f_*` is lax monoidal then `f^*` is oplax via
`Adjunction.leftAdjointOplaxMonoidal` (`Mathlib/CategoryTheory/Monoidal/Functor.lean:1026`,
verified present), strong iff the oplax `δ` is iso.

**Attack (fatal):** `leftAdjointOplaxMonoidal` requires `MonoidalCategory` instances on **both**
`SheafOfModules` categories and `G.LaxMonoidal` for `G = f_*`. **mathlib has no
`SheafOfModules/Monoidal.lean`** (`ls Mathlib/Algebra/Category/ModuleCat/Sheaf/ | grep -i monoidal`
→ empty). The sheaf-level tensor in this project is the bespoke `tensorObj`, *not* a
`MonoidalCategory (SheafOfModules R)` instance. To run route M I would first have to build the
entire `MonoidalCategory X.Modules` — which is exactly the group-law layer that [PIC-P1b-MONO]
*gates*. Circular. Route M is out until that layer exists (and this leaf is a prerequisite for it,
not a consumer).

*(Correction of a prior board claim: my earlier "`CategoryTheory.Monoidal.Mates` is absent" was
WRONG. mathlib has `rightAdjointLaxMonoidal` (Functor.lean:908), `leftAdjointOplaxMonoidal`
(Functor.lean:1026), and `mateEquiv` (Bicategory/Adjunction/Mate.lean). Route M is not blocked by
missing mates infrastructure — it is blocked by the missing sheaf-level monoidal category.)*

### Route D — direct, at the sheaf level, via mathlib's `pullbackIso` / `sheafificationCompPullback`. **CHOSEN.**
`Scheme.Modules.pullback f = SheafOfModules.pullback f.toRingCatSheafHom`
(`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:182-183`), so mathlib's two structural isos apply
verbatim. Route D never needs a sheaf-level monoidal category — it works one level down, at
presheaves, and sheafifies at the end. Four pieces (3 pre-existing, 1 new).

---

## Step 1 — Prose proof (Route D)

Write `P := M.val`, `Q := N.val` (underlying presheaves), `sh_X`, `sh_Y` for the sheafifications
`PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)` resp. over `Y`, and
`f^*ᵖ := PresheafOfModules.pullback f.toRingCatSheafHom.hom` for the *presheaf* pullback.
By definition `tensorObj M N = sh_X(P ⊗ Q)` and `f^* := Modules.pullback f`.

**LHS.** `sheafificationCompPullback` is the natural iso `sh_X ⋙ f^* ≅ f^*ᵖ ⋙ sh_Y`. Evaluated at
`P ⊗ Q ∈ X.PresheafOfModules`:
```
f^*(tensorObj M N) = f^*(sh_X(P ⊗ Q)) ≅ sh_Y(f^*ᵖ(P ⊗ Q)).                        (L)
```

**RHS.** `pullbackIso` is `f^* ≅ forget ⋙ f^*ᵖ ⋙ sh_Y`. Evaluated at `M`, then taking underlying
presheaves (`.val = forget`):
```
(f^* M).val ≅ (sh_Y(f^*ᵖ P)).val,   likewise for N.
```
Hence, applying `sh_Y` to the tensor of these (functoriality of `sh_Y ∘ (- ⊗ -)`):
```
tensorObj (f^* M) (f^* N) = sh_Y((f^* M).val ⊗ (f^* N).val)
      ≅ sh_Y((sh_Y(f^*ᵖ P)).val ⊗ (sh_Y(f^*ᵖ Q)).val).                            (R)
```

**Collapse the double sheafification (D-Idem).** The sheafification units
`η : A ⟶ (sh_Y A).val` are locally bijective; `sheafificationW_tensorHom` says the tensor of two
locally bijective maps is locally bijective; and `sh_Y` inverts locally bijective maps. So
`sh_Y(η_{f^*ᵖP} ⊗ₘ η_{f^*ᵖQ})` is an iso:
```
sh_Y((sh_Y(f^*ᵖ P)).val ⊗ (sh_Y(f^*ᵖ Q)).val) ≅ sh_Y(f^*ᵖ P ⊗ f^*ᵖ Q).           (I)
```

**Pullback–tensor comparison, sheafified (D-PresPB′).** The natural comparison
`f^*ᵖ(P ⊗ Q) → f^*ᵖ P ⊗ f^*ᵖ Q` is a *stalkwise* isomorphism (stalk of an inverse image = stalk at
the image point; tensor commutes with stalks), hence locally bijective, hence inverted by `sh_Y`:
```
sh_Y(f^*ᵖ(P ⊗ Q)) ≅ sh_Y(f^*ᵖ P ⊗ f^*ᵖ Q).                                        (C)
```

**Assemble.** `(L) ≫ (C) ≫ (I)⁻¹ ≫ (R)⁻¹`:
```
f^*(M ⊗ N) ≅(L) sh_Y(f^*ᵖ(P⊗Q)) ≅(C) sh_Y(f^*ᵖP ⊗ f^*ᵖQ) ≅(I)⁻¹
   sh_Y((sh_Y f^*ᵖP).val ⊗ (sh_Y f^*ᵖQ).val) ≅(R)⁻¹  f^*M ⊗ f^*N.   ∎
```

---

## Step 2 — Ordered leaves

| # | Leaf | Source | Status |
|---|------|--------|--------|
| L | `sheafificationCompPullback` at `P⊗Q` | mathlib `PullbackContinuous.lean:118` | **have** |
| R/PBIso | `pullbackIso` at `M`,`N` + `.val` + `sh_Y`-functoriality | mathlib `PullbackContinuous.lean:106` | **have** |
| I / **D-Idem** | `sh(sh(A).val ⊗ sh(B).val) ≅ sh(A⊗B)` | this project GAP1-W-MONO (`sheafificationW_tensorHom`) + unit loc-bij | **new (leaf 1)** |
| C / **D-PresPB′** | `sh_Y(f^*ᵖ(P⊗Q)) ≅ sh_Y(f^*ᵖP ⊗ f^*ᵖQ)` | comparison is stalkwise iso ⇒ loc-bij | **new (leaf 2)** |
| A | assemble `(L)≫(C)≫(I)⁻¹≫(R)⁻¹` | — | glue |

Skeleton decls (both `sorry`, both typecheck):
`nonempty_sheafify_tensor_idem` (I), `nonempty_sheafify_presheafPullback_tensor` (C),
in `ForMathlib/PullbackTensorMonoidal.lean`, namespace `AlgebraicGeometry.Scheme.Modules`.

---

## Step 3 — Verbatim source quotes

**L — `sheafificationCompPullback`** (`.lake/…/ModuleCat/Sheaf/PullbackContinuous.lean:117-126`):
```
/-- The pullback of (pre)sheaves of modules commutes with the sheafification. -/
noncomputable def sheafificationCompPullback :
    PresheafOfModules.sheafification (𝟙 S.obj) ⋙ pullback.{v} φ ≅
      PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq …
```
Match: `S := X.ringCatSheaf`, `R := Y.ringCatSheaf`, `φ := f.toRingCatSheafHom`,
`pullback φ = Modules.pullback f`. Evaluate the functor iso at `P ⊗ Q`.

**R — `pullbackIso`** (`PullbackContinuous.lean:103-110`):
```
/-- The pullback functor on sheaves of modules can be described as a composition
of the forget functor to presheaves, the pullback on presheaves of modules, and
the sheafification functor. -/
noncomputable def pullbackIso :
    pullback.{v} φ ≅
      forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq …
```
Instances needed (`[(pushforward φ).IsRightAdjoint]`, `[HasWeakSheafify J AddCommGrpCat]`,
`[J.WEqualsLocallyBijective AddCommGrpCat]`) are all discharged in the scheme setting —
`Modules.pullback f` is a defined left adjoint (`Sheaf.lean:195-196`) and the Zariski site of a
scheme has weak sheafification (`InvertibleSheaf` already relies on both).

**I — GAP1-W-MONO** (`ForMathlib/SheafOfModulesMonoidal.lean:~630`, `sheafificationW_tensorHom`):
the tensor of two `sheafificationW` maps is `sheafificationW`; and
`sheafificationW_iff` (`:53`): `sheafificationW α f ↔ IsIso ((sheafification α).map f)`. So
`sh.map (η_A ⊗ₘ η_B)` is `IsIso` once `η_A, η_B ∈ sheafificationW`.

**C — presheaf pullback def** (`ModuleCat/Presheaf/Pullback.lean:44`):
```
noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint
```
— an *abstract* left adjoint (the inverse-image Kan extension + extend-scalars), **not** a
pointwise `extendScalars`; this is the crux the sheafified form (C) sidesteps.

**M (rejected)** — `Adjunction.leftAdjointOplaxMonoidal` (`Monoidal/Functor.lean:1024-1026`):
```
/-- The left adjoint of a lax monoidal functor is oplax monoidal. -/
def leftAdjointOplaxMonoidal : F.OplaxMonoidal where …
```
exists, but consumes `MonoidalCategory` instances on both sides — absent for `SheafOfModules`.

---

## Step 4 / 4.5 — Per-leaf provability + adversarial attacks (≥3 each)

### Leaf L (`sheafificationCompPullback`) — mathlib, **CONFIRMED**
1. *Exists at cited type?* Read verbatim, `PullbackContinuous.lean:117-126`. ✓
2. *Does `sh_X(P⊗Q) = tensorObj M N`?* `tensorObj M N := sh_X(M.val ⊗ N.val)` and `P=M.val`.
   Defeq — same modulo the sheafification instance-clothing seam already documented in
   `sheafifyValIso`'s docstring (`InvertibleSheaf.lean:91-101`); a bookkeeping cost, not a blocker. ✓
3. *Instances available?* `[(pushforward φ).IsRightAdjoint]` = `Sheaf.lean:196`; sheafification
   instances used throughout `InvertibleSheaf`. ✓
4. *Direction?* `sh_X ⋙ f^* ≅ f^*ᵖ ⋙ sh_Y` applied at `P⊗Q` gives `f^*(sh_X(P⊗Q))` on the left —
   exactly LHS. ✓ **Survives.**

### Leaf R (`pullbackIso` + `.val`) — mathlib, **CONFIRMED**
1. *Exists?* `PullbackContinuous.lean:103-110`. ✓
2. *`.val` = `forget`?* `forget S : SheafOfModules S ⥤ PresheafOfModules S.val`, `(forget S).obj M
   = M.val`; used throughout `InvertibleSheaf` (`tensorObj`, `sheafifyValIso`). ✓
3. *Does `sh_Y ∘ (- ⊗ -)` transport the two `.val` isos?* Yes — apply `sh_Y.mapIso` to the tensor
   of `(pullbackIso.app M).val`-isos in `X.PresheafOfModules` (monoidal, functorial). ✓
   **Survives** (hands the `forget∘sh` term to D-Idem).

### Leaf I / D-Idem — new, **CONFIRMED modulo one sub-anchor**
1. *Does `sheafificationW_tensorHom` yield an ISO, not just membership?* `sheafificationW_iff`:
   membership ↔ `IsIso (sh.map ·)`. `asIso` gives the iso. ✓
2. ⚠ *Are the units `η_A, η_B ∈ sheafificationW` (locally bijective)?* THE sub-anchor. mathlib has
   `toPresheaf_map_sheafificationAdjunction_unit_app` (`Sheafification.lean:145`) identifying the
   underlying map with the presheaf-level sheafification unit; that unit is locally bijective by the
   `WEqualsLocallyBijective` characterization. Exact lemma name (`isLocallyInjective/Surjective` of
   `toSheafify`, or via `J.W_of_isLocallyBijective` run backwards) **not yet located** — a
   five-method search at build time. Standard fact; **medium-high confidence.** *Survives, flagged.*
3. *Objects/direction?* `η_A : A ⟶ (sh A).val`, so `η_A ⊗ₘ η_B : A⊗B ⟶ (sh A).val ⊗ (sh B).val`,
   `sh.map` of it `: sh(A⊗B) ≅ sh((sh A).val ⊗ (sh B).val)` — matches the skeleton statement. ✓
4. *Is `⊗ₘ` of units the right map (vs some coherence-twisted map)?* `sheafificationW_tensorHom` is
   stated for `f ⊗ₘ g` exactly. ✓ **Survives.**

### Leaf C / D-PresPB′ — new, **REFINED from a refuted predecessor**
Predecessor leaf "D-PresPB: `f^*ᵖ` is strong monoidal at the presheaf level" — **REFUTED**:
1. *Is `f^*ᵖ` pointwise `extendScalars`?* NO — `pullback φ := (pushforward φ).leftAdjoint`
   (`Pullback.lean:44`) is an abstract left adjoint that includes an inverse-image **left Kan
   extension along the site functor F**, not just extend-scalars.
2. *Does that Kan extension commute with the presheaf tensor for general `f`?* NO. Inverse image of
   a tensor and tensor of inverse images differ at the presheaf level (they agree only on stalks).
   So the presheaf-level strong-monoidal statement is **false for general `f`.** ⇒ predecessor
   rejected; **fix the plan, not the leaf.**

Refined leaf C (sheafified comparison) then survives its own attacks:
1. *Is the comparison a stalkwise iso?* Stalk of inverse image at `y` = stalk of the source at
   `f(y)`; `(-)ₓ` is a monoidal (tensor-preserving) functor. Both sides have stalk
   `P_{f y} ⊗ Q_{f y}`; the comparison induces the identity on stalks. ✓
2. *Stalkwise iso ⇒ locally bijective ⇒ inverted by `sh_Y`?* Locally bijective ⇔ iso on the
   associated sheaf; that is exactly `sheafificationW` membership (`sheafificationW_iff_isLocallyBijective`,
   `SheafOfModulesMonoidal.lean:60`). So `sh_Y` inverts it. ✓
3. *Does the comparison map even EXIST to be sheafified?* It is the oplax `δ` of `f^*ᵖ`; its lax
   partner is `restrictScalars.LaxMonoidal` (`ModuleCat/Monoidal/Adjunction.lean`, verified) on the
   pushforward, transported by `leftAdjointOplaxMonoidal`. Constructing this presheaf-level oplax
   structure (`PresheafOfModules.pushforward.LaxMonoidal`, then `leftAdjointOplaxMonoidal`) is the
   **one genuine new build** — but it is a clean lift of a mathlib pointwise instance, on the model
   of `pushforward₀OfCommRingCat.Monoidal` (`PushforwardZeroMonoidal.lean:33`). Alternatively `δ`
   can be built by hand from the pullback adjunction unit/counit. **Medium confidence; the leaf is
   true, the labour is the oplax-structure lift.** *Survives.*
4. *Could the site functor for schemes be so wild that "stalkwise" fails?* No — the small Zariski
   site has enough points (stalks are conservative); inverse image is the standard `f⁻¹`. ✓

### Assembly A — **CONFIRMED**
1. *Do the objects line up across (L),(C),(I),(R)?* All four are isos between explicit `sh_Y(…)`
   objects; the shared vertices `sh_Y(f^*ᵖ(P⊗Q))` and `sh_Y(f^*ᵖP ⊗ f^*ᵖQ)` appear verbatim in the
   skeleton statements. ✓
2. *Directions composable?* Each is an iso; `.symm` on (I),(R) as written. ✓
3. *Hidden defeq mismatch `tensorObj` vs `sh_X(P⊗Q)`?* Same seam as Leaf L attack 2 — documented,
   discharged by `sheafifyValIso`-style nudging. ✓ **Survives.**

---

## Step 5 — Confidence gate

| Condition | Verdict |
|-----------|---------|
| Every leaf has a source locator | ✓ (mathlib file:line, or this project's `sheafificationW_tensorHom`) |
| Every leaf has a verbatim quote / Lean-↔-source paragraph | ✓ (Step 3) |
| No leaf requires substantial mathlib-absent infrastructure | ✓ — the one build (D-PresPB′ oplax lift) is a pointwise-instance lift, modelled on `pushforward₀OfCommRingCat.Monoidal` |
| No leaf is false / needs an unstated hypothesis | ✓ **after** refuting the presheaf-level predecessor and refining to the sheafified form |
| Skeleton typechecks (`lake build`, sorries only) | ✓ `ModularCurves.ForMathlib.PullbackTensorMonoidal` |
| Route decision recorded with the rejected route's fatal attack | ✓ (Step 0: route M ⟂ no `SheafOfModules` monoidal) |
| Adversarial attack log ≥3 per leaf/node, non-empty | ✓ (Step 4.5) |

**Two flagged residual risks** (neither a blocker):
- **D-Idem sub-anchor** — the exact mathlib "sheafification unit is locally bijective" lemma name is
  unlocated (a build-time search); the fact is standard.
- **D-PresPB′ labour** — building `PresheafOfModules.pushforward.LaxMonoidal` (⇒ oplax `δ` via
  `leftAdjointOplaxMonoidal`) is real work (~60–120 lines), though a mechanical pointwise lift.

---

## Feasibility assessment

**Feasible.** [PIC-P1b-MONO] decomposes into 4 leaves + glue, of which **2 are mathlib defs used
verbatim** (`sheafificationCompPullback`, `pullbackIso`), **1 is this project's already-built
GAP1-W-MONO** (`sheafificationW_tensorHom`, repackaged as D-Idem — needs only the standard
"unit is locally bijective" fact), and **1 is a single new build** (D-PresPB′ — the sheafified
pullback–tensor comparison, provable stalkwise, whose only real labour is lifting
`restrictScalars.LaxMonoidal` to `PresheafOfModules.pushforward` and transporting via
`leftAdjointOplaxMonoidal`). The adversarial pass earned its keep: it **refuted** the natural first
decomposition (presheaf-level strong monoidality of `f^*ᵖ`, *false* for general `f` because of the
inverse-image Kan extension) and **refined** it to the sheafified comparison, which is true and
provable by the project's existing `sheafificationW` machinery. Route M (mates) is correctly out —
not for want of mates lemmas (mathlib has them) but for want of a `MonoidalCategory (SheafOfModules R)`,
which this very leaf is a prerequisite for. **Recommendation: build Route D; sequence the leaves
(I) then (C) then assemble.** No statement change to `nonempty_pullback_tensorObj` is required —
the general-`f` form is provable as decomposed (specialisation to open immersions, which is all the
sole consumer `IsInvertible.tensorObj` uses, would make D-PresPB′ trivial but is *not needed*).

## DS-END0 / two-route note (v10.74 required line, carried forward)
This leaf sits on route (a) (build the Pic group law natively from `tensorObj` + these coherence
isos). It does **not** touch p2's Cartier-duality lane (route (b)); the v10.36 two-route edge —
"never build duality twice" — is unaffected: [PIC-P1b-MONO] is pure module-pullback compatibility,
consumed only by `IsInvertible.tensorObj` → the Pic group structure, not by any duality construction.

## Next step
Not a ticket (planning-only). When execution resumes under `/beastmode`: work leaf (I) D-Idem first
(smallest, unblocks the double-sheafification collapse), then (C) D-PresPB′ (the oplax lift), then
the ~20-line assembly `nonempty_pullback_tensorObj`. Board update: v10.78.
