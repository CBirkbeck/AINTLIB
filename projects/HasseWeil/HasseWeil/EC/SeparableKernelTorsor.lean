import HasseWeil.EC.IsogenyKernel
import HasseWeil.Curves.Differentials
import HasseWeil.EC.TranslationOrd

/-!
# Separable isogeny: `#ker φ = deg φ` over an algebraically closed field

The **embedding↔kernel torsor** (Silverman III.4.10c) for a separable endomorphism `φ` of an
elliptic curve: over `K̄`, the extension `K(E) / φ*K(E)` is Galois with group `ker φ` acting by
translation, so `#ker φ = #Gal(K(E)/φ*K(E)) = deg φ`.

**Why not the bare statement `sepDegree φ = #ker φ`.** The project's `Isogeny` bundles `pullback`
and `toAddMonoidHom` as *independent* fields (constructing one from the other is unfinished AG),
so `sepDegree`/`IsSeparable` (driven by `pullback`) and `kernel` (driven by `toAddMonoidHom`) are
a priori unrelated: a decoupled `{pullback := id, toAddMonoidHom := 0}` is "separable" with
`sepDegree = 1` yet `kernel = ⊤` (`Nat.card = 0` over `K̄`). So any `#ker = deg` statement needs a
**coherence** input tying the two fields — here, the two genuine-isogeny facts: the function-field
extension is `Normal`, and the translation action gives a bijection `ker φ ≃ Aut(K(E)/φ*K(E))`.
Both hold for a genuine separable isogeny over `K̄` and are discharged downstream for `φ = [ℓ]`.

The `1−π` case (`GapSpines.isogOneSub_negFrobenius_sepDegree_eq_card_kernel`) proves this directly,
but via geometric-Frobenius / `ker = ⊤` specifics that do **not** generalise; the Galois packaging
below is the general route (reviewer round 19, Q1).

Reference: Silverman III.4.10c, III.6.4.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **`#ker φ = deg φ` for a separable endomorphism**, via the Galois packaging of the
embedding↔kernel torsor (Silverman III.4.10c). Parametric on the two genuine-isogeny coherence
inputs over `K̄`:
* `h_normal` — the function-field extension `K(E) / φ*K(E)` is normal (with separability, this is
  `IsGalois`, giving `#Aut = deg φ` via the shipped `card_aut_eq_degree_of_isGalois`);
* `h_card` — the translation action `ker φ → Aut(K(E)/φ*K(E))` is a bijection on cardinalities,
  `#ker φ = #Aut`.

Both are discharged for `φ = [ℓ]` (`ℓ ≠ p`) in the torsion ticket; supplied here they give
`#ker φ = #Aut = deg φ`. -/
theorem card_kernel_eq_degree_of_separable_isogeny
    (φ : Isogeny W.toAffine W.toAffine) (hsep : φ.IsSeparable)
    (h_normal : letI := φ.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (h_card : Nat.card φ.kernel =
      Nat.card (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra)) :
    Nat.card φ.kernel = φ.degree := by
  rw [h_card]
  exact Isogeny.card_aut_eq_degree_of_isGalois φ (isogeny_finiteDimensional W φ)
    (Isogeny.isGalois_of_isSeparable_and_normal φ hsep h_normal)

/-- **`#ker φ = #Aut(K(E)/φ*K(E))`** from the forward/inverse translation witnesses (the
Galois-group ↔ kernel bijection, Silverman III.4.10a). The `forward` map is the kernel-translation
action (PointFix `kernelTranslateForwardAsAut`, already built given the covariance `hcov`); the
`inverse` map (`σ ↦ σ(P_gen)−P_gen ∈ ker`, with its constancy over `K̄`) plus the mutual-inverse
identities are the substantive remaining content. This discharges `h_card` of
`card_kernel_eq_degree_of_separable_isogeny`. (The PointFix scaffold for this is `[Fintype]`-scoped,
so we build the trivial cardinality bijection inline — no finiteness needed.) -/
theorem card_kernel_eq_card_aut_of_inverse_witnesses
    (φ : Isogeny W.toAffine W.toAffine)
    (forward : φ.kernel → (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra))
    (inverse : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) → φ.kernel)
    (h_left : Function.LeftInverse inverse forward)
    (h_right : Function.RightInverse inverse forward) :
    Nat.card φ.kernel =
      Nat.card (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) :=
  Nat.card_congr ⟨forward, inverse, h_left, h_right⟩

/-- **`#ker φ = deg φ` for a separable endomorphism over `K̄`, witness form** (Silverman
III.4.10c): the reviewer-endorsed general fibre-count, fully reduced to the PointFix
Galois-correspondence witnesses (`h_normal` + forward/inverse translation maps). At `φ = [ℓ]`,
`deg[ℓ] = ℓ²`, this gives `#E[ℓ] = ℓ²`. -/
theorem card_kernel_eq_degree_of_separable_of_witnesses
    (φ : Isogeny W.toAffine W.toAffine) (hsep : φ.IsSeparable)
    (h_normal : letI := φ.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (forward : φ.kernel → (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra))
    (inverse : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) → φ.kernel)
    (h_left : Function.LeftInverse inverse forward)
    (h_right : Function.RightInverse inverse forward) :
    Nat.card φ.kernel = φ.degree :=
  card_kernel_eq_degree_of_separable_isogeny W φ hsep h_normal
    (card_kernel_eq_card_aut_of_inverse_witnesses W φ forward inverse h_left h_right)

/-- **The forward witness, made concrete** (general, no `[Fintype]`): translation by a kernel point
`k`, promoted to a `φ*K(E)`-algebra automorphism of `K(E)` via the covariance hypothesis `hcov`
(`τ_k` fixes the pullback range, the function-field shadow of `φ ∘ (·+k) = φ` for `k ∈ ker φ`).
This supplies the `forward` argument of `card_kernel_eq_degree_of_separable_of_witnesses`, leaving
only `hcov`, the `inverse` map, the mutual-inverse identities, and `h_normal` to discharge for `[ℓ]`.
(PointFix's version is `[Fintype]`-scoped; this is the K̄ version.) -/
noncomputable def kernelTranslateForwardAut
    (φ : Isogeny W.toAffine W.toAffine)
    (hcov : ∀ k : φ.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z) :
    φ.kernel → (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) :=
  fun k =>
    letI := φ.toAlgebra
    AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W k.val).toRingEquiv)
      (fun r => hcov k r)

/-- **The forward kernel-translation map is injective.** Two kernel points giving the same
`φ*K(E)`-algebra automorphism of `K(E)` give the same translation `AlgEquiv` (the forward map is
literally `τ_{k.val}` recast as an `Aut`), and `translateAlgEquivOfPoint` is injective
(`translateAlgEquivOfPoint_injective`: distinct points give distinct translations).  Hence the
forward map is injective on `ker φ`. -/
theorem kernelTranslateForwardAut_injective
    (φ : Isogeny W.toAffine W.toAffine)
    (hcov : ∀ k : φ.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z) :
    Function.Injective (kernelTranslateForwardAut W φ hcov) := by
  intro k1 k2 h
  apply Subtype.ext
  apply translateAlgEquivOfPoint_injective W
  -- Equal `Aut`s ⟹ equal underlying functions ⟹ `τ_{k1.val} = τ_{k2.val}`.
  have hfun :
      (kernelTranslateForwardAut W φ hcov k1 :
        W.toAffine.FunctionField → W.toAffine.FunctionField) =
      kernelTranslateForwardAut W φ hcov k2 := by rw [h]
  exact AlgEquiv.ext (fun z => congrFun hfun z)

/-- **Finiteness of `ker φ` for any endomorphism isogeny over `K̄` (or any field), from the
kernel-translation covariance `hcov`.** The function-field extension `K(E) / φ*K(E)` is
finite-dimensional (`isogeny_finiteDimensional`, true for *any* isogeny — no separability needed),
so its automorphism group `Aut(K(E)/φ*K(E))` is a `Fintype`. The injective forward map
`kernelTranslateForwardAut` (needing only `hcov`) then embeds `ker φ` into this finite group, so
`ker φ` is finite.

This is the **trace-free / dual-free** route to kernel finiteness: it avoids the geometric
Verschiebung and the characteristic-polynomial relation `π + V = [t]` entirely (neither of which is
available over `K̄`), routing through the finite-dimensionality of the pullback field extension and
the faithfulness of the kernel-translation action (Silverman III.4.10a/c). -/
theorem finite_kernel_of_hcov
    (φ : Isogeny W.toAffine W.toAffine)
    (hcov : ∀ k : φ.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z) :
    Finite φ.kernel := by
  letI := φ.toAlgebra
  haveI := isogeny_finiteDimensional W φ
  haveI : Finite (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) :=
    Finite.of_fintype _
  exact Finite.of_injective _ (kernelTranslateForwardAut_injective W φ hcov)

/-! ## Phase 1 — the translation action on the generic point

The function-field translation `τ_k = translateAlgEquivOfPoint W k`, lifted to a map on
`(W_KE).Point` via `Affine.Point.map`, sends the generic point `P_gen` to `P_gen + (k lifted)`.
This is the point-level shadow of "translation by `k`", and the single substantive fact behind
both mutual-inverse identities (`h_left`, `h_right`) of the torsor. It combines the shipped
action-on-generators lemmas (`translateAlgHom_apply_x_gen` etc.) with the curve group-law identity
`genericPoint_add_liftSomePoint`. Axiom-clean. -/

/-- Action of `translateAlgEquivOfPoint W (.some xk yk h_ns)` on `x_gen`: it produces the
`x`-coordinate `translateX_xy` of the translate, in either the 2-torsion or non-2-torsion case. -/
theorem translateAlgEquivOfPoint_apply_x_gen_of_some
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (.some xk yk h_ns) (x_gen W) = translateX_xy W xk yk := by
  by_cases h2 : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h2]
    show translateAlgEquiv_of_2tor W xk yk h_ns h2 (x_gen W) = _
    unfold translateAlgEquiv_of_2tor
    rw [AlgEquiv.ofAlgHom_apply]
    exact translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h2
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h2]
    show translateAlgEquiv W xk yk h_ns h2 (x_gen W) = _
    unfold translateAlgEquiv
    rw [AlgEquiv.ofAlgHom_apply]
    exact translateAlgHom_apply_x_gen W xk yk h_ns h2

/-- Action of `translateAlgEquivOfPoint W (.some xk yk h_ns)` on `y_gen`: it produces the
`y`-coordinate `translateY_xy` of the translate. -/
theorem translateAlgEquivOfPoint_apply_y_gen_of_some
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (.some xk yk h_ns) (y_gen W) = translateY_xy W xk yk := by
  by_cases h2 : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h2]
    show translateAlgEquiv_of_2tor W xk yk h_ns h2 (y_gen W) = _
    unfold translateAlgEquiv_of_2tor
    rw [AlgEquiv.ofAlgHom_apply]
    exact translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h2
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h2]
    show translateAlgEquiv W xk yk h_ns h2 (y_gen W) = _
    unfold translateAlgEquiv
    rw [AlgEquiv.ofAlgHom_apply]
    exact translateAlgHom_apply_y_gen W xk yk h_ns h2

/-- **The translation action on the generic point** (Silverman III.4.2 / §III.5): for any
`k ∈ E(F)`, the function-field translation `τ_k = translateAlgEquivOfPoint W k`, lifted to
`(W_KE).Point` via `Affine.Point.map`, sends the generic point to `P_gen + (k lifted to K(E))`.
Case analysis on `k`: at `k = 0` the map is the identity (`map_id`); at `k = .some _ _ _` the
`Affine.Point.map` coordinates are `(τ_k x_gen, τ_k y_gen) = (translateX_xy, translateY_xy)`,
matching `genericPoint_add_liftSomePoint`. Axiom-clean. -/
theorem translateAlgEquivOfPoint_map_genericPoint (k : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W)
        (translateAlgEquivOfPoint W k).toAlgHom (genericPoint W) =
      genericPoint W + liftPointToKE W k := by
  rcases k with _ | ⟨xk, yk, h_ns⟩
  · rw [translateAlgEquivOfPoint_zero_toAlgHom]
    change _ = genericPoint W + liftPointToKE W (0 : W.toAffine.Point)
    rw [show liftPointToKE W (0 : W.toAffine.Point) = 0 from map_zero _, add_zero]
    rw [genericPoint_xOf_some]
    exact WeierstrassCurve.Affine.Point.map_id
      (Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W))
  · rw [liftPointToKE_some W xk yk h_ns]
    rw [genericPoint_add_liftSomePoint W xk yk h_ns]
    rw [genericPoint_xOf_some]
    refine (WeierstrassCurve.Affine.Point.map_some
      (f := (translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns)).toAlgHom)
      (generic_nonsingular W)).trans ?_
    congr 1
    · exact translateAlgEquivOfPoint_apply_x_gen_of_some W xk yk h_ns
    · exact translateAlgEquivOfPoint_apply_y_gen_of_some W xk yk h_ns

/-! ## Phase 2 — the inverse map from a descent witness, and the mutual-inverse identities

An automorphism `σ ∈ Aut(K(E)/φ*K(E))` acts on the generic point `P_gen ∈ (W_KE).Point` via
`Affine.Point.map` (restricting `σ` to its `F`-algebra structure). The inverse witness of the
torsor is `σ ↦ σ(P_gen) − P_gen`, which must be a *kernel point over `F`* — this descent +
kernel-membership is the one genuinely-geometric input, packaged as `hdesc` (Silverman III.4.10c:
the kernel is finite and `F`-rational, and the difference `σ(P_gen) − P_gen` lies in it). Given
`hdesc`, both `h_left` (`inverse (τ_k) = k`) and `h_right` (`τ_{inverse σ} = σ`) follow from the
Phase-1 action lemma plus `algEquiv_ext_x_y_gen` / injectivity of `liftPointToKE`. -/

/-- The action of `σ ∈ Aut(K(E)/φ*K(E))` on the generic point, as a point of `(W_KE).Point`:
`Affine.Point.map` of the `F`-algebra restriction of `σ`, applied to `P_gen`. -/
noncomputable def genericPointAct (φ : Isogeny W.toAffine W.toAffine)
    (σ : @AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) :
    (W_KE W).toAffine.Point :=
  letI := φ.toAlgebra
  WeierstrassCurve.Affine.Point.map (W' := W) (σ.toAlgHom.restrictScalars F) (genericPoint W)

/-- The σ-action on the generic point in coordinates: `genericPointAct φ σ = (σ x_gen, σ y_gen)`.
Direct from `Affine.Point.map_some` applied to `genericPoint = some x_gen y_gen _`. -/
theorem genericPointAct_eq_some (φ : Isogeny W.toAffine W.toAffine)
    (σ : @AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) :
    letI := φ.toAlgebra
    genericPointAct W φ σ =
      Affine.Point.some (σ (x_gen W)) (σ (y_gen W))
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (σ.toAlgHom.restrictScalars F).injective (x_gen W) (y_gen W)).mpr
            (generic_nonsingular W)) := by
  letI := φ.toAlgebra
  unfold genericPointAct
  rw [genericPoint_xOf_some]
  exact WeierstrassCurve.Affine.Point.map_some
    (f := σ.toAlgHom.restrictScalars F) (generic_nonsingular W)

/-- **σ-equivariance brick — the kernel membership of `σ(P_gen) − P_gen` over `K(E)`.** Let `g`
be the geometric action of `φ` on `(W_KE).Point` (the witness of `IsGenuineWith φ g`, here
unpacked as `g(P_gen) = (φ*x_gen, φ*y_gen)`). If `g` is σ-equivariant — `g ∘ (Point.map σ) =
(Point.map σ) ∘ g`, the `hequiv` hypothesis — then `g(σ(P_gen)) = g(P_gen)`, i.e.
`σ(P_gen) − P_gen ∈ ker g`. This is the function-field-level half of the crux (Silverman
III.4.10c): the fibre `σ(P_gen) − P_gen` is killed by `φ`, because `σ` fixes the pullback range
`φ*K(E) ∋ φ*x_gen, φ*y_gen` (`σ.commutes`). It is the φ-agnostic generalisation of GapSpines'
`emb_le_card_kernel` membership argument, dropping the Frobenius/`ker = ⊤` route. The *only*
content left for the full `hdesc` of `card_kernel_eq_degree_of_separable_concrete` is then the
descent of this `ker g` element from `K(E)` to an `F`-rational `ker φ` point (the `toPointMap`
base-change square G-004 + descent lemma G-005 of `Curves/CurveMapBaseChange.lean`). Axiom-clean. -/
theorem genericPointAct_mem_ker_g (φ : Isogeny W.toAffine W.toAffine)
    (g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (X Y : W.toAffine.FunctionField) (hns : (W_KE W).toAffine.Nonsingular X Y)
    (hgP : g (genericPoint W) = Affine.Point.some X Y hns)
    (hX : X = φ.pullback (x_gen W)) (hY : Y = φ.pullback (y_gen W))
    (σ : @AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra)
    (hequiv : g (genericPointAct W φ σ) =
      WeierstrassCurve.Affine.Point.map (W' := W)
        (letI := φ.toAlgebra; σ.toAlgHom.restrictScalars F) (g (genericPoint W))) :
    g (genericPointAct W φ σ) = g (genericPoint W) := by
  letI := φ.toAlgebra
  rw [hequiv, hgP]
  refine (WeierstrassCurve.Affine.Point.map_some (f := σ.toAlgHom.restrictScalars F) hns).trans ?_
  -- `σ` fixes the pullback range: `σ X = σ (φ*x_gen) = φ*x_gen = X`, likewise for `Y`.
  have hσX : (σ.toAlgHom.restrictScalars F) X = X := by rw [hX]; exact σ.commutes (x_gen W)
  have hσY : (σ.toAlgHom.restrictScalars F) Y = Y := by rw [hY]; exact σ.commutes (y_gen W)
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hσX, hσY⟩

/-- The forward map sends `k` to the translation `τ_k`, whose action on the generic point is
`P_gen + (k lifted)` (Phase-1 master lemma): `genericPointAct (forward k) = P_gen + lift k`. The
forward map's underlying `F`-algebra automorphism is *definitionally* `translateAlgEquivOfPoint W
k.val`, so this is the Phase-1 lemma after identifying the two algebra homs. -/
theorem genericPointAct_kernelTranslateForwardAut (φ : Isogeny W.toAffine W.toAffine)
    (hcov : ∀ k : φ.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z)
    (k : φ.kernel) :
    genericPointAct W φ (kernelTranslateForwardAut W φ hcov k) =
      genericPoint W + liftPointToKE W k.val := by
  letI := φ.toAlgebra
  unfold genericPointAct kernelTranslateForwardAut
  have hAlgHom : ((AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W k.val).toRingEquiv)
        (fun r => hcov k r)).toAlgHom.restrictScalars F) =
      (translateAlgEquivOfPoint W k.val).toAlgHom := by
    apply AlgHom.ext; intro z; rfl
  rw [hAlgHom]
  exact translateAlgEquivOfPoint_map_genericPoint W k.val

/-- **`#ker φ = deg φ` for a separable endomorphism over `K̄`, concrete form** (Silverman
III.4.10c). The `forward` witness is the concrete translation map `kernelTranslateForwardAut`
(needing the covariance `hcov`); the `inverse` witness `σ ↦ σ(P_gen) − P_gen` and its
kernel-membership + descent to `F` are supplied by the single geometric hypothesis `hdesc` (the
generic-point translation torsor: every fibre `σ(P_gen) − P_gen` is an `F`-rational kernel point).
The two mutual-inverse identities are then discharged here from the Phase-1 action lemma:

* `h_left` (`inverse (τ_k) = k`): `lift (inverse τ_k) = τ_k(P_gen) − P_gen = (P_gen + lift k) −
  P_gen = lift k`, so `inverse τ_k = k` by injectivity of `liftPointToKE`;
* `h_right` (`τ_{inverse σ} = σ`): `τ_{inverse σ}(P_gen) = P_gen + lift (inverse σ) = σ(P_gen)`,
  so `τ_{inverse σ}` and `σ` agree on `x_gen, y_gen`, hence are equal by `algEquiv_ext_x_y_gen`.

This discharges the `forward`/`inverse`/`h_left`/`h_right` witnesses of
`card_kernel_eq_degree_of_separable_of_witnesses`, leaving only `hcov`, `h_normal`, and `hdesc`
as parametric inputs (the genuine-isogeny coherence facts, discharged downstream for `[ℓ]`). -/
theorem card_kernel_eq_degree_of_separable_concrete
    (φ : Isogeny W.toAffine W.toAffine) (hsep : φ.IsSeparable)
    (hcov : ∀ k : φ.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z)
    (h_normal : letI := φ.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ φ.kernel ∧
        liftPointToKE W k = genericPointAct W φ σ - genericPoint W) :
    Nat.card φ.kernel = φ.degree := by
  -- The inverse witness: pick the descended kernel point from `hdesc`.
  set inverse : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra) → φ.kernel :=
    fun σ => ⟨(hdesc σ).choose, (hdesc σ).choose_spec.1⟩ with hinv_def
  set forward := kernelTranslateForwardAut W φ hcov with hfwd_def
  -- Defining property of `inverse`: `lift (inverse σ).val = σ(P_gen) − P_gen`.
  have hinv_spec : ∀ σ, liftPointToKE W (inverse σ).val =
      genericPointAct W φ σ - genericPoint W :=
    fun σ => (hdesc σ).choose_spec.2
  -- `liftPointToKE` is injective.
  have hlift_inj : Function.Injective (liftPointToKE W) := by
    unfold liftPointToKE
    exact WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId F W.toAffine.FunctionField)
  -- `h_left`: inverse (forward k) = k.
  have h_left : Function.LeftInverse inverse forward := by
    intro k
    apply Subtype.ext
    apply hlift_inj
    rw [hinv_spec (forward k), hfwd_def, genericPointAct_kernelTranslateForwardAut W φ hcov k]
    -- (P_gen + lift k.val) − P_gen = lift k.val
    rw [add_comm, add_sub_cancel_right]
  -- `h_right`: forward (inverse σ) = σ.
  have h_right : Function.RightInverse inverse forward := by
    intro σ
    letI := φ.toAlgebra
    -- `forward (inverse σ)` acts on `P_gen` as `P_gen + lift (inverse σ).val = σ(P_gen)`.
    have hact : genericPointAct W φ (forward (inverse σ)) = genericPointAct W φ σ := by
      rw [hfwd_def, genericPointAct_kernelTranslateForwardAut W φ hcov (inverse σ)]
      rw [hinv_spec σ, add_comm, sub_add_cancel]
    -- Coordinate agreement on `x_gen`, `y_gen` (read off via `genericPointAct_eq_some`).
    rw [genericPointAct_eq_some W φ (forward (inverse σ)),
      genericPointAct_eq_some W φ σ] at hact
    have hcoords := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hact
    -- The two `Aut`-equivs agree as `F`-algHoms on the generators ⟹ equal pointwise.
    have hcoeq : ((forward (inverse σ)).toAlgHom.restrictScalars F) =
        (σ.toAlgHom.restrictScalars F) :=
      algHom_ext_x_y_gen W hcoords.1 hcoords.2
    refine AlgEquiv.ext fun z => ?_
    exact DFunLike.congr_fun hcoeq z
  rw [card_kernel_eq_degree_of_separable_of_witnesses W φ hsep h_normal forward inverse
    h_left h_right]

end HasseWeil
