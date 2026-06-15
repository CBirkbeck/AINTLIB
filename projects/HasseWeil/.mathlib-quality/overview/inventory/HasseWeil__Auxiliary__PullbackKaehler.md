# Inventory: ./HasseWeil/Auxiliary/PullbackKaehler.lean

**File summary**: 237 lines. Defines `AlgHom.pullbackKaehler`, the additive endomorphism of Kähler differentials `Ω[S⁄R]` induced by an R-algebra endomorphism `f : S →ₐ[R] S`, characterized by `f*(D x) = D(f x)`. Uses a twisted-module wrapper to work around typeclass conflicts. No sorries, no maxHeartbeats overrides.

---

## Namespace `AlgHom`

### `structure TwistedKaehler`
- **Type**: `(f : S →ₐ[R] S) → Type*`; a single-field wrapper around `Ω[S⁄R]`, field `out : Ω[S⁄R]`
- **What**: A wrapper type definitionally equal to `Ω[S⁄R]` but meant to carry a twisted `S`-module structure (where `s ∈ S` acts via `f s`), preventing conflict with the global `Module S Ω[S⁄R]` instance.
- **How**: Pure structure definition; no proof content.
- **Hypotheses**: `R`, `S` are commutative rings, `S` is an `R`-algebra.
- **Uses from project**: none
- **Used by**: `derivationCompHom`, `pullbackKaehler`, and most declarations in the `TwistedKaehler` namespace
- **Visibility**: public
- **Lines**: 48–52, definition only
- **Notes**: None

---

### `theorem TwistedKaehler.ext`
- **Type**: `{x y : TwistedKaehler f} → x.out = y.out → x = y`
- **What**: Extensionality for `TwistedKaehler`: two elements are equal iff their underlying `out` fields are equal.
- **How**: `cases x; cases y; congr` — standard single-field structure extensionality.
- **Hypotheses**: None beyond the structure setup.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.instModule`, `TwistedKaehler.instSMulR`, `Module R (TwistedKaehler f)`, `IsScalarTower`, `derivationCompHom`
- **Visibility**: public (`@[ext]`)
- **Lines**: 59–61, ~2 lines
- **Notes**: None

---

### `noncomputable instance : Zero (TwistedKaehler f)`
- **Type**: `Zero (TwistedKaehler f)`
- **What**: Zero element: wraps `(0 : Ω[S⁄R])`.
- **How**: Anonymous constructor `⟨⟨0⟩⟩`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public
- **Lines**: 62, 1 line
- **Notes**: None

---

### `noncomputable instance : Add (TwistedKaehler f)`
- **Type**: `Add (TwistedKaehler f)`
- **What**: Pointwise addition via the underlying `out` field.
- **How**: Anonymous constructor.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public
- **Lines**: 63, 1 line
- **Notes**: None

---

### `noncomputable instance : Neg (TwistedKaehler f)`
- **Type**: `Neg (TwistedKaehler f)`
- **What**: Negation via the underlying `out` field.
- **How**: Anonymous constructor.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public
- **Lines**: 64, 1 line
- **Notes**: None

---

### `noncomputable instance : Sub (TwistedKaehler f)`
- **Type**: `Sub (TwistedKaehler f)`
- **What**: Subtraction via the underlying `out` field.
- **How**: Anonymous constructor.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public
- **Lines**: 65, 1 line
- **Notes**: None

---

### `theorem TwistedKaehler.out_zero`
- **Type**: `(0 : TwistedKaehler f).out = 0`
- **What**: Simp lemma: the `out` of zero is zero.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.instModule`, `Module R (TwistedKaehler f)`
- **Visibility**: public (`@[simp]`)
- **Lines**: 67, 1 line
- **Notes**: None

---

### `theorem TwistedKaehler.out_add`
- **Type**: `(x y : TwistedKaehler f) → (x + y).out = x.out + y.out`
- **What**: Simp lemma: `out` distributes over addition.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`, `derivationCompHom`
- **Visibility**: public (`@[simp]`)
- **Lines**: 68, 1 line
- **Notes**: None

---

### `theorem TwistedKaehler.out_neg`
- **Type**: `(x : TwistedKaehler f) → (-x).out = -x.out`
- **What**: Simp lemma: `out` commutes with negation.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public (`@[simp]`)
- **Lines**: 69, 1 line
- **Notes**: None

---

### `theorem TwistedKaehler.out_sub`
- **Type**: `(x y : TwistedKaehler f) → (x - y).out = x.out - y.out`
- **What**: Simp lemma: `out` distributes over subtraction.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `TwistedKaehler.AddCommGroup`
- **Visibility**: public (`@[simp]`)
- **Lines**: 70, 1 line
- **Notes**: None

---

### `noncomputable instance : AddCommGroup (TwistedKaehler f)`
- **Type**: `AddCommGroup (TwistedKaehler f)`
- **What**: The wrapper type inherits an abelian group structure from `Ω[S⁄R]`.
- **How**: Each axiom discharged by `ext; simp [...]` using the `out_*` simp lemmas and the corresponding axiom of `Ω[S⁄R]`. Uses `zsmulRec` and `nsmulRec` for the derived `ℤ`/`ℕ` scalar actions.
- **Hypotheses**: None.
- **Uses from project**: `out_add`, `out_neg`, `out_sub`, `out_zero`
- **Used by**: `instModule`, `pullbackKaehler`, `derivationCompHom`
- **Visibility**: public
- **Lines**: 72–81, ~9 lines
- **Notes**: None

---

### `noncomputable instance TwistedKaehler.instSMul : SMul S (TwistedKaehler f)`
- **Type**: `SMul S (TwistedKaehler f)` where `s • x := ⟨f s • x.out⟩`
- **What**: The twisted `S`-scalar action: `s` acts as `f s` on the underlying differential.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `out_smul_S`, `instModule`, `IsScalarTower`, `derivationCompHom`
- **Visibility**: public (named instance)
- **Lines**: 83–85, 3 lines
- **Notes**: None

---

### `theorem TwistedKaehler.out_smul_S`
- **Type**: `(s : S) (x : TwistedKaehler f) → (s • x).out = f s • x.out`
- **What**: Simp lemma unfolding the twisted `S`-action on `out`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `instModule`, `IsScalarTower`, `derivationCompHom`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
- **Visibility**: public (`@[simp]`)
- **Lines**: 86–87, 2 lines
- **Notes**: None

---

### `noncomputable instance TwistedKaehler.instModule : Module S (TwistedKaehler f)`
- **Type**: `Module S (TwistedKaehler f)` (twisted via `f`)
- **What**: The twisted `S`-module structure: the `S`-module axioms hold because `f` is a ring homomorphism (so `f(st)=f(s)f(t)`, `f(1)=1`, etc.).
- **How**: Each axiom uses `ext; simp [out_smul_S, ...]` plus `map_mul`, `map_one`, `map_add`, `map_zero` for `f`, and `mul_smul`, `smul_add`, `add_smul` for `Ω[S⁄R]`.
- **Hypotheses**: None.
- **Uses from project**: `ext` (via `ext`), `out_smul_S`
- **Used by**: `derivationCompHom` (needs `Module S (TwistedKaehler f)` to define an `S`-linear lift)
- **Visibility**: public (named instance)
- **Lines**: 90–97, ~7 lines
- **Notes**: None

---

### `noncomputable instance TwistedKaehler.instSMulR : SMul R (TwistedKaehler f)`
- **Type**: `SMul R (TwistedKaehler f)` where `r • x := ⟨r • x.out⟩`
- **What**: The `R`-scalar action on the wrapper, lifting the standard `R`-action on `Ω[S⁄R]`.
- **How**: Direct definition.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `out_smul_R`, `Module R (TwistedKaehler f)`, `IsScalarTower`
- **Visibility**: public (named instance)
- **Lines**: 99–100, 2 lines
- **Notes**: None

---

### `theorem TwistedKaehler.out_smul_R`
- **Type**: `(r : R) (x : TwistedKaehler f) → (r • x : TwistedKaehler f).out = r • x.out`
- **What**: Simp lemma unfolding the `R`-action on `out`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: `Module R (TwistedKaehler f)`, `pullbackKaehler_smul_R`
- **Visibility**: public (`@[simp]`)
- **Lines**: 102–103, 2 lines
- **Notes**: None

---

### `noncomputable instance : Module R (TwistedKaehler f)`
- **Type**: `Module R (TwistedKaehler f)`
- **What**: The `R`-module structure on the wrapper, matching the standard `R`-action on `Ω[S⁄R]`.
- **How**: Each axiom uses `ext; simp [out_smul_R, ...]` plus the corresponding `Ω[S⁄R]` axioms.
- **Hypotheses**: None.
- **Uses from project**: `out_smul_R`
- **Used by**: `IsScalarTower`
- **Visibility**: public
- **Lines**: 105–111, ~6 lines
- **Notes**: None

---

### `instance : IsScalarTower R S (TwistedKaehler f)`
- **Type**: `IsScalarTower R S (TwistedKaehler f)`
- **What**: The scalar tower `R → S → TwistedKaehler f` is compatible: `(r • s) •_twisted ω = r • (s •_twisted ω)`.
- **How**: Reduces to `f(r • s) • ω.out = r • (f s • ω.out)`, then uses `map_smul` (f is R-linear) and `smul_assoc` on `Ω[S⁄R]`.
- **Hypotheses**: None.
- **Uses from project**: `ext`, `out_smul_S`, `out_smul_R`
- **Used by**: `derivationCompHom` (needed for the derivation's `map_smul'` field and for `liftKaehlerDifferential` to be S-linear in the twisted sense)
- **Visibility**: public
- **Lines**: 114–118, ~5 lines
- **Notes**: None

---

### `noncomputable def derivationCompHom`
- **Type**: `(f : S →ₐ[R] S) → Derivation R S (TwistedKaehler f)`
- **What**: The composition `x ↦ D(f x)` (landing in `TwistedKaehler f`) is an `R`-derivation from `S`. The twisted module structure is precisely what makes the Leibniz rule `D(f(xy)) = f(x)·D(f(y)) + f(y)·D(f(x))` hold with the twisted scalar actions.
- **How**: Constructs the derivation explicitly. The `leibniz'` field uses `map_mul` for `f`, `Derivation.leibniz` for `D`, and unfolds the twisted `S`-action via `out_smul_S`, `out_add`.
- **Hypotheses**: None.
- **Uses from project**: `TwistedKaehler.out_add`, `TwistedKaehler.out_smul_S`
- **Used by**: `pullbackKaehler`, `pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`
- **Visibility**: public
- **Lines**: 124–142, ~19 lines
- **Notes**: None

---

### `noncomputable def pullbackKaehler`
- **Type**: `(f : S →ₐ[R] S) → Ω[S⁄R] →+ Ω[S⁄R]`
- **What**: The additive endomorphism of `Ω[S⁄R]` induced by `f`, defined as the composite: lift `derivationCompHom f` via the universal property of Kähler differentials (`liftKaehlerDifferential`) to get an `S`-linear map `Ω[S⁄R] →ₗ[S] TwistedKaehler f`, then project via `.out`.
- **How**: Applies `Derivation.liftKaehlerDifferential` to `derivationCompHom f` (universal property of `Ω[S⁄R]`), then wraps the result as an `AddMonoidHom` by extracting `.out`.
- **Hypotheses**: None.
- **Uses from project**: `derivationCompHom`
- **Used by**: `pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_id`, `pullbackKaehler_comp`
- **Visibility**: public
- **Lines**: 146–152, ~7 lines
- **Notes**: None

---

### `theorem pullbackKaehler_D`
- **Type**: `(f : S →ₐ[R] S) (x : S) → f.pullbackKaehler (D R S x) = D R S (f x)`
- **What**: The defining property: the pullback of `D x` is `D(f x)`.
- **How**: Unfolds to `derivationCompHom.liftKaehlerDifferential` applied to `D x`, then uses `Derivation.liftKaehlerDifferential_comp_D` (the universal property equation) and `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `derivationCompHom`, `pullbackKaehler`
- **Used by**: `pullbackKaehler_id`, `pullbackKaehler_comp`
- **Visibility**: public (`@[simp]`)
- **Lines**: 155–162, ~7 lines
- **Notes**: None

---

### `theorem pullbackKaehler_smul_R`
- **Type**: `(f : S →ₐ[R] S) (r : R) (ω : Ω[S⁄R]) → f.pullbackKaehler (r • ω) = r • f.pullbackKaehler ω`
- **What**: The pullback is `R`-linear: it commutes with the base ring scalar action.
- **How**: The lifted map is `S`-linear in the twisted module; the scalar tower `R → S → TwistedKaehler f` means `S`-linearity implies `R`-linearity, invoked via `LinearMap.map_smul_of_tower`.
- **Hypotheses**: None.
- **Uses from project**: `derivationCompHom`, `pullbackKaehler`, `TwistedKaehler.out_smul_R`
- **Used by**: none in file (public API)
- **Visibility**: public
- **Lines**: 165–172, ~7 lines
- **Notes**: None

---

### `theorem pullbackKaehler_smul_S`
- **Type**: `(f : S →ₐ[R] S) (s : S) (ω : Ω[S⁄R]) → f.pullbackKaehler (s • ω) = f s • f.pullbackKaehler ω`
- **What**: The pullback is `f`-semilinear: pulling out an `S`-scalar `s` transforms it to `f s`.
- **How**: The lifted map is `S`-linear in the twisted structure, so `lift(s • ω) = s •_twisted lift(ω)`, whose `.out` is `f s • (lift ω).out` by definition of the twisted action. Uses `LinearMap.map_smul` and `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `derivationCompHom`, `pullbackKaehler`, `TwistedKaehler.out_smul_S`
- **Used by**: `pullbackKaehler_id`, `pullbackKaehler_comp`
- **Visibility**: public
- **Lines**: 175–181, ~7 lines
- **Notes**: None

---

### `private theorem ext_of_D`
- **Type**: `{f₁ f₂ : Ω[S⁄R] →+Ω[S⁄R]} → (∀ s ω, f₁ ω = f₂ ω → f₁ (s•ω) = f₂ (s•ω)) → (∀ x, f₁ (D R S x) = f₂ (D R S x)) → f₁ = f₂`
- **What**: Extensionality for `AddMonoidHom`s on `Ω[S⁄R]`: two such maps agreeing on all `D x` and compatible with `S`-smul (inductively) are equal.
- **How**: Uses `KaehlerDifferential.span_range_derivation` (which says `Ω[S⁄R]` is spanned by `{D x}` as an `S`-module) plus `Submodule.span_induction` to reduce to the generators.
- **Hypotheses**: None (private helper).
- **Uses from project**: none
- **Used by**: `pullbackKaehler_id`, `pullbackKaehler_comp`
- **Visibility**: private
- **Lines**: 185–201, ~17 lines
- **Notes**: None

---

### `theorem pullbackKaehler_id`
- **Type**: `(AlgHom.id R S).pullbackKaehler = AddMonoidHom.id _`
- **What**: The pullback along the identity algebra endomorphism is the identity map on `Ω[S⁄R]`.
- **How**: Applies `ext_of_D`. On generators `D x`: uses `pullbackKaehler_D` and `AlgHom.id` (so `D(id x) = D x`). For the smul step: uses `pullbackKaehler_smul_S` and the inductive hypothesis.
- **Hypotheses**: None.
- **Uses from project**: `ext_of_D`, `pullbackKaehler_smul_S`, `pullbackKaehler_D`
- **Used by**: none in file (public API)
- **Visibility**: public (`@[simp]`)
- **Lines**: 205–214, ~10 lines
- **Notes**: None

---

### `theorem pullbackKaehler_comp`
- **Type**: `(f g : S →ₐ[R] S) → (f.comp g).pullbackKaehler = f.pullbackKaehler.comp g.pullbackKaehler`
- **What**: Contravariant functoriality: the pullback of a composition is the composition of pullbacks (in the same order, since `comp` is covariant on algebra homs while pullback reverses the direction in general, but here both source/target are the same `S`).
- **How**: Applies `ext_of_D`. On generators `D x`: uses `pullbackKaehler_D` three times to show `D(f(g(x))) = D(f(g x))`. For the smul step: uses `pullbackKaehler_smul_S` twice.
- **Hypotheses**: None.
- **Uses from project**: `ext_of_D`, `pullbackKaehler_smul_S`, `pullbackKaehler_D`
- **Used by**: none in file (public API)
- **Visibility**: public (`@[simp]`)
- **Lines**: 221–234, ~14 lines
- **Notes**: None

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `TwistedKaehler` (struct) | virtually everything |
| `TwistedKaehler.out_smul_S` | `instModule`, `IsScalarTower`, `derivationCompHom`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp` |
| `derivationCompHom` | `pullbackKaehler`, `pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S` |
| `pullbackKaehler` | `pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_id`, `pullbackKaehler_comp` |
| `ext_of_D` (private) | `pullbackKaehler_id`, `pullbackKaehler_comp` |
| `pullbackKaehler_smul_S` | `pullbackKaehler_id`, `pullbackKaehler_comp` |
| `pullbackKaehler_D` | `pullbackKaehler_id`, `pullbackKaehler_comp` |
