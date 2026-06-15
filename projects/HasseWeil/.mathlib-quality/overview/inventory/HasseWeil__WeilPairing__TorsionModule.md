# Inventory: ./HasseWeil/WeilPairing/TorsionModule.lean

**File purpose**: Packages the structure-theoretic consequences of `#E[ℓ]=ℓ²`: equips the geometric `ℓ`-torsion `E[ℓ] = W.toAffine[(ℓ:ℤ)]` with a `Module (ZMod ℓ)` structure, proves it is finite of `ZMod ℓ`-dimension `2`, and produces a `Fin 2`-basis and the linear equivalence `E[ℓ] ≃ₗ (Fin 2 → ZMod ℓ)`. These are the structures the downstream mod-`ℓ` representation (`Representation.lean`/`DetDeg.lean`) consumes.

**Imports**: `HasseWeil.WeilPairing.TorsionCardEll`, `Mathlib.Algebra.Module.ZMod`, `Mathlib.Algebra.Field.ZMod`, `Mathlib.FieldTheory.Finiteness`, `Mathlib.LinearAlgebra.Dimension.Free`

**Namespace**: `HasseWeil.WeilPairing.TorsionGeometric` (re-opens `HasseWeil`). **Section variables**: `{F}[Field F][DecidableEq F](W)[IsElliptic]`. Two sections: `ModuleStructure` (`(ℓ:ℕ)[Fact ℓ.Prime]`) and `Dimension` (adds `[IsAlgClosed F](hℓF:(ℓ:F)≠0)`).

**Total declarations**: 7 (1 `noncomputable scoped instance`, 2 `noncomputable def`, 4 `theorem`). **No `sorry`, no `set_option`.**

---

## Declarations

### `theorem nsmul_eq_zero_of_mem_torsion_ell`
- **What**: Every `P ∈ E[ℓ]` is killed by the natural-number action: `ℓ • P = 0`. The defining property feeding the `ZMod ℓ`-module structure.
- **How**: from membership (`mem_torsionSubgroup`) get `(ℓ:ℤ)•P.val=0`, convert to `ℓ•P.val=0` (`natCast_zsmul`), transport into the subgroup via `Subtype.ext` + `AddSubmonoidClass.coe_nsmul`.
- **Hypotheses**: `omit hℓ` (no primality needed); `(ℓ:ℕ)`, `(P : E[ℓ])`. No characteristic hypothesis.
- **Uses from project**: `mem_torsionSubgroup`, `torsionSubgroup`.
- **Used by (in file)**: `torsion_ell_zmodModule`.
- **Visibility**: public. **Lines**: 53–63.

### `noncomputable scoped instance torsion_ell_zmodModule`
- **What**: The `Module (ZMod ℓ) E[ℓ]` instance, from "`ℓ` annihilates `E[ℓ]`".
- **How**: `AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_torsion_ell W ℓ)` — the standard mathlib idiom for turning an `ℓ`-torsion abelian group into a `ZMod ℓ`-module.
- **Hypotheses**: `(ℓ:ℕ)[Fact ℓ.Prime]`. Independent of `(ℓ:F)≠0`.
- **Uses from project**: `nsmul_eq_zero_of_mem_torsion_ell`.
- **Used by**: all of the `Dimension` section, and downstream (`Representation.lean`, `DetDeg.lean`). Registered **scoped** so `finrank`/`Basis` API resolves it.
- **Visibility**: scoped instance. **Lines**: 68–70.

### `theorem card_torsion_ell_nat`
- **What**: `Nat.card E[ℓ] = ℓ²` (the `Nat.card` form, dropping the `ℤ`-coercion of `card_torsion_ell`).
- **How**: `card_torsion_ell W (ℓ:ℤ)` then a cast bookkeeping (`push_cast` + `exact_mod_cast`).
- **Hypotheses**: `omit hℓ`; `include hℓF`; `[IsAlgClosed F]`, `hℓF:(ℓ:F)≠0`.
- **Uses from project**: `card_torsion_ell`.
- **Used by (in file)**: `torsion_ell_finite`, `finrank_torsion_ell`.
- **Visibility**: public. **Lines**: 83–87.

### `theorem torsion_ell_finite`
- **What**: `Finite E[ℓ]` (cardinality `ℓ²>0`).
- **How**: `Nat.finite_of_card_ne_zero` with `card_torsion_ell_nat` and `pow_ne_zero`.
- **Uses from project**: `card_torsion_ell_nat`.
- **Used by (in file)**: `finrank_torsion_ell`, `torsion_ell_basis`.
- **Visibility**: public. **Lines**: 90–93.

### `theorem finrank_torsion_ell`  ★ live API (dimension = 2)
- **What**: `Module.finrank (ZMod ℓ) E[ℓ] = 2`.
- **How**: `Module.natCard_eq_pow_finrank` gives `#E[ℓ] = (#ZMod ℓ)^finrank`; rewrite `#E[ℓ]=ℓ²` and `#ZMod ℓ=ℓ` (`ZMod.card`, `NeZero ℓ`), then `Nat.pow_right_injective hℓ.two_le` forces `finrank=2`.
- **Uses from project**: `card_torsion_ell_nat`, `torsion_ell_finite`.
- **Used by (in file)**: `torsion_ell_basis`.
- **Visibility**: public. **Lines**: 98–110.

### `noncomputable def torsion_ell_basis`  ★ live API (the chosen basis)
- **What**: A `Basis (Fin 2) (ZMod ℓ) E[ℓ]`.
- **How**: `Module.finBasisOfFinrankEq (ZMod ℓ) _ (finrank_torsion_ell …)`.
- **Uses from project**: `torsion_ell_finite`, `finrank_torsion_ell`.
- **Used by (in file)**: `torsion_ell_linearEquiv`.
- **Used by (external)**: `Representation.lean` (the basis in which `rhoEll` is the matrix), `DetDeg.lean` (the pairing Gram-determinant basis). **This is the single most load-bearing definition for the ℓ-adic matrix.**
- **Visibility**: public. **Lines**: 113–116.

### `noncomputable def torsion_ell_linearEquiv`
- **What**: `E[ℓ] ≃ₗ[ZMod ℓ] (Fin 2 → ZMod ℓ)` (the explicit `(ZMod ℓ)²` identification).
- **How**: `(torsion_ell_basis …).equivFun`.
- **Uses from project**: `torsion_ell_basis`.
- **Used by (in file)**: none.
- **Used by (external)**: `Representation.lean` (only — and only referenced in its module docstring as the motivating structure; the matrix `rhoEll` is built from `torsion_ell_basis` directly, not from this equiv).
- **Visibility**: public. **Lines**: 120–122.

---

## File Summary

**Role in cluster**: Turns the bare cardinality `#E[ℓ]=ℓ²` into the **linear-algebraic object** `E[ℓ] ≅ (ZMod ℓ)²`. This is the bridge from the AG content to the matrix endgame.

**Live spine**: `torsion_ell_zmodModule` (the module instance) → `finrank_torsion_ell` (=2) → `torsion_ell_basis` (the basis feeding `rhoEll` and the pairing Gram matrix in `DetDeg.lean`).

**Cleanup findings**:
- (a) **Unused-in-file but exported**: `torsion_ell_linearEquiv` — only referenced in `Representation.lean`'s docstring, never in a proof. It is effectively documentation; consider dropping it or marking its purely-illustrative status. `nsmul_eq_zero_of_mem_torsion_ell` is exposed publicly but is really a helper for the instance (could be `private`).
- (b) No scratch/abandoned routes.
- (c) **Best-practice mathlib API throughout** — this file is the *positive* example for the cluster: `AddCommGroup.zmodModule`, `Module.natCard_eq_pow_finrank`, `Module.finBasisOfFinrankEq`, `Basis.equivFun` are exactly the idiomatic constructions. `E[ℓ]` is the project's `torsionSubgroup` and the `(ZMod ℓ)²` structure is genuinely `Module (ZMod ℓ)` / `Basis` / `finrank`, not hand-rolled. **No cleanup needed on the modelling.**
- (d) **Under-general**: `torsion_ell_zmodModule` and `nsmul_eq_zero_of_mem_torsion_ell` deliberately drop the characteristic hypothesis (good — they hold for any `ℓ`); only the `Dimension` section needs `[IsAlgClosed F]`+`(ℓ:F)≠0`. Correctly factored.
- **`sorry`/heartbeats**: none. All proofs ≤13 lines.
