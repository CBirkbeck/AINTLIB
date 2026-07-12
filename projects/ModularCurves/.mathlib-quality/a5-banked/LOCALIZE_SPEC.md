# a5-P-loc: localized descent + spread of the invariant Weierstrass model

## Goal
Prove (as a NEW standalone algebra lemma, in a fresh scratch file
`/Users/mcu22seu/.claude5/jobs/dc627d4b/tmp/localize_agent.lean`):

Given a finite group `G` acting on a commutative ring `R` (`[Fintype G] [DecidableEq G]
[Nontrivial R] [MulSemiringAction G R]`), a FREE action (`hfree : IsFreeAlgebraAction G ℤ R`,
def in `ForMathlib/InvariantTorsor.lean`), a Weierstrass curve `W₀ : WeierstrassCurve R`, and a
`VariableChange`-cocycle `C : G → VariableChange R` (`IsVCocycle C`,
`haction : ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀`), and a prime
`p` of the fixed subring `Rᴳ := FixedPoints.subring R G` (i.e. `p : Ideal ↥Rᴳ`, `[p.IsPrime]`),
produce an INVARIANT `a ∉ p` and a descended Weierstrass curve over the basic localization
`(Rᴳ)_a = Localization.Away a` whose base change up to `R_a = Localization.Away (a:R)` is
`E⁻¹ • (W₀ base-changed to R_a)` for some `E`. Concretely something like:

```
theorem exists_locally_descended_model {G R} [Group G] [Fintype G] [DecidableEq G]
    [CommRing R] [Nontrivial R] [MulSemiringAction G R] (hfree : IsFreeAlgebraAction G ℤ R)
    (W₀ : WeierstrassCurve R) {C : G → VariableChange R} (hC : IsVCocycle C)
    (haction : ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀)
    (p : Ideal (FixedPoints.subring R G)) [p.IsPrime] :
    ∃ (a : FixedPoints.subring R G) (_ : a ∉ p)
      (W₁ : WeierstrassCurve (Localization.Away a))
      (E : VariableChange (Localization.Away (a : R))),
      W₁.map (algebraMap (Localization.Away a) (Localization.Away (a : R)))
        = E⁻¹ • (W₀.map (algebraMap R (Localization.Away (a : R)))) := ...
```
(Adjust the exact statement as needed — what MATTERS is: an invariant `a ∉ p`, a Weierstrass
curve over `(Rᴳ)_a`, and a base-change relation to `E⁻¹•W₀` over `R_a`, so that
`projModel_descentIso` can later build `projModel W₀' ≅ (projModel W₁) ×_{Spec (Rᴳ)_a} Spec R_a`.)

## Strategy (the two hard parts)
**Part 1 — descend over the LOCAL ring (Rᴳ)_p.**
- `exists_invariant_descent` (`ForMathlib/WeierstrassInvariant.lean`) descends given
  `[IsLocalRing (FixedPoints.subalgebra ℤ A G)]` + `IsFreeAlgebraAction` + a cocycle. So localize.
- Localize `R` at the multiplicative set `S := (Rᴳ \ p)` pushed into `R` (an INVARIANT mult set).
  Let `R_S := Localization S`. Then `(R_S)ᴳ ≅ Localization.AtPrime p = (Rᴳ)_p`, which IS LOCAL.
  KEY NEW INFRA to build: (a) the `MulSemiringAction G R_S` (analogous to
  `InvariantLocalization.MulSemiringAction.away`, but for the mult set `S`; you may build a
  general `MulSemiringAction.localization` for an invariant `Submonoid`); (b) fixed points commute:
  `FixedPoints.subring R_S G ≅ Localization.AtPrime p` — use mathlib `Algebra.IsInvariant`
  (`Mathlib/RingTheory/Invariant/Basic.lean`; `Algebra.IsInvariant.isIntegral`,
  `IsFractionRing`/`IsLocalization` machinery) and AINTLIB `InvariantLocalization.lean`
  (`exists_fixed_mk'_eq_of_forall_awayHom_eq` is the `Away` analogue — generalize its proof to `S`);
  (c) freeness localizes: `IsFreeAlgebraAction G ℤ R_S` from `hfree` (the InvariantTorsor structure
  base-changes; freeness = the torsor map `G × R_S → R_S ×_{(R_S)ᴳ} R_S`-type condition is
  preserved by localization).
- Base-change the cocycle `C` and `W₀` to `R_S` (VariableChange/WeierstrassCurve `.map` are
  functorial; the cocycle stays a cocycle and stays action-compatible — prove via `.map` naturality).
- Apply `exists_invariant_descent` over `R_S` ⇒ `W₁ᵖ : WeierstrassCurve (Rᴳ)_p` and `Eᵖ` with
  `W₁ᵖ.map ((Rᴳ)_p ↪ R_S) = Eᵖ⁻¹ • (W₀ base-changed to R_S)`.

**Part 2 — spread from (Rᴳ)_p to (Rᴳ)_a.**
- `(Rᴳ)_p = Localization.AtPrime p = colim_{a∉p} Localization.Away a`. The 5 coefficients of `W₁ᵖ`
  (`a₁,a₂,a₃,a₄,a₆ ∈ (Rᴳ)_p`) and the entries of `Eᵖ` each come from some `(Rᴳ)_{a_i}`
  (`IsLocalization.AtPrime` ⇒ each element is `b/a_iⁿ`); take `a = ∏ a_i ∉ p`, so all live in
  `(Rᴳ)_a`. Reconstruct `W₁ : WeierstrassCurve (Rᴳ)_a`, `E : VariableChange R_a`, and prove the
  base-change relation persists (it holds after further localizing to `(Rᴳ)_p`/`R_S`; use
  `IsLocalization` injectivity `IsLocalization.injective`/`IsLocalization.map` to descend the
  equation from `R_S` to `R_a`). This "finitely many denominators ⇒ common `a`" is the spread.

## Compile
```
cd /Users/mcu22seu/Documents/GitHub/aintlib-modular-curves
timeout 500 env LEAN_PATH="$(~/.elan/bin/lake env printenv LEAN_PATH)" ~/.elan/bin/lean /Users/mcu22seu/.claude5/jobs/dc627d4b/tmp/localize_agent.lean 2>&1 | grep -iA4 "error" | head -30
```
Start the file with:
```
import ModularCurves.ForMathlib.WeierstrassInvariant
import ModularCurves.ForMathlib.InvariantLocalization
open WeierstrassCurve
open scoped Pointwise
universe u v
namespace ModularCurves
```
You may `import Mathlib` too if you need broad mathlib (slower but fine here). Never put `2>/dev/null` next to lean. You may use a `_scratch.lean` copy in the repo root for lean-lsp MCP tools; delete it when done.

## Key existing lemmas
`exists_invariant_descent`, `IsVCocycle`, `FixedPoints.subring`/`subalgebra` (defeq), `vcSMul`/
`map_variableChange`, `WeierstrassCurve.map`/`map_map`; `InvariantLocalization` (`away`, `awayHom`,
`exists_fixed_mk'_eq_of_forall_awayHom_eq`, `Submonoid.powers_le_comap_algebraMap`); mathlib
`Algebra.IsInvariant`, `IsLocalization`, `Localization.Away`, `Localization.AtPrime`,
`IsLocalization.AtPrime`, `IsLocalization.mk'`, `IsLocalization.exists_mk'_eq`,
`IsLocalization.injective`.

## Report
Report the full working lemma(s) verbatim when the file compiles clean (NO sorry). This is a big
task — if you can only finish Part 1 (the local descent) or only the new infra, report exactly what
compiles, the precise statements proven, and what remains with the exact remaining goals. Partial
verified infra is valuable. Do NOT claim done with any sorry present. Do not touch `projects/`.
