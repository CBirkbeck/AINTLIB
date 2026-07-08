import ModularCurves.LevelStructure.Incidence

/-!
# Level spaces over the Weierstrass atlas (T-W8)

The level spaces `U_{Γ₁(N)}`, `U_{Γ(N)}` (and `U_{Γ₀(N)}`) as closed subschemes cut out of the
`N`-torsion (resp. its self-product) by the D-stream Cartier incidence loci. Parametric over an
arbitrary `E : EllipticCurve S`; the universal instantiation over `weierstrassAtlas` follows once
the universal `EllipticCurve` is available. The classifying/universal properties (`_spec`) are the
representability presentations `T-E7` and the H-stream consume.

Per v10.24(b) each level-space definition ships its opaque interface — the closed immersion and
the universal-property `_spec` — in this same file; downstream consumers use `_spec`, never the
raw `Classical.choose`.

## Main definitions

* `levelSpaceΓ₁ E N` : `U_{Γ₁(N)}`, closed in `E[N]`, cut by the exact-order locus.
* `levelSpaceΓ E N`   : `U_{Γ(N)}`, closed in `E[N] ×_S E[N]`, cut by the full-level locus.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)

/-! ### `U_{Γ₁(N)}` — exact-order-`N` level structures -/

/-- **(T-W8, `U_{Γ₁(N)}`)** The `Γ₁(N)` level space: the closed subscheme of `E[N]` where the
tautological torsion point has exact order `N`, cut out by `exists_exactOrderLocus`. -/
noncomputable def levelSpaceΓ₁ [NeZero N] : Scheme.{u} :=
  (exists_exactOrderLocus E N).choose.subscheme

/-- The closed immersion `U_{Γ₁(N)} ↪ E[N]`. -/
noncomputable def levelSpaceΓ₁ι [NeZero N] : levelSpaceΓ₁ E N ⟶ E.torsion N :=
  (exists_exactOrderLocus E N).choose.subschemeι

/-- **Opaque interface (v10.24(b))** — the universal property of `U_{Γ₁(N)}`: a point of `E`
killed by `N` over `t` factors (via its classifying map to `E[N]`) through `U_{Γ₁(N)}` iff it has
exact order `N` on the base-changed curve. -/
theorem levelSpaceΓ₁_spec [NeZero N] :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P : E.Point t)
      (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ levelSpaceΓ₁ E N, h ≫ levelSpaceΓ₁ι E N = E.pointToTorsion P hP) ↔
        EllipticCurve.Section.HasExactOrder (E.baseChange t)
          (EllipticCurve.Point.asSection E t P) N :=
  (exists_exactOrderLocus E N).choose_spec

/-! ### `U_{Γ(N)}` — Drinfeld full level-`N` structures -/

/-- **(T-W8, `U_{Γ(N)}`)** The `Γ(N)` level space: the closed subscheme of `E[N] ×_S E[N]` where
the tautological pair is a Drinfeld full level-`N` structure, cut out by `exists_fullLevelLocus`. -/
noncomputable def levelSpaceΓ [NeZero N] : Scheme.{u} :=
  (exists_fullLevelLocus E N).choose.subscheme

/-- The closed immersion `U_{Γ(N)} ↪ E[N] ×_S E[N]`. -/
noncomputable def levelSpaceΓι [NeZero N] :
    levelSpaceΓ E N ⟶ pullback (E.torsionπ N) (E.torsionπ N) :=
  (exists_fullLevelLocus E N).choose.subschemeι

/-- **Opaque interface (v10.24(b))** — the universal property of `U_{Γ(N)}`: a pair of points of
`E` killed by `N` over `t` factors (via its classifying map to `E[N] ×_S E[N]`) through
`U_{Γ(N)}` iff it is a Drinfeld full level-`N` structure. -/
theorem levelSpaceΓ_spec [NeZero N] :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P Q : E.Point t)
      (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero)
      (hQ : Q.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ levelSpaceΓ E N, h ≫ levelSpaceΓι E N =
          pullback.lift (E.pointToTorsion P hP) (E.pointToTorsion Q hQ) (by simp)) ↔
        (E.baseChange t).IsFullLevel N (EllipticCurve.Point.asSection E t P)
          (EllipticCurve.Point.asSection E t Q) :=
  (exists_fullLevelLocus E N).choose_spec

end ModularCurves
