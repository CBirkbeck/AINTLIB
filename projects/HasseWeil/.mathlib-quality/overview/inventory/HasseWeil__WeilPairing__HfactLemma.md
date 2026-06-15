# Inventory: ./HasseWeil/WeilPairing/HfactLemma.lean

**File**: `HasseWeil/WeilPairing/HfactLemma.lean`
**Total declarations**: 6 (5 theorems/defs, 1 Prop-valued `def`)
**Lines**: 344

**Summary**: Discharges the divisor factorisation hypothesis `hfact` of `weilPairing_adjoint_core` (Silverman III.8.2). The file proves that for a separable isogeny `φ`, there is a factorisation `φ^* g_T = c · (g_{φ̂T} · [ℓ]^* k)` (nonzero constant `c`, function `k`), isolating the one carried residual `PicDualDivisorClass` (the projective-model form of Silverman III.6.1b). No `sorry`, no `set_option maxHeartbeats`.

---

### `theorem pullbackDivisor_comm`

- **Type**:
  ```
  theorem pullbackDivisor_comm {f g : W.toAffine.Point →+ W.toAffine.Point}
      (hf : Finite f.ker) (hg : Finite g.ker)
      (hfg : g.comp f = f.comp g)
      (D : ProjectiveDivisor (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
      pullbackDivisor f hf (pullbackDivisor g hg D) =
        pullbackDivisor g hg (pullbackDivisor f hf D)
  ```
- **What**: Fibre-pullback divisors of commuting additive point endomorphisms commute: `(f^* ∘ g^*) D = (g^* ∘ f^*) D`.
- **How**: Pure point-function extensionality: unfolds `pullbackDivisor_apply` at each place `w`, then uses `DFunLike.congr_fun hfg` (the commutation hypothesis applied pointwise) to show `g(f(w)) = f(g(w))`.
- **Hypotheses**: Two `AddMonoidHom` endomorphisms `f, g` of `E.Point` with finite kernels, satisfying `g.comp f = f.comp g`.
- **Uses from project**: `pullbackDivisor_apply` (from `DivisorPullback.lean`), `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by**: `hfact_projectiveDivisorOf_eq` (within this file, lines 225-226)
- **Visibility**: public
- **Lines**: 94–107, proof ~10 lines
- **Notes**: Clean, no issues.

---

### `theorem pullbackDivisor_kappaDivisor_local`

- **Type**:
  ```
  theorem pullbackDivisor_kappaDivisor_local (ℓ : ℤ)
      [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] (T : W.toAffine.Point) :
      pullbackDivisor (mulByInt W.toAffine ℓ).toAddMonoidHom hker (Curves.kappaDivisor W.toAffine T) =
        pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker T -
          pullbackDiv (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0
  ```
- **What**: The fibre-pullback of the Abel–Jacobi divisor `(T) − (O)` under `[ℓ]` decomposes as `[ℓ]^*(T) − [ℓ]^*(O)` in `pullbackDiv` terms. Local copy of `PairingNondeg.pullbackDivisor_kappaDivisor`, renamed `_local` to avoid cross-file name clash.
- **How**: Rewrites `kappaDivisor` as a difference of singles and uses `pullbackDivisorHom_apply`, `map_sub`, `pullbackDivisor_single`, `one_smul`, and point coercion lemmas.
- **Hypotheses**: `[ℓ]`-kernel is finite (typeclass).
- **Uses from project**: `Curves.kappaDivisor`, `pullbackDivisorHom_apply`, `pullbackDivisor_single`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`, `ProjectiveSmoothPoint.toAffinePoint_infinity`
- **Used by**: `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` (line 142)
- **Visibility**: public
- **Lines**: 120–129, proof ~5 lines
- **Notes**: Named `_local` specifically to avoid clash with `PairingNondeg.pullbackDivisor_kappaDivisor` when `SeparableScaling` imports both files.

---

### `theorem weilFunction_divisor_eq_pullbackDivisor_kappaDivisor`

- **Type**:
  ```
  theorem weilFunction_divisor_eq_pullbackDivisor_kappaDivisor [IsAlgClosed F]
      (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) =
        pullbackDivisor (mulByInt W.toAffine ℓ).toAddMonoidHom
            (mulByInt_ker_finite W ℓ hℓ) (Curves.kappaDivisor W.toAffine T)
  ```
- **What**: The projective divisor of the Weil function `g_T` equals the fibre-pullback divisor `[ℓ]^*(κ(T))` of the Abel–Jacobi divisor `(T) − (O)`.
- **How**: Combines `weilFunction_divisor` (the explicit formula `div(g_T) = pullbackDiv [ℓ] T − pullbackDiv [ℓ] O`) with `pullbackDivisor_kappaDivisor_local` to rewrite as a single pullbackDivisor.
- **Hypotheses**: `F` algebraically closed, `ℓ ≠ 0` in `F`, `T` is `ℓ`-torsion.
- **Uses from project**: `mulByInt_ker_finite`, `weilFunction_divisor`, `pullbackDivisor_kappaDivisor_local` (this file), `W_smooth`
- **Used by**: `hfact_projectiveDivisorOf_eq` (lines 224, 238)
- **Visibility**: public
- **Lines**: 134–142, proof ~6 lines
- **Notes**: The `show rfl` step at line 140–141 handles the `W_smooth` vs `⟨W.toAffine⟩` definitional identity (a known pitfall in this project since `W_smooth` is a `def`).

---

### `def PicDualDivisorClass`

- **Type**:
  ```
  def PicDualDivisorClass (φ : Isogeny W.toAffine W.toAffine)
      [Finite φ.toAddMonoidHom.ker]
      (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom)
      (hfin : letI := ch.toAlgebra; Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing)
      : Prop :=
    ∀ T : W.toAffine.Point,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
        (pullbackDivisor φ.toAddMonoidHom inferInstance (Curves.kappaDivisor W.toAffine T) -
          Curves.kappaDivisor W.toAffine ((φ.picDual ch hinj hfin) T))
  ```
- **What**: A `Prop`-valued definition packaging the projective-divisor form of Silverman III.6.1b: for every torsion point `T`, the difference divisor `φ^*((T) − (O)) − (φ̂T − O)` is principal (i.e., `div k₀` for some `k₀ ∈ K(E)`). This is the single isolated minimal residual of the `hfact` discharge.
- **How**: No proof body; pure definition encoding the hypothesis.
- **Hypotheses**: Isogeny `φ : E → E` with finite kernel, `CoordHom` data `ch`, injectivity `hinj`, finiteness `hfin` (for `picDual` to be defined).
- **Uses from project**: `pullbackDivisor`, `Curves.kappaDivisor`, `Isogeny.picDual`, `SmoothPlaneCurve.ProjIsPrincipal`
- **Used by**: `hfact_of_picDualDivisorClass` (line 266), `weilPairing_adjoint_of_picDualDivisorClass` (line 332); also used extensively in `PicDualDivisorClassLemma.lean`
- **Visibility**: public
- **Lines**: 164–173, no proof
- **Notes**: The key API export of this file. Represents the frontier between the projective-divisor world (`hfact`) and the affine ideal class group model (`PicDual`). Referenced as the "honest frontier" in the module docstring.

---

### `theorem hfact_projectiveDivisorOf_eq`

- **Type**:
  ```
  theorem hfact_projectiveDivisorOf_eq (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
      (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
      (hφ : ProjOrdTransport φ)
      (hcomm : [ℓ] ∘ φ = φ ∘ [ℓ] as AddMonoidHoms)
      {T U : W.toAffine.Point} (hT : ℓ • T = 0) (hU : ℓ • U = 0)
      {k₀ : KE} (hk₀_ne : k₀ ≠ 0)
      (hk₀_div : projectiveDivisorOf k₀ = pullbackDivisor φ (kappaDivisor T) − kappaDivisor U) :
      projectiveDivisorOf (φ.pullback (weilFunction W ℓ hℓ T hT)) =
        projectiveDivisorOf (weilFunction W ℓ hℓ U hU * (mulByInt W.toAffine ℓ).pullback k₀)
  ```
- **What**: The key divisor equality of the `hfact` proof: given the Abel–Jacobi function `k₀` witnessing `φ^*(κT) ∼ κU`, the projective divisors of `φ^*(g_T)` and `g_U · [ℓ]^*(k₀)` are equal.
- **How**: Three-step calculation. (LHS) `div(φ^* g_T) = φ^*([ℓ]^* κT)` via `pullback_divisorOf_eq_of_divisorOf_eq hφ` with `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor`, then commuted to `[ℓ]^*(φ^* κT)` via `pullbackDivisor_comm`. (Middle) `φ^* κT = κU + div k₀` from `hk₀_div` by `abel`. (RHS) `div(g_U · u) = div(g_U) + div(u)` via `projectiveDivisorOf_mul` + `pullback_divisorOf_eq_of_divisorOf_eq` for `[ℓ]`. Concludes by `pullbackDivisorHom_apply` + `map_add`.
- **Hypotheses**: `F` algebraically closed (via section variable), `ℓ ≠ 0` in `F`, `φ` with finite kernel and `ProjOrdTransport` datum, `[ℓ] ∘ φ = φ ∘ [ℓ]`, `T` and `U` are `ℓ`-torsion, `k₀ ≠ 0` with the stated divisor.
- **Uses from project**: `mulByInt_ker_finite`, `projOrdTransport_mulByInt`, `Curves.kappaDivisor`, `pullbackDivisor_comm` (this file), `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` (this file), `weilFunction_ne_zero`, `Isogeny.pullback_injective`, `pullback_divisorOf_eq_of_divisorOf_eq`, `SmoothPlaneCurve.projectiveDivisorOf_mul`, `pullbackDivisorHom_apply`
- **Used by**: `hfact_of_picDualDivisorClass` (line 279)
- **Visibility**: public
- **Lines**: 196–242; proof body lines 210–242 = **33 lines** (>30)
- **Notes**: Proof >30 lines. Contains the core divisor calculation of Silverman III.8.2 (the heavy computation). Uses `set κT` / `set κU` for readability. Relies on `projOrdTransport_mulByInt` for the `[ℓ]` case of `ProjOrdTransport`.

---

### `theorem hfact_of_picDualDivisorClass`

- **Type**:
  ```
  theorem hfact_of_picDualDivisorClass (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
      (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
      (hφ : ProjOrdTransport φ) (hcomm : [ℓ] ∘ φ = φ ∘ [ℓ])
      (ch : φ.CoordHom) (hinj : ...) (hfin : ...)
      (hpd : PicDualDivisorClass W φ ch hinj hfin)
      (T : W.toAffine.Point) (hT : ℓ • T = 0) :
      ∃ (c : F) (k : KE), c ≠ 0 ∧
        φ.pullback (weilFunction W ℓ hℓ T hT) =
          algebraMap F KE c * (weilFunction W ℓ hℓ ((φ.picDual ch hinj hfin) T) (...) *
            (mulByInt W.toAffine ℓ).pullback k)
  ```
- **What**: The separable divisor factorisation `hfact` (Silverman III.8.2 / III.6.1b): given `PicDualDivisorClass`, there exist `c ∈ F×` and `k ∈ K(E)` with `φ^*(g_T) = c · g_{φ̂T} · [ℓ]^*(k)`.
- **How**: Destructs `hpd T` to obtain the Abel–Jacobi function `k₀`. Calls `hfact_projectiveDivisorOf_eq` to get the divisor equality `div(φ^* g_T) = div(g_U · [ℓ]^* k₀)`. Then computes `div(φ^* g_T / (g_U · [ℓ]^* k₀)) = 0` via `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, and `add_neg_cancel`. Applies `const_unit_of_projectiveDivisorOf_eq_zero` to extract the nonzero constant `c`. Concludes by `div_eq_iff` rearrangement.
- **Hypotheses**: Same as `hfact_projectiveDivisorOf_eq` plus `hpd : PicDualDivisorClass`.
- **Uses from project**: `hfact_projectiveDivisorOf_eq` (this file), `PicDualDivisorClass` (this file), `weilFunction_ne_zero`, `Isogeny.pullback_injective`, `SmoothPlaneCurve.projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, `const_unit_of_projectiveDivisorOf_eq_zero` (from `Constancy`), `Isogeny.picDual`
- **Used by**: `weilPairing_adjoint_of_picDualDivisorClass` (line 341)
- **Visibility**: public
- **Lines**: 258–303; proof body lines 273–303 = **31 lines** (>30)
- **Notes**: Proof >30 lines. Contains the "same-divisor ⟹ constant ratio" argument. The `IsDedekindDomain` instance is inferred via `haveI` at the start of the proof body (line 274).

---

### `theorem weilPairing_adjoint_of_picDualDivisorClass`

- **Type**:
  ```
  theorem weilPairing_adjoint_of_picDualDivisorClass (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
      (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
      (ch : φ.CoordHom) (hinj : ...) (hfin : ...)
      (hφ : ProjOrdTransport φ) (hcommφ : [ℓ] ∘ φ = φ ∘ [ℓ])
      (hpd : PicDualDivisorClass W φ ch hinj hfin)
      (S T : W.toAffine.Point) (hS hT : ...) (hφS : ...)
      (hcomm' : translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
                  φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) (weilFunction W ℓ hℓ T hT))) :
      weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT =
        weilPairing W ℓ hℓ S ((φ.picDual ch hinj hfin) T) hS (...)
  ```
- **What**: The separable Weil-pairing adjoint `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` (Silverman III.8.2), proved by wiring `hfact_of_picDualDivisorClass` into `weilPairing_adjoint_picDual`. The `hfact` hypothesis of the core adjoint lemma is supplied here rather than carried.
- **How**: Single `obtain` to get `(c, k, hc0, hfact)` from `hfact_of_picDualDivisorClass`, then a single `exact weilPairing_adjoint_picDual` applying those witnesses.
- **Hypotheses**: All hypotheses of `hfact_of_picDualDivisorClass` plus the translation covariance `hcomm'` required by `weilPairing_adjoint_core` (still carried, not derived here).
- **Uses from project**: `hfact_of_picDualDivisorClass` (this file), `weilPairing_adjoint_picDual` (from `PairingAdjoint.lean`)
- **Used by**: `PicDualDivisorClassLemma.weilPairing_adjoint_of_naturality` (external, `PicDualDivisorClassLemma.lean` line 313)
- **Visibility**: public
- **Lines**: 324–342; proof body lines 339–342 = ~4 lines
- **Notes**: Very short proof; serves as the public API exit point from this file into `PicDualDivisorClassLemma`.

---

## Cross-reference summary

| Declaration | Used by (in file) | Used by (other files) |
|---|---|---|
| `pullbackDivisor_comm` | `hfact_projectiveDivisorOf_eq` | (no external callers found) |
| `pullbackDivisor_kappaDivisor_local` | `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` | (no external callers found) |
| `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` | `hfact_projectiveDivisorOf_eq` (×2) | (no external callers found) |
| `PicDualDivisorClass` | `hfact_of_picDualDivisorClass`, `weilPairing_adjoint_of_picDualDivisorClass` | `PicDualDivisorClassLemma.lean` (many), `FrobeniusGalois.lean` (comments) |
| `hfact_projectiveDivisorOf_eq` | `hfact_of_picDualDivisorClass` | `SeparableScaling.lean` (comment mention only) |
| `hfact_of_picDualDivisorClass` | `weilPairing_adjoint_of_picDualDivisorClass` | `PicDualDivisorClassLemma.lean` (indirectly via adjoint) |
| `weilPairing_adjoint_of_picDualDivisorClass` | (unused in file) | `PicDualDivisorClassLemma.lean` line 313 |

**Key API** (used by 3+ declarations in file): `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` is used twice in `hfact_projectiveDivisorOf_eq`; `PicDualDivisorClass` is referenced by 2 theorems plus is the central exported type. No single declaration is referenced by 3+ others within this file; the closest is `PicDualDivisorClass` (used in 2 theorems + the def) and `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` (used twice in one proof).

**Declarations not referenced elsewhere in this file** (dead-code candidates for this file; all used externally):
- `pullbackDivisor_kappaDivisor_local` — only used within this file by `weilFunction_divisor_eq_pullbackDivisor_kappaDivisor`
- `weilPairing_adjoint_of_picDualDivisorClass` — the file's main public export, unused within the file
