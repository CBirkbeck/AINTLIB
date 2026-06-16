# Decomposition — complete the dual isogeny / isogeny-class symmetry (Silverman III.4.10–4.12, III.6.1)

Source: Silverman AEC 2nd ed, in-repo PDF (PDF page = book page + 18). Read in full:
III.4.8 (p.71), III.4.10 (p.72–73), III.4.11 (p.73–74), III.4.12 (p.74–75), III.5.1 (p.76).
BINDING reuse discipline: every leaf cites the EXISTING project decl that discharges it
(verified present), or is flagged as genuine remaining content.

## Plain-English proof (the dual, mirroring Silverman)

The dual `φ̂ : E₂ → E₁` of a nonconstant isogeny `φ : E₁ → E₂` of degree `m` is obtained by
**factoring `[m] : E₁ → E₁` through `φ`** (Silverman III.6.1 via III.4.11), not by exhibiting
`κ⁻¹∘φ*∘κ` as a rational map. For **separable** `φ`:
1. `#ker φ = m = deg φ` (III.4.10c). Hence by Lagrange every `k ∈ ker φ` is `m`-torsion, so
   `ker φ ⊆ ker[m]` (III.4.10c + Lagrange).
2. `φ` separable ⟹ `K̄(E₁)/φ*K̄(E₂)` is Galois with group `≅ ker φ` acting by translations
   `τ_T*` (III.4.10b,c).
3. `ker φ ⊆ ker[m]` ⟹ every `τ_T*` (`T ∈ ker φ`) fixes `[m]*K̄(E₁)` (because `[m]∘τ_T = [m]` as
   `[m]T = 0`), so `[m]*K̄(E₁) ⊆ (K̄(E₁))^{ker φ} = φ*K̄(E₂)` (III.4.11's fixed-field step).
4. The inclusion `Im([m]*) ⊆ Im(φ*)` (II.2.4b) yields `λ = φ̂ : E₂ → E₁` with `φ̂∘φ = [m]`, an
   isogeny since `φ̂(O) = φ̂(φ(O)) = [m](O) = O`.

For **inseparable** `φ`: factor `φ = φ_s ∘ Frob^r` (III.4.10a: `deg_i φ = e_φ`, the
Frobenius part), dualize `φ_s` as above and the Frobenius part via Verschiebung.

This is EXACTLY the `EC.universal_dualGaloisData` residual (`Dual.lean:461`): the per-φ Galois
fixed-field data. The agent's `DualGalois.lean` already realizes steps 2–4 modulo the per-φ
inputs; this plan discharges those inputs for a general (separable) φ.

## Existing infra to REUSE (verified present, sorry-free unless noted)

- `Hasse/PointFix.lean:pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` — step 2/3's
  fixed-field equality `Im(φ*) = Fix(ker φ)` (needs `[Fintype F]`, `#ker=deg`, the φ-covariance).
- `EC/SeparableKernelTorsor.lean:card_kernel_eq_degree_of_separable_concrete` (#ker=deg, witness-param),
  `kernelTranslateForwardAut` (III.4.10b translation action).
- `EC/IsogenyKernel.lean:isGalois_of_separable_and_normal`, `card_kernel_eq_degree_of_separable_witness`,
  `ramificationIndex_eq_one_of_separable_witnesses`, `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`.
- `EC/TranslationOrd.lean:translateAlgEquivOfPoint` (τ_T* as an AlgEquiv of K(E)).
- `EC/IsogenyAG/Dual.lean`: `rangeIncl_of_fixedField`, `DualGaloisData`, `hasDualWitness_of_galoisData`,
  `universal_dual_witness` (modulo `universal_dualGaloisData`).
- `EC/IsogenyAG/DualGalois.lean`: `fixedField_hfix_of_xy_family_of_card`, capstone
  `hasDualWitness_of_basic_witnesses` (axiom-clean — proves the residual IS dischargeable from
  standard witnesses).
- `EC/IsogenyAG.lean`: `addHomProperty` (III.4.8, done), `toAddMonoidHomOfWitness`, `mulByIntOfBasepoint`.

## Leaves (ordered; each cites source + the discharging existing decl)

### DUAL-1 — `ker φ ⊆ ker[deg φ]` for separable φ (Lagrange)
Statement: for separable `φ : EC.Isogeny W₁ W₂`, every `k ∈ ker φ` satisfies `(deg φ) • k = 0`.
Source: III.4.10c (`#ker φ = deg φ`, p.73) + Lagrange (`orderOf k ∣ #ker φ`).
Discharge: REUSE `card_kernel_eq_degree_of_separable_concrete` + mathlib `pow_card_eq_one`/
`orderOf_dvd_card` (Lagrange on the finite group `ker φ`). LOC ~30 (source: 1 line "Lagrange").
→ **leaf** (mathlib + existing project).

### DUAL-2 — the per-φ covariance `xy_family` for a general isogeny ⚑ (the genuine remaining content)
Statement: a general `φ : EC.Isogeny W₁ W₂` (with a CoordHom) satisfies the translation-covariance
hypothesis `xy_family` that `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` consumes
(φ commutes with the ker-φ translation action on generators).
Source: III.4.10b proof (p.72): "`τ_T*(φ*f) = (φ∘τ_T)*f = φ*f` since `φ∘τ_T = φ`" — the covariance
IS that `φ∘τ_T = φ` for `T ∈ ker φ`, i.e. φ kills its kernel by translation.
Discharge status: the Hasse work proved this only for SPECIFIC isogenies (1−π, rπ−s). For a general φ
it follows from `φ.addHomProperty` (III.4.8, NOW PROVEN): `φ(P+T) = φ(P) + φ(T) = φ(P)` for `T∈ker φ`,
i.e. `φ∘τ_T = φ`; lift to `τ_T*∘φ* = φ*` on K(E). → **needs `addHomProperty` (have it) + the
generic-point lift** (the `xy_family` shape). API GAP if the generic-point lift of `φ∘τ_T=φ` to
`τ_T*∘φ*=φ*` isn't a one-liner from existing covariance infra. LOC ~80–150. **The crux of the
general discharge.**

### DUAL-3 — `universal_dualGaloisData` for separable φ
Statement: `EC.universal_dualGaloisData φ` for separable `φ` with a CoordHom + `[Fintype F]`.
Source: III.4.11 (p.73–74) applied to `(φ, [deg φ])`.
Discharge: assemble `fixedField_hfix_of_xy_family_of_card` (REUSE) from DUAL-2 (`xy_family`) +
`card_kernel_eq_degree` + DUAL-1; feed `DualGaloisData` via `rangeIncl_of_fixedField` (REUSE). The
basepoint/∞-reflection are RAMI-1 / `frobenius_reflects_ordAtInfty`. → **internal** (composes
DUAL-1, DUAL-2, RAMI-1 + reused Dual/DualGalois decls). LOC ~60.

### BRIDGE-1 — `EC.Isogeny → HasseWeil.Isogeny` (now that III.4.8 is proven)
Statement: `EC.Isogeny.toBasicIsogeny (φ) (cd) : HasseWeil.Isogeny W₁ W₂` :=
`{ pullback := φ.toCurveMap.pullback, toAddMonoidHom := φ.toAddMonoidHomOfWitness cd
  (φ.addHomProperty cd) }`.
Source: III.4.8 (p.71, the group-hom property — now `addHomProperty`).
Discharge: REUSE `addHomProperty` (done) + `toAddMonoidHomOfWitness`. → **leaf** (existing project).
LOC ~25. Lets DUAL-2/3 name `ker φ` at the Basic.Isogeny level (where the kernel/Galois lemmas live).

### RAMI-1 — `e_φ(P) = deg_i φ` uniform ⟹ ∞-regularity reflection
Statement: for `φ` and any `g ∈ K(E₂)`, `0 ≤ ord_∞(g) → 0 ≤ ord_∞(φ*g)`; for separable φ, `e_φ(O)=1`.
Source: III.4.10a (p.72–73): `e_φ(P) = deg_i φ` for every `P` (uniform ramification).
Discharge: REUSE `ramificationIndex_eq_one_of_separable_witnesses` (separable ⟹ e=1) +
`ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`; the reflection is `e=1 ⟹ ord preserved`.
Frobenius case = `frobenius_reflects_ordAtInfty` (done). → **leaf/internal** (existing project). LOC ~50.

### DUAL-4 — general (inseparable) φ via Frobenius factorization [SCOPE: defer]
Statement: `universal_dualGaloisData φ` for ALL φ, via `φ = φ_s ∘ Frob^r` (III.4.10a) + Verschiebung.
Source: III.4.10a (`deg_i = e_φ`, the Frobenius part), III.4.12 (quotient/separable).
Status: the inseparable side needs the separable∘Frobenius factorization as `EC.Isogeny`s + the
Frobenius dual (Verschiebung). Larger; **defer** — DUAL-3 closes the separable case, which is the
bulk + suffices for the isogeny-class relation restricted to separable isogenies. Flag as a later ticket.

## Honest assessment
- DUAL-1, BRIDGE-1, RAMI-1: clean reuse of existing infra (small).
- DUAL-3: assembly of reused decls (small) — gated on DUAL-2.
- **DUAL-2 is the genuine crux**: the per-φ covariance `xy_family` for a GENERAL isogeny. III.4.8
  (`addHomProperty`, now proven) gives `φ∘τ_T = φ` for `T∈ker φ`; the remaining content is lifting
  that point-level identity to the generic-point/pullback `xy_family` shape that PointFix consumes.
  This is the one piece that may need real work (or may be a short consequence of `addHomProperty` +
  existing covariance lemmas — to be confirmed by stating it).
- DUAL-4 (inseparable): deferred (Frobenius/Verschiebung), explicitly out of this plan's core.
