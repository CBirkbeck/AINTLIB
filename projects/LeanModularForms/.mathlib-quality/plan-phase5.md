# Development Plan: Phase 5 — Hecke Adjoint Theory (revised 2026-04-13)

## Goal

Prove `heckeT_p_adjoint` (DS Theorem 5.5.3): `T_p* = ⟨p⟩⁻¹ T_p` w.r.t. the
level-N Petersson inner product `petN`, then derive the full spectral theorem
for simultaneous Hecke eigenforms.

```lean
theorem heckeT_p_adjoint (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g))
```

## References

- **[DS]** Diamond–Shurman, §5.5 (Proposition 5.5.2, Theorem 5.5.3)
- **[Miy]** Miyake, §4.5 (Theorem 4.5.4–4.5.5)

## Current State (2026-04-13 audit)

### What's proved (sorry-free)

| Component | Location | Lines |
|-----------|----------|-------|
| `CuspForm.toModularForm'` | AdjointTheory.lean:50 | Cusp → modular coercion |
| `heckeT_p_zero_at_cusps` | AdjointTheory.lean:92 | T_p preserves cuspidality |
| `heckeT_p_cusp`, `heckeT_n_cusp` | AdjointTheory.lean:140, 275 | Cusp form restrictions |
| `preservesCusps_*` family | AdjointTheory.lean:175-272 | Cuspidality preservation API |
| `heckeT_n_cusp_unfold` | AdjointTheory.lean:284 | Prime-power decomposition |
| `adjointGamma0Rep` + `_units` | AdjointTheory.lean:373-412 | Double coset identity |
| `peterssonAdj` + full API | AdjointTheory.lean:452-597 | GL₂ adjugate: det, coe, smul, denom, slash |
| `peterssonInner_slash_adjoint` | AdjointTheory.lean:616-664 | DS Prop 5.5.2(a) ✓ |
| `diamondOp_petersson_unitary` | AdjointTheory.lean:711 | ⟨d⟩ unitary for petN ✓ |
| `petN_heckeT_p_adjoint_unsymm` | AdjointTheory.lean:822 | T_p adjoint (from core) |
| `heckeT_p_adjoint` | AdjointTheory.lean:909 | The main theorem (reduces to core) |
| `heckeT_n_normal` | AdjointTheory.lean:1018 | T_n T_n* = T_n* T_n |
| `heckeT_n_cusp_preserves_cuspFormCharSpace` | AdjointTheory.lean:1057 | T_n preserves χ-space |
| `heckeT_n_cusp_charRestrict` | AdjointTheory.lean:1083 | T_n restricted to χ-space |
| `petN_add_left'`, `petN_conj_smul_left'` | AdjointTheory.lean:1100-1118 | petN linearity |
| `petN_self_re_nonneg`, `petN_innerProductCore` | AdjointTheory.lean:1123-1145 | Inner product core |
| `heckeT_n_adjoint_on_charSpace` | AdjointTheory.lean:1149 | Adjoint scalar on χ-space |
| `heckeT_n_cusp_isSemisimple_on_charSpace` | AdjointTheory.lean:1209 | Triangularizability |
| `instSMulInvMeasure_GLpos` | PSL2Action.lean:545 | GL₂⁺ preserves μ_hyp ✓ |
| `isFundamentalDomain_fdo_PSL` | PSL2Action.lean:402 | PSL₂ fund domain ✓ |
| `petN_slash_invariant` | PeterssonLevelN.lean:320 | Γ₀(N) invariance of petN ✓ |
| `heckeT_n_comm` | HeckeT_n.lean:1693 | T_m T_n = T_n T_m ✓ (NOT sorry'd!) |
| `heckeT_n_comm_diamondOp` | HeckeT_n.lean:2527 | T_n commutes with ⟨d⟩ ✓ |

### What's sorry'd (4 remaining)

| # | Line | Declaration | Content |
|---|------|-------------|---------|
| 1 | 777 | `petN_slash_adjoint_GL2` | Lift peterssonInner_slash_adjoint to petN |
| 2 | 815 | `petN_heckeT_p_diamond_shift_core` | petN(T_p f, g) = petN(⟨p⟩f, T_p g) |
| 3 | 1010 | `heckeT_n_adjoint` | Composite n case of adjoint induction |
| 4 | 1325 | `exists_simultaneous_eigenform_basis` | Spectral theorem |

## Mathematical Strategy

### Stage 1: IsFundamentalDomain API for Γ₁(N) (T201–T203)

**Goal**: Relate petN to an integral over a Γ₁(N)-fundamental domain, and prove
domain-shift invariance for Γ₁(N)-invariant integrands.

**Key construction**: D_N = ⋃ q : SL₂/Γ₁(N), q.out⁻¹ • fdo (coset tiling).

**Key results**:
- `IsFundamentalDomain (imageGamma1 N) D_N μ_hyp`
- `petN f g = ∫_{D_N} petersson k ⇑f ⇑g ∂μ_hyp`
- `∫_{D} h ∂μ = ∫_{D'} h ∂μ` for any two Γ₁-fund domains, h Γ₁-invariant

**Mathlib**: `IsFundamentalDomain.setIntegral_eq` (FundamentalDomain.lean:411)
gives integral equality between fund domains for invariant functions.

### Stage 2: Core adjoint (T204–T205)

**Sorry #1** (T204): Assembly of Stage 1 + peterssonInner_slash_adjoint:
```
petN(f|α, g) = ∫_{D_N} petersson(f|α, g) = ∫_{α•D_N} petersson(f, g|adj(α))
             = ∫_{D_N} petersson(f, g|adj(α)) = petN(f, g|adj(α))
```
The domain shift α•D_N → D_N uses T203 (requires α normalizing Γ₁(N)).

**Sorry #2** (T205): The hardest step. Two approaches:

*Approach A*: Via T204, apply to the double coset operator [Γ₁αΓ₁] where α = diag(1,p).
Package T_p as a single double coset slash, apply T204, use the identity from T105.

*Approach B*: Direct coset-sum manipulation. Key insight:
```
g ∣[k] adj([1,b;0,p]) = g ∣[k] [p,0;0,1]  for all b
```
(since [p,-b;0,1] = T(-b)·[p,0;0,1] and T(-b) ∈ Γ₁(N) acts trivially on g).
Then [p,0;0,1] = γ₁⁻¹ · [1,0;0,p] · γ₀ (double coset identity from T105), giving
g ∣ adj(α_b) = (g ∣ α_∞) ∣ γ₀. This collapses the b-dependence in the adjoint.

### Stage 3: General adjoint (T206)

**Sorry #3**: Purely algebraic. Strong induction on n:
- n = 1: trivial (T_1 = id, ⟨1⟩ = id)
- n = p prime: heckeT_p_adjoint (from Stage 2)
- n = p^v (v ≥ 2): prime-power recursion T_{p^v} = T_p·T_{p^{v-1}} - p^{k-1}⟨p⟩T_{p^{v-2}}
- n = p^v · m (coprime): T_n = T_{p^v} · T_m, anti-homomorphism (AB)* = B*A*

All supporting lemmas proved: `heckeT_ppow_succ_succ`, `heckeT_n_mul_coprime`,
`heckeT_n_comm_diamondOp`, `diamondOp_petersson_unitary`.

### Stage 4: Spectral theorem (T207)

**Sorry #4**: Mathlib assembly.
1. Joint eigenspace decomposition via `iSup_iInf_maxGenEigenspace_eq_top_of_commute`
2. Basis extraction from finite-dimensional eigenspace decomposition
3. Orthogonality from `heckeT_n_adjoint_on_charSpace`:
   λ_n · petN f g = χ(n)⁻¹ · μ_n · petN f g, so petN f g = 0 when λ ≠ χ⁻¹μ
4. Same-eigenspace orthogonalization via Gram-Schmidt (needs InnerProductSpace instance
   from petN_innerProductCore)

All Mathlib APIs verified available (2026-04-13):
- `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_...` (Eigenspace.Pi)
- `Module.End.iSup_maxGenEigenspace_eq_top` (Eigenspace.Triangularizable)
- `InnerProductSpace.ofCore` (InnerProductSpace.Basic)
- `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces` (JointEigenspace)
- `IsFundamentalDomain.setIntegral_eq` (FundamentalDomain)

## Dependency Graph

```
T201 (IsFundDomain) → T202 (petN = ∫_{D_N}) ┐
         │                                     ├→ T204 (sorry #1)
         └─→ T203 (domain shift) ─────────────┘       │
                                                       ↓
                                               T205 (sorry #2)
                                                       │
                                                       ↓
                                               T206 (sorry #3)
                                                       │
                                                       ↓
                                               T207 (sorry #4) → T208 (cleanup)
```

## Generality Decisions

- **IsFundamentalDomain API**: State for general finite-index Γ ⊂ SL₂(ℤ), not just Γ₁(N)
- **petN domain equality**: State for general Γ-invariant integrands
- **Adjoint formula**: petN_slash_adjoint_GL2 stated for general α ∈ GL₂⁺(ℝ) normalizing Γ
- **Spectral theorem**: Stated for general character χ on (ℤ/Nℤ)ˣ with FiniteDimensional hypothesis
