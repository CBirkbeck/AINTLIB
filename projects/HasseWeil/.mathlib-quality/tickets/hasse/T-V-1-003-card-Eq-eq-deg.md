# T-V-1-003: #E(F_q) = deg(1 − π)

**Status**: PARTIAL (witness-parametric form landed)
**Silverman**: V.1 (uses III.4.10c)

**Reviewer-driven plan (2026-05-08)**: closes mechanically once T-II-2-009
+ T-III-4-015 close (the latter is a corollary of the former). Worker B's
target is T-II-2-009 + the elliptic-curve translation bootstrap; the
translation bootstrap then specialises to `1 − π` in this ticket.

If T-II-2-009 stalls, the **pole-divisor route for `γ = 1 − π`
specifically** (per first reviewer response) is the Plan-C fallback. See
T-POLE-DIVISOR-* sub-tickets. That route avoids T-II-2-009 entirely but is
bound-specific (only works for `1 − π`, not general separable isogenies).
**Module**: `HasseWeil/Hasse/PointFix.lean` (witness form); target
`HasseWeil/Hasse/PointCount.lean` (unconditional form)
**Owner**: worker-J
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: F

## Depends on
- T-V-1-001 (E(F_q) = ker(1-π)) — PARTIAL
- T-V-1-002 (1-π separable) — OPEN
- T-III-4-015 (separable ⇒ #ker = deg) — OPEN
- **T-III-4-009 follow-up**: concrete pullback for the isogeny `1 − α` with its
  *true* degree. The current `HasseWeil.isogOneSub` uses `AlgHom.id` as a
  placeholder (see `Endomorphism.lean:71`), so `(isogOneSub α).degree = 1`
  identically, which makes the current `pointCount_eq` statement evaluate to
  `pointCount = 1` (false).
- Alternatively uses dual isogeny machinery (T-III-6-001..008, BLOCKED/OPEN)
  via the Silverman V.1.2 expansion
  `deg(1−π) = (1−π̂)(1−π) = 1 − tr(π) + q`.

## Blocks
- T-V-1-004 (point count formula)

## Statement (Silverman V.1)
For `E/F_q`, `#E(F_q) = deg(1 − π)`.

## Acceptance criteria

```lean
namespace HasseWeil.Hasse

theorem card_Fq_eq_degree_one_minus_frobenius
    (E : WeierstrassCurve (ZMod p)) [Fact p.Prime] [Fact (E.Δ ≠ 0)]
    (q : ℕ) (hq : q = p^k) :
    Fintype.card (E.toAffine.Point) = (E.mulByInt 1 - (E.mulByInt 1).comp (E.frobeniusIsogeny q)).degree

end HasseWeil.Hasse
```

## Notes
- Combine T-V-1-001 (points = kernel) with T-III-4-015 (#ker = deg for
  separable) and T-V-1-002 (1-π is separable).
- The current implementation at `HasseWeil/Frobenius.lean:94-100` is
  `pointCount_eq` but is STATED in terms of the placeholder
  `oneSubFrobeniusIsog := isogOneSub (frobeniusIsog W)`. Under the placeholder,
  the theorem is false. See the docstring there for a detailed account of the
  blocker and two possible unblockings:
    1. Close `AdditionPullback.lean` so `isogOneSub` can carry a genuine pullback
       reflecting `1 − π` on function fields, with `.degree` matching `#ker`.
    2. Restate `pointCount_eq` to take a witness `β : Isogeny E E` together with
       `hβ_hom` (group-hom agreement with `id − π`) and `hβ_deg` (β.degree =
       pointCount), mirroring the `degree_quadratic_nonneg` design in
       `DegreeQuadraticForm.lean`.

## Progress log
- 2026-04-17 [auto] Reviewed `Frobenius.lean:100` sorry. Status upgraded from
  PARTIAL → BLOCKED. Not closable with current placeholder `isogOneSub`.
  Docstring on `pointCount_eq` expanded with the diagnosis and two unblocking
  paths. No proof change.
- 2026-04-20 [worker-J] Witness-parametric form `degree_eq_pointCount_of_witness`
  added to `HasseWeil/Hasse/PointFix.lean`: given a witness isogeny `β` with
  `β.toAddMonoidHom = id − π.toAddMonoidHom` and `Nat.card β.kernel = β.degree`
  (the T-III-4-015 content for `β`), concludes `β.degree = pointCount`.
  Also `kernel_eq_top_of_hom_eq_id_sub_frobenius` (β.kernel = ⊤). Axiom-hygienic
  (standard only). Status BLOCKED → PARTIAL. Unconditional form still requires
  the `isogOneSub` placeholder replacement + T-III-4-015.
