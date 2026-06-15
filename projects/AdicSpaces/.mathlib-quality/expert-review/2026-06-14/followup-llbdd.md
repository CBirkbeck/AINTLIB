# Follow-up — (LL-bdd) power-boundedness without `IsDomain`

*Prepared 2026-06-14 for the same reviewer. Follow-up to the 2026-06-14 brief on
Wedhorn Thm 8.28(b). Self-contained; uses the same notation (Spa, rational subsets
`R(T/s)`, `𝒪_X(D) = A⟨T/s⟩`, the loc-lift property (LL), case (a)/(b)).*

## Status since your last reply (thank you — the route worked)

Following your Q2 guidance, the **(LL-unit)** half is now **formally proven, sorry-free**:
for `D' ⊆ D` rational, `s_D` is a unit in `𝒪_X(D')`, via your valuative route — the unit
criterion (Wedhorn 7.52(2)) applied through the `Spa(𝒪(D')) ≃ rationalOpen(D')` comparison.
No `IsDomain`, no "`A⁺` a ring of definition". Exactly as you sketched.

One packaging correction we had to make: the formalised unit criterion needs an
auxiliary `A⁺ ⊆ P.A₀` (a ring-of-definition `P` containing `A⁺`). This is available for the
completions in question, so we carry it as a hypothesis `hplus` rather than as an
unconditional typeclass instance. (Our `A⁺` is just a *designated* subring — see the snag
below — so "`A⁺ ⊆ P.A₀`" is not automatic.) This is fine for the application; flagging only
so the asymmetry with your "instance" framing is on the record.

## The (LL-bdd) snag

Your sketch for **(LL-bdd)** was: *for `t ∈ D.T`, every Spa-point `y` of `𝒪_X(D')` pulls
back into `D' ⊆ D`, so `y(t/s) ≤ 1`; hence `t/s` lies in the ring of integral elements of
`𝒪_X(D')` (Wedhorn 7.52(1) / 7.18); and since the plus ring is contained in the
power-bounded subring, `t/s` is power-bounded.*

We get `y(t/s) ≤ 1` on all of `Spa(𝒪_X(D'))` cleanly (same comparison as (LL-unit)). The two
later steps are where we are stuck, and both stem from one fact about our setup:

1. **"plus ⊆ power-bounded" is not available abstractly.** In our formalisation `A⁺` is a
   *designated subring* (the data of an affinoid ring), **without** a built-in axiom that it
   consists of integral / power-bounded elements. So from `t/s ∈ 𝒪_X(D')⁺` we cannot
   conclude `t/s` is power-bounded in general. (We *can* when `𝒪_X(D')⁺` is contained in a
   ring of definition — which again is the `hplus` situation.)

2. **The reverse direction of 7.52(1) requires a domain.** The step "`y(t/s) ≤ 1` for all
   `y ∈ Spa` ⟹ `t/s` is integral" is, in our library, the topology-aware valuative criterion
   (Wedhorn 7.18). Its only proof we have **assumes the ring is an integral domain** — it
   passes to the fraction field and dominates the relevant local subring by a valuation ring
   (à la [Hu2] Lemma 3.3 / Stacks 090P). But `𝒪_X(D')` is a *completion of a localization* —
   **not a domain** in general (case (b)). So the criterion does not apply to it as stated.

So `(LL-bdd)` for a complete strongly-noetherian Tate ring that is **not a domain** is the
genuine gap.

## Questions

**Q-bdd-1 (the core).** For a **complete strongly-noetherian Tate ring `B`** (with `B⁺`) that
is **not an integral domain**, and `x ∈ B` with `v(x) ≤ 1` for every `v ∈ Spa(B, B⁺)`, what is
the cleanest route to *"`x` is power-bounded in `B`"*?

  - Is the standard move to **reduce to the minimal-prime quotients** `B/𝔭ᵢ` (each a complete
    Tate **domain**), apply the domain version of 7.18 / the valuative criterion on each, and
    patch? If so, what is the clean statement that lets one conclude integrality/
    power-boundedness in `B` from integrality in all `B/𝔭ᵢ` (the integral closure does not
    commute with quotients naively, so we want the precise form you would use)?
  - Or is there a **more direct** argument that avoids the integral-Nullstellensatz entirely
    — e.g. showing the lift `σ(t/s)` lands in a **ring of definition** of `𝒪_X(D')` directly
    (it is, after all, the image of the ring-of-definition element `t/s ∈ A₀[T/s] ⊆ 𝒪_X(D)`
    under the restriction map `𝒪_X(D) → 𝒪_X(D')`)? Concretely: does the restriction map of
    structure presheaves send (a) the ring of definition / (b) power-bounded elements of
    `𝒪_X(D)` into power-bounded elements of `𝒪_X(D')`? (A continuous ring homomorphism does
    **not** preserve power-boundedness in general; we are asking whether the *restriction
    maps specifically* do, e.g. because they are adic / bounded.)

**Q-bdd-2 (can we sidestep it for Leaf A?).** In the Remark 7.55 chain
`Spa B ⊇ X₀ ⊇ ⋯ ⊇ Xₙ = im E`, every step `Xᵢ ⊆ Xᵢ₋₁` is a **basic-Laurent** step: the new
numerator lies in a ring of definition `B₀` of the intermediate base. For a numerator
`t ∈ B₀`, power-boundedness of `t` (and of the lift `t/s`) is **easy** in our library —
`t ∈ B₀ ⟹ t` is power-bounded directly, no integral-Nullstellensatz needed (this is exactly
how our already-proven *single basic-Laurent-step* flatness establishes its
power-boundedness hypotheses).

So: **is it legitimate to structure the entire Prop 8.30 / Remark 7.55 argument so that the
(LL-bdd) input is only ever invoked with the numerator in the ring of definition** (the
basic-Laurent case), thereby never needing the general `IsDomain`-free 7.18? Put differently:
does Wedhorn's Remark 7.55 chain *guarantee* that the only power-boundedness facts the proof
of Prop 8.30 consumes are for ring-of-definition numerators — so that the general "every
`y(t/s) ≤ 1` element is power-bounded" statement is **not on the critical path** to 8.28(b)
at all? If yes, we will specialise and skip the deep keystone; if no, we need Q-bdd-1.

## Why this matters for the plan

If **Q-bdd-2 is "yes"**, Leaf A closes using only machinery we already have (the basic-Laurent
power-boundedness + flatness, both proven), plus the (LL-unit) we just landed — no deep
integral-Nullstellensatz. If **"no"**, then Q-bdd-1's `IsDomain`-free 7.18 becomes a required
keystone, and we would value your steer on the minimal-prime-reduction vs direct-restriction
route before we invest in it.
