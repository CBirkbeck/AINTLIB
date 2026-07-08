import Mathlib

open CategoryTheory Abelian Limits ModuleCat
open scoped ModuleCat.Algebra

namespace ModuleCat.BaseChangeExt

variable {S : Type} [CommRing S] (𝔪 : Submonoid S)

/-- The localization functor is `S`-linear. -/
instance functorLinear : (ModuleCat.localizedModuleFunctor.{0} 𝔪).Linear S where
  map_smul {M N} f s := by
    ext x
    simp [ModuleCat.localizedModuleMap]

end ModuleCat.BaseChangeExt

/-- Flat base change for Ext: localizing the Ext module commutes with computing Ext over the
localization. -/
theorem localizedModule_ext_subsingleton_iff {S : Type} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (q : PrimeSpectrum S) (i : ℕ) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl
        (Ext (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i))
      ↔ Subsingleton (Ext
          (ModuleCat.of (Localization q.asIdeal.primeCompl)
            (Localization q.asIdeal.primeCompl ⧸ I.map (algebraMap S (Localization q.asIdeal.primeCompl))))
          (ModuleCat.of (Localization q.asIdeal.primeCompl) (Localization q.asIdeal.primeCompl)) i) := by
  sorry
