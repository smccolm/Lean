import Dubon2026.CanonicalLocalizedIntegerMaps
import Dubon2026.LocalizedIntegerIntegralClosure
import Dubon2026.LocalizedIntegerRamificationEquivalence

/-! # The canonical localized integer extension and its actual ramification criterion -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- The canonical localized rings inside the original fields form a finite algebra, give the actual integral closure, and are unramified exactly when the remaining original prime indices are one. All coefficient maps and scalar towers are constructed from the original field embedding. -/
theorem canonicalLocalizedIntegerAlgebra_data (a : 𝓞 K) (ha : a ≠ 0) :
    (let Rₐ := originalLocalizedIntegers K a ha
     let Sₐ := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
       (originalIntegerMap_ne_zero (L := L) a ha)
     letI : Algebra Rₐ Sₐ := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
     Module.Finite Rₐ Sₐ ∧ IsIntegralClosure Sₐ Rₐ L ∧
       (Algebra.FormallyUnramified Rₐ Sₐ ↔
         ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
           (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)) := by
  let Rₐ := originalLocalizedIntegers K a ha
  let Sₐ := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  letI : Algebra Rₐ Sₐ := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : IsScalarTower (𝓞 K) Rₐ Sₐ :=
    IsScalarTower.of_algHom (originalLocalizedIntegersMap (L := L) a ha)
  letI : IsScalarTower Rₐ Sₐ L := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact ⟨Module.Finite.of_isLocalization (𝓞 K) (𝓞 L) (.powers a),
    localizedNumberFieldIntegers_isIntegralClosure a ha Rₐ Sₐ,
    numberField_localizedIntegers_unramified_iff a Rₐ Sₐ⟩

end
end Dubon2026
