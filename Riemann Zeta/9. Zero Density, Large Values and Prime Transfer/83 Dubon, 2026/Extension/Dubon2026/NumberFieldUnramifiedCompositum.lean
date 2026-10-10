import Dubon2026.CanonicalLocalizedIntegerAlgebras
import Dubon2026.UnramifiedCompositumIntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Original number-field ramification is preserved by actual finite composita -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable {K L M Ω : Type*} [Field K] [Field L] [Field M] [Field Ω]
  [NumberField K] [NumberField L] [NumberField M] [NumberField Ω]
  [Algebra K L] [Algebra K M] [Algebra K Ω] [Algebra L Ω] [Algebra M Ω]
  [IsScalarTower K L Ω] [IsScalarTower K M Ω]

/-- Every original prime away from the exceptional integer remains unramified in the actual field compositum of two original number-field extensions unramified there. -/
theorem numberField_unramified_compositum (a : 𝓞 K) (ha : a ≠ 0)
    (hL : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hM : ∀ w : HeightOneSpectrum (𝓞 M), algebraMap (𝓞 K) (𝓞 M) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (htop : (algebraMap L Ω).fieldRange ⊔ (algebraMap M Ω).fieldRange = ⊤) :
    ∀ w : HeightOneSpectrum (𝓞 Ω), algebraMap (𝓞 K) (𝓞 Ω) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let Rₐ := originalLocalizedIntegers K a ha
  let A := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  let B := originalLocalizedIntegers M (algebraMap (𝓞 K) (𝓞 M) a)
    (originalIntegerMap_ne_zero (L := M) a ha)
  let C := originalLocalizedIntegers Ω (algebraMap (𝓞 K) (𝓞 Ω) a)
    (originalIntegerMap_ne_zero (L := Ω) a ha)
  letI : Algebra Rₐ A := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : Algebra Rₐ B := (originalLocalizedIntegersMap (L := M) a ha).toRingHom.toAlgebra
  letI : Algebra Rₐ C := (originalLocalizedIntegersMap (L := Ω) a ha).toRingHom.toAlgebra
  letI : IsScalarTower Rₐ A Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply K L Ω x.val
  letI : IsScalarTower Rₐ B Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply K M Ω x.val
  letI : IsScalarTower Rₐ C Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hA := canonicalLocalizedIntegerAlgebra_data (L := L) a ha
  have hB := canonicalLocalizedIntegerAlgebra_data (L := M) a ha
  have hC := canonicalLocalizedIntegerAlgebra_data (L := Ω) a ha
  letI : Module.Finite Rₐ A := hA.1
  letI : Module.Finite Rₐ B := hB.1
  letI : Algebra.FormallyUnramified Rₐ A := hA.2.2.mpr hL
  letI : Algebra.FormallyUnramified Rₐ B := hB.2.2.mpr hM
  letI : IsIntegralClosure C Rₐ Ω := hC.2.1
  letI : IsDedekindDomain Rₐ := IsLocalization.isDedekindDomain (𝓞 K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha) Rₐ
  let f : A →ₐ[Rₐ] Ω := IsScalarTower.toAlgHom Rₐ A Ω
  let g : B →ₐ[Rₐ] Ω := IsScalarTower.toAlgHom Rₐ B Ω
  have hi : (algebraMap L Ω).comp (algebraMap A L) = f.toRingHom := by
    ext x
    rfl
  have hj : (algebraMap M Ω).comp (algebraMap B M) = g.toRingHom := by
    ext x
    rfl
  exact hC.2.2.mp (integralClosure_formallyUnramified_of_compositum_top
    f g (algebraMap L Ω) (algebraMap M Ω) hi hj htop C)

end
end Dubon2026
