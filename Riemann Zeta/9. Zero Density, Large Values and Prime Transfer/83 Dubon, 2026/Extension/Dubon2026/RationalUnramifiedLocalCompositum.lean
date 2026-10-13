import Dubon2026.RationalPrimeLocalizedIntegerUnits
import Dubon2026.CanonicalLocalizedIntegerAlgebras
import Dubon2026.BaseChangedUnramifiedIntegralClosure
import Dubon2026.LocalFieldIntegerIntegralClosure

/-! # Original arithmetic unramifiedness passes to the actual local compositum

The actual localized integer coefficient map and the already proved unramified
base-change integral-closure theorem give this passage. It is the missing
field-level edge before DUB-17's unramified H2 vanishing supplies local support.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel nonZeroDivisors

variable (L M : Type) [Field L] [NumberField L] [Field M] [Algebra ℚ L]
  (p : ℕ) (hp : p.Prime)
  [Algebra (rationalPrimeLocalField p hp) M] [Algebra ℚ M] [Algebra L M]
  [IsScalarTower ℚ (rationalPrimeLocalField p hp) M] [IsScalarTower ℚ L M]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]

/-- A number-field extension unramified away from the original exceptional
integer gives an unramified actual local compositum at each prime not dividing
that integer. Its local integer unramifiedness is derived by actual base change. -/
theorem rationalUnramifiedLocalCompositum_integer_unramified
    (a : 𝓞 ℚ) (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (hL : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 ℚ) (𝓞 L) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1)
    (htop : (algebraMap (rationalPrimeLocalField p hp) M).fieldRange ⊔
      (algebraMap L M).fieldRange = ⊤) :
    Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp] 𝒪[M] := by
  let E := rationalPrimeLocalField p hp
  let R := originalLocalizedIntegers ℚ a ha
  let S := originalLocalizedIntegers L (algebraMap (𝓞 ℚ) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  let fR := originalLocalizedIntegerToValuationIntegerMap ℚ E a ha
    (rationalPrimeOriginalInteger_isUnit p hp a hpa)
  letI : Algebra R S := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : Algebra R 𝒪[E] := fR.toAlgebra
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply ℚ L M (x : ℚ)
  haveI : IsScalarTower R 𝒪[E] M := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap ℚ M (x : ℚ) = algebraMap E M (fR x : E)
    rw [originalLocalizedIntegerToValuationIntegerMap_coe]
    exact IsScalarTower.algebraMap_apply ℚ E M (x : ℚ)
  have hS := canonicalLocalizedIntegerAlgebra_data (L := L) a ha
  haveI : Module.Finite R S := hS.1
  haveI : Algebra.FormallyUnramified R S := hS.2.2.mpr hL
  haveI : IsFractionRing S L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (algebraMap (𝓞 ℚ) (𝓞 L) a)) S L
  haveI : IsIntegralClosure 𝒪[M] 𝒪[E] M := localField_integer_isIntegralClosure
  let f : S →ₐ[R] M := IsScalarTower.toAlgHom R S M
  apply integralClosure_formallyUnramified_of_baseChange_compositum_top
    f (algebraMap E M) (algebraMap L M) _ _ htop 𝒪[M]
  · ext x
    exact (IsScalarTower.algebraMap_apply 𝒪[E] E M x).symm
  · ext x
    rfl

end
end Dubon2026
