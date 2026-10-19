import Dubon2026.AuxiliaryFixedPowerSeriesComparison
import Dubon2026.PowerSeriesAugmentationScalarComparison

/-! Couple the actual fixed character data with its proved comparison
over the common parameter algebra. This is the ring-specialization
input of DUB-17's existing generic patching theorem, without imposing
any of its still-unproved Hecke-module hypotheses. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

variable (O : Type*) [CommRing O] {R A ι n G η : Type*}
  [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
  [Fintype ι] [Fintype n] [DecidableEq n] [Fintype η]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- The actual fixed-index data and the resulting isomorphism over
its common parameter algebra. This is a constructed output type. -/
def AuxiliaryFixedPowerSeriesPatchingRingComparison : Type _ :=
  Σ d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η,
    let e := auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d
    letI : Algebra (MvPowerSeries η O) R := e.toAlgebra
    letI : Algebra (MvPowerSeries η O) A :=
      ((algebraMap O A).comp MvPowerSeries.constantCoeff).toAlgebra
    (R ⧸ Ideal.map e.toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) ≃ₐ[MvPowerSeries η O] A

/-- Construct the scalar-compatible comparison from the same actual
character family and the proved finite-variable augmentation identity. -/
def auxiliaryFixedPowerSeriesPatchingRingComparisonOfData
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η) :
    AuxiliaryFixedPowerSeriesPatchingRingComparison O (ι := ι) (η := η) Q q τ τ₀ :=
  ⟨d, powerSeriesAugmentationQuotientEquivOverParameters
    (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d)
    (auxiliaryFixedPowerSeriesQuotientEquiv O Q q τ τ₀ d)⟩

/-- Scalar upgrading preserves the exact original quotient map. -/
theorem auxiliaryFixedPowerSeriesPatchingRingComparison_map
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (x : R ⧸ Ideal.map (auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d).toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) :
    (auxiliaryFixedPowerSeriesPatchingRingComparisonOfData O Q q τ τ₀ d).2 x =
      auxiliaryFixedPowerSeriesQuotientEquiv O Q q τ τ₀ d x := rfl

end
end Dubon2026
