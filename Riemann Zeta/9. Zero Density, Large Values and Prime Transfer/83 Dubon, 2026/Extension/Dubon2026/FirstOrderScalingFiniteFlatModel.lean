import Dubon2026.FirstOrderCoefficientScaling
import Dubon2026.FiniteCoefficientExtensionHopfModel
import Dubon2026.MatrixAdicHopfFlatFiniteCoefficients
import Dubon2026.MatrixAdicFiniteFlatSchemeCondition

/-! # Actual local finite-flat models under epsilon scaling and the zero lift -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]

/-- A genuine original finite-flat first-order model is preserved under every actual
epsilon scaling, by the proved finite coefficient-extension model construction. -/
theorem matrixFirstOrderScale_finiteFlatScheme
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (c : k)
    (τ : MatrixFirstOrderLift ρ) (hτ : MatrixAdicFiniteFlatScheme R F K τ.val) :
    MatrixAdicFiniteFlatScheme R F K (matrixFirstOrderScale ρ c τ).val := by
  letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  letI : Fintype (DualNumber k) := Fintype.ofFinite _
  obtain ⟨mτ⟩ := (matrixAdicHopfFlat_finite_iff τ.val).mp
    ((matrixAdicHopfFlat_iff_finiteFlatScheme τ.val).mpr hτ)
  let m := finiteCoefficientExtensionHopfModel (dualNumberEpsilonScale k c) τ.val mτ
  exact (matrixAdicHopfFlat_iff_finiteFlatScheme _).mp (matrixAdicHopfFlat_of_model _ m)

/-- An actual model of the original residual representation constructs a model of
its zero first-order lift through the genuine constant coefficient inclusion. -/
theorem matrixFirstOrderZero_finiteFlatScheme
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
      (matrixUnderlyingGroupAction ρ)) :
    MatrixAdicFiniteFlatScheme R F K (firstOrderLiftFromCocycle ρ 0).val := by
  letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  letI : Fintype (DualNumber k) := Fintype.ofFinite _
  rw [firstOrderLiftFromZero_constant]
  let mzero := finiteCoefficientExtensionHopfModel (algebraMap k (DualNumber k)) ρ m
  exact (matrixAdicHopfFlat_iff_finiteFlatScheme _).mp (matrixAdicHopfFlat_of_model _ mzero)

end
end Dubon2026
