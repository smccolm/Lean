import Dubon2026.FirstOrderCoefficientAddition
import Dubon2026.MatrixFiberProductHopfModel
import Dubon2026.FiniteCoefficientExtensionHopfModel
import Dubon2026.MatrixAdicHopfFlatFiniteCoefficients
import Dubon2026.MatrixAdicFiniteFlatSchemeCondition

/-! # Genuine finite-flat models are preserved by original first-order addition -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]

/-- Genuine local finite-flat first-order models are closed under the actual
addition of deformations. Construct the model over compatible dual-number pairs
from the two original models, then transport it through the actual epsilon-addition
coefficient map. Every original positive adic level is preserved. -/
theorem matrixFirstOrderSum_finiteFlatScheme
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k)
    (τ υ : MatrixFirstOrderLift ρ)
    (hτ : MatrixAdicFiniteFlatScheme R F K τ.val)
    (hυ : MatrixAdicFiniteFlatScheme R F K υ.val) :
    MatrixAdicFiniteFlatScheme R F K (matrixFirstOrderSum ρ τ υ).val := by
  letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  letI : Fintype (DualNumber k) := Fintype.ofFinite _
  obtain ⟨mτ⟩ := (matrixAdicHopfFlat_finite_iff τ.val).mp
    ((matrixAdicHopfFlat_iff_finiteFlatScheme τ.val).mpr hτ)
  obtain ⟨mυ⟩ := (matrixAdicHopfFlat_finite_iff υ.val).mp
    ((matrixAdicHopfFlat_iff_finiteFlatScheme υ.val).mpr hυ)
  let f := (TrivSqZeroExt.fstHom k k k).toRingHom
  let t := matrixFirstOrderPair ρ τ υ
  have hp := coefficientFiberProductRepresentation_projections f f τ.val υ.val
    (τ.property.trans υ.property.symm)
  change ((GeneralLinearGroup.map (coefficientFiberProductFst f f)).comp t = τ.val) ∧
    ((GeneralLinearGroup.map (coefficientFiberProductSnd f f)).comp t = υ.val) at hp
  have mA : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → DualNumber k))
      (matrixUnderlyingGroupAction
        ((GeneralLinearGroup.map (coefficientFiberProductFst f f)).comp t)) := by
    rw [hp.1]
    exact mτ
  have mB : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K
      (Multiplicative (ι → DualNumber k))
      (matrixUnderlyingGroupAction
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f f)).comp t)) := by
    rw [hp.2]
    exact mυ
  let m := matrixFiberProductHopfModel f f t mA mB
  let msum := finiteCoefficientExtensionHopfModel (dualNumberCompatibleAddition k) t m
  exact (matrixAdicHopfFlat_iff_finiteFlatScheme _).mp
    (matrixAdicHopfFlat_of_model _ msum)

end
end Dubon2026
