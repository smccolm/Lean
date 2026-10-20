import Dubon2026.SourceIntegralTensorGenericFibre
import Dubon2026.IntegralHighestTensor

/-! The original tensor group action through its exact generic-fibre comparison.
Native source tensor bases reduce the linear-operator identity to the
proved actual pure-tensor formula and original factor action comparisons.
-/

namespace Dubon2026
noncomputable section
open Module
open scoped TensorProduct

universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [IsLocalRing R] [CharZero R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
variable {I : Type u} [Finite I] {m : ℕ}
variable (weight : I → Fin (m + 1) → ℤ) (hw : ∀ i, Antitone (weight i))

/-- The original embedding tensor's generic-fibre comparison intertwines every actual tuple of integral matrices, with their literal scalar-extended operators. -/
theorem sourceIntegralTensorGenericFibreEquiv_action
    (g : I → Matrix.GeneralLinearGroup (Fin (m + 1)) R)
    (z : K ⊗[R] IntegralInducedTensor R (m + 1) weight) :
    sourceIntegralTensorGenericFibreEquiv R K weight hw
      ((integralInducedTensorRepresentation R (m + 1) weight g).baseChange K z) =
      integralInducedTensorRepresentation K (m + 1) weight
        (fun i => Matrix.GeneralLinearGroup.map (algebraMap R K) (g i))
          (sourceIntegralTensorGenericFibreEquiv R K weight hw z) := by
  let e := sourceIntegralTensorGenericFibreEquiv R K weight hw
  have he : e.toLinearMap.comp
      ((integralInducedTensorRepresentation R (m + 1) weight g).baseChange K) =
      (integralInducedTensorRepresentation K (m + 1) weight
        (fun i => Matrix.GeneralLinearGroup.map (algebraMap R K) (g i))).comp e.toLinearMap := by
    apply ((integralLocalInducedTensorBasis R weight).baseChange K).ext
    intro j
    have hj : integralLocalInducedTensorBasis R weight j =
        PiTensorProduct.tprod R
          (fun i => Module.Free.chooseBasis R
            (generalLinearIntegralInducedSubmodule R (m + 1) (weight i)) (j i)) :=
      Basis.piTensorProduct_apply _ j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.baseChange_apply]
    rw [hj]
    simp only [LinearMap.baseChange_tmul, integralInducedTensorRepresentation_tprod,
      e, sourceIntegralTensorGenericFibreEquiv_tprod, one_smul,
      sourceInducedCoefficientMap_action]
  exact LinearMap.congr_fun he z

/-- The original tensor generic fibre preserves the actual normalized highest pure tensor. -/
theorem sourceIntegralTensorGenericFibreEquiv_highest :
    sourceIntegralTensorGenericFibreEquiv R K weight hw
      ((1 : K) ⊗ₜ[R] integralHighestTensor R weight hw) =
        integralHighestTensor K weight hw := by
  change sourceIntegralTensorGenericFibreEquiv R K weight hw
    ((1 : K) ⊗ₜ[R] PiTensorProduct.tprod R
      (fun i => integralDominantHighestVector R (weight i) (hw i))) = _
  rw [sourceIntegralTensorGenericFibreEquiv_tprod, one_smul]
  simp only [sourceInducedCoefficientMap_highest, integralHighestTensor]

end
end Dubon2026
