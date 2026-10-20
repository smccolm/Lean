import Dubon2026.SourcePiTensorBaseChange
import Dubon2026.SourceIntegralGenericFibreAction
import Dubon2026.IntegralInducedTensor

/-! The exact generic fibre of the original embedding tensor.
The tensor of the original factor comparisons is composed with literal
finite tensor scalar extension. Its pure-tensor formula retains every
original coefficient function and the original scalar.
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

/-- The literal generic fibre of the original integral source tensor is the tensor of the original field inductions. -/
def sourceIntegralTensorGenericFibreEquiv :
    K ⊗[R] IntegralInducedTensor R (m + 1) weight ≃ₗ[K]
      IntegralInducedTensor K (m + 1) weight :=
  (sourcePiTensorBaseChangeEquiv R K
    (fun i => Module.Free.chooseBasis R
      (generalLinearIntegralInducedSubmodule R (m + 1) (weight i)))).trans
    (PiTensorProduct.congr fun i => sourceIntegralGenericFibreEquiv R K (weight i) (hw i))

/-- The generic fibre of the original source tensor retains the same actual functions on each pure tensor. -/
theorem sourceIntegralTensorGenericFibreEquiv_tprod (k : K)
    (p : ∀ i, generalLinearIntegralInducedSubmodule R (m + 1) (weight i)) :
    sourceIntegralTensorGenericFibreEquiv R K weight hw (k ⊗ₜ[R] PiTensorProduct.tprod R p) =
      k • PiTensorProduct.tprod K
        (fun i => sourceInducedCoefficientMap R K (m + 1) (weight i) (p i)) := by
  change (PiTensorProduct.congr fun i => sourceIntegralGenericFibreEquiv R K (weight i) (hw i))
    (sourcePiTensorBaseChangeEquiv R K _
      (k ⊗ₜ[R] PiTensorProduct.tprod R p)) = _
  rw [sourcePiTensorBaseChangeEquiv_tprod, map_smul, PiTensorProduct.congr_tprod]
  simp only [sourceIntegralGenericFibreEquiv_tmul, one_smul]

end
end Dubon2026
