import Dubon2026.SourceWeightTwoFullHeckeAlgebra

/-! DUB-17/18 -> rank-two Hecke decomposition -> the faithful first
Fourier-coefficient pairing. The full original algebra and cusp forms
separate one another by the already proved all-index coefficient formula.
Finite dimension makes the pairing perfect. This discharges both the
operator-separation and equal-dimension inputs in the rank-two route.
The pairing argument also appears in anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CuspForm_finrank_span_heckeAlgebra_eq_finrank. Here the original native
all-index Hecke formula supplies separation without a new Fourier induction.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Gamma0 N) 2
local notation "A" => sourceWeightTwoFullHeckeAlgebra N

/-- First coefficient of the genuine operator applied to a cusp form. -/
def sourceWeightTwoHeckePairing : A →ₗ[ℂ] Module.Dual ℂ S where
  toFun T := (cuspCoefficientLinear N 2 1).comp T.val
  map_add' T U := LinearMap.comp_add T.val U.val (cuspCoefficientLinear N 2 1)
  map_smul' c T := LinearMap.comp_smul _ c T.val

theorem sourceWeightTwoHeckePairing_apply (T : A) (f : S) :
    sourceWeightTwoHeckePairing N T f = cuspCoefficients (T.val f) 1 := rfl

theorem sourceWeightTwoHeckePairing_injective :
    Function.Injective (sourceWeightTwoHeckePairing N) := by
  rw [injective_iff_map_eq_zero]
  intro T hT
  apply Subtype.ext
  apply sourceWeightTwoFullHecke_operator_separated N T.val T.property
  intro f
  exact congrArg (fun L : Module.Dual ℂ S => L f) hT

theorem sourceWeightTwoHeckePairing_flip_injective :
    Function.Injective (sourceWeightTwoHeckePairing N).flip := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply sourceWeightTwoFullHecke_form_separated N f
  intro T hT
  exact congrArg (fun L : Module.Dual ℂ A => L ⟨T, hT⟩) hf

theorem sourceWeightTwoFullHeckeAlgebra_finrank :
    Module.finrank ℂ A = Module.finrank ℂ S := by
  letI := SourceFunctionField.original_weight_two_cusp_finite N
  letI := sourceWeightTwoFullHeckeAlgebra_finite N
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective
      (sourceWeightTwoHeckePairing_injective N)
    rwa [Subspace.dual_finrank_eq] at h
  · have h := LinearMap.finrank_le_finrank_of_injective
      (sourceWeightTwoHeckePairing_flip_injective N)
    rwa [Subspace.dual_finrank_eq] at h

theorem sourceWeightTwoHeckePairing_bijective :
    Function.Bijective (sourceWeightTwoHeckePairing N) := by
  letI := SourceFunctionField.original_weight_two_cusp_finite N
  letI := sourceWeightTwoFullHeckeAlgebra_finite N
  refine ⟨sourceWeightTwoHeckePairing_injective N, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℂ A = Module.finrank ℂ (Module.Dual ℂ S) by
      rw [Subspace.dual_finrank_eq, sourceWeightTwoFullHeckeAlgebra_finrank N])).mp
  exact sourceWeightTwoHeckePairing_injective N

/-- Every cusp linear functional is first-coefficient evaluation after an actual Hecke-algebra operator. -/
def sourceWeightTwoHeckeDualEquiv : A ≃ₗ[ℂ] Module.Dual ℂ S :=
  LinearEquiv.ofBijective (sourceWeightTwoHeckePairing N) (sourceWeightTwoHeckePairing_bijective N)

theorem sourceWeightTwoHeckeDualEquiv_apply (T : A) (f : S) :
    sourceWeightTwoHeckeDualEquiv N T f = cuspCoefficients (T.val f) 1 := rfl

end
end Dubon2026
