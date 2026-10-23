import Dubon2026.SourceWeightTwoHeckePerfectPairing

/-! DUB-17/18 -> rank-two Hecke descent -> a cusp basis dual to the
actual integral Hecke algebra. The already proved perfect pairing
identifies cusp forms with the dual full Hecke algebra. Operator action
becomes precomposition by multiplication, giving integral cusp matrices
once the algebra basis is chosen from its integral lattice.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Gamma0 N) 2
local notation "A" => sourceWeightTwoFullHeckeAlgebra N

theorem sourceWeightTwoHeckePairing_flip_bijective :
    Function.Bijective (sourceWeightTwoHeckePairing N).flip := by
  letI := SourceFunctionField.original_weight_two_cusp_finite N
  letI := sourceWeightTwoFullHeckeAlgebra_finite N
  refine ⟨sourceWeightTwoHeckePairing_flip_injective N, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℂ S = Module.finrank ℂ (Module.Dual ℂ A) by
      rw [Subspace.dual_finrank_eq, sourceWeightTwoFullHeckeAlgebra_finrank N])).mp
  exact sourceWeightTwoHeckePairing_flip_injective N

/-- The faithful first-coefficient pairing, oriented from cusp forms to algebra duals. -/
def sourceWeightTwoCuspHeckeDualEquiv : S ≃ₗ[ℂ] Module.Dual ℂ A :=
  LinearEquiv.ofBijective (sourceWeightTwoHeckePairing N).flip
    (sourceWeightTwoHeckePairing_flip_bijective N)

theorem sourceWeightTwoCuspHeckeDualEquiv_apply (f : S) (T : A) :
    sourceWeightTwoCuspHeckeDualEquiv N f T = cuspCoefficients (T.val f) 1 := rfl

theorem sourceWeightTwoCuspHeckeDualEquiv_operator (f : S) (T U : A) :
    sourceWeightTwoCuspHeckeDualEquiv N (T.val f) U =
      sourceWeightTwoCuspHeckeDualEquiv N f (U * T) := rfl

end
end Dubon2026
