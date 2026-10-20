import Dubon2026.IntegralHighestWeightAction
import Dubon2026.IntegralInducedTensor
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-! The actual highest vector in the original embedding tensor.
Evaluation at the longest matrix supplies each factor's actual dual
functional with value one. Native tensor duality proves the original
pure tensor nonzero without an assumed basis or irreducibility. Its
character is the exact product of the original highest-weight characters.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped TensorProduct

universe u
variable (R : Type u) [CommRing R] {n : ℕ}

/-- Evaluation at the actual longest matrix as a linear functional on the original induced module. -/
def integralHighestEvaluation (lam : Fin (n + 1) → ℤ) :
    generalLinearIntegralInducedSubmodule R (n + 1) lam →ₗ[R] R :=
  (generalLinearRegularEval (integralWeightLongest R (n + 1))).toLinearMap.comp
    (generalLinearIntegralInducedSubmodule R (n + 1) lam).subtype

/-- The original highest vector is normalized to one by the actual longest-matrix evaluation. -/
theorem integralHighestEvaluation_vector (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    integralHighestEvaluation R lam (integralDominantHighestVector R lam hlam) = 1 :=
  integralDominantHighestRegular_longest R lam

variable {I : Type u} [Finite I] (lam : I → Fin (n + 1) → ℤ) (hlam : ∀ i, Antitone (lam i))

/-- The original highest pure tensor, using the actual highest vectors of its literal induced factors. -/
def integralHighestTensor : IntegralInducedTensor R (n + 1) lam :=
  PiTensorProduct.tprod R (fun i => integralDominantHighestVector R (lam i) (hlam i))

/-- The actual tensor of longest-matrix evaluations, as a functional on the original coefficient tensor. -/
def integralHighestTensorEvaluation : IntegralInducedTensor R (n + 1) lam →ₗ[R] R :=
  PiTensorProduct.dualDistrib (PiTensorProduct.tprod R (fun i => integralHighestEvaluation R (lam i)))

/-- Native tensor duality gives normalization one for the actual source highest tensor. -/
theorem integralHighestTensorEvaluation_vector :
    integralHighestTensorEvaluation R lam (integralHighestTensor R lam hlam) = 1 := by
  letI := Fintype.ofFinite I
  have h := PiTensorProduct.dualDistrib_apply
    (fun i => integralHighestEvaluation R (lam i))
    (fun i => integralDominantHighestVector R (lam i) (hlam i))
  simpa only [integralHighestEvaluation_vector, Finset.prod_const_one] using h

/-- The actual highest tensor is nonzero over every nontrivial original coefficient ring. -/
theorem integralHighestTensor_ne_zero [Nontrivial R] : integralHighestTensor R lam hlam ≠ 0 := by
  intro h
  have he := integralHighestTensorEvaluation_vector R lam hlam
  rw [h, map_zero] at he
  exact zero_ne_one he

omit [Finite I] in
/-- The original coefficient tensor action has precisely the product of original highest-weight characters on its constructed highest vector. -/
theorem integralHighestTensor_action [Fintype I] (b : I → generalLinearBorel R (n + 1)) :
    integralInducedTensorRepresentation R (n + 1) lam (fun i => (b i).val)
      (integralHighestTensor R lam hlam) =
      (∏ i : I, ((∏ j : Fin (n + 1), generalLinearBorelDiagonalUnit (b i) j ^ lam i j : Rˣ) : R)) •
        integralHighestTensor R lam hlam := by
  change integralInducedTensorRepresentation R (n + 1) lam (fun i => (b i).val)
      (PiTensorProduct.tprod R (fun i => integralDominantHighestVector R (lam i) (hlam i))) = _
  rw [integralInducedTensorRepresentation_tprod]
  simp_rw [integralDominantHighestVector_action]
  exact (PiTensorProduct.tprod R).map_smul_univ _ _

end
end Dubon2026
