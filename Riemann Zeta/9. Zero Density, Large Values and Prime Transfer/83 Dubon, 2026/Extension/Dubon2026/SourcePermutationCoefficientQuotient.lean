import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations -> finite permutation coefficients.
The free module on the actual coefficient vectors maps onto the original
representation. Native finite-support linearization gives the equivariance;
no eigenclass, arithmetic action or characteristic-zero lift is assumed.
Hecke-compatible finite-level realization and the adic limit remain required.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G]

/-- The permutation representation on the actual vectors of a coefficient representation. -/
def sourceCoefficientPermutationRep (A : Rep R G) : Rep R G :=
  Rep.of {
    toFun g := Finsupp.lmapDomain R R (A.ρ g)
    map_one' := by ext x r; simp
    map_mul' g h := by ext x r; simp [Module.End.mul_apply] }

/-- Evaluation sends each formal coefficient vector to that same original vector. -/
def sourceCoefficientPermutationEvaluation (A : Rep R G) :
    sourceCoefficientPermutationRep A ⟶ A :=
  Rep.ofHom {
    toLinearMap := Finsupp.linearCombination R (id : A → A)
    isIntertwining' g := by
      ext x
      simp }

/-- The actual vector is the image of its single formal generator. -/
theorem sourceCoefficientPermutationEvaluation_single (A : Rep R G) (x : A) (r : R) :
    sourceCoefficientPermutationEvaluation A (Finsupp.single x r) = r • x := by
  change Finsupp.linearCombination R (id : A → A) (Finsupp.single x r) = r • x
  exact Finsupp.linearCombination_single R r x

/-- Evaluation is onto the original coefficient representation. -/
theorem sourceCoefficientPermutationEvaluation_surjective (A : Rep R G) :
    Function.Surjective (sourceCoefficientPermutationEvaluation A) := by
  intro x
  exact ⟨Finsupp.single x 1, by rw [sourceCoefficientPermutationEvaluation_single, one_smul]⟩

/-- Every actual linear coefficient operator commutes with the corresponding permutation evaluation. -/
theorem sourceCoefficientPermutationEvaluation_linearMap
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (Finsupp.linearCombination R (id : N → N)).comp (Finsupp.lmapDomain R R f) =
      f.comp (Finsupp.linearCombination R (id : M → M)) := by
  ext x
  simp

end
end Dubon2026
