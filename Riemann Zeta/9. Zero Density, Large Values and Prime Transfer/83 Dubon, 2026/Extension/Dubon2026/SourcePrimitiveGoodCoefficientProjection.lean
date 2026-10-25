import Dubon2026.SourcePrimitiveGoodCoefficientAnnihilator
import Dubon2026.SourceMappedKernelProjection
import Dubon2026.SourcePolynomialKernelProjectionLaws
import Dubon2026.SourceSymmetricKernelReduction

/-! DUB-17/18 -> primitive determinant -> arithmetic primitive component.
The actual projector polynomial is now defined over the literal Fourier
coefficient field. Its complex realization has exactly the primitive line
as its range. Original Tate transport is still a separate obligation. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2

theorem exists_primitive_good_coefficient_projection (f : PrimitiveCuspForm N 2) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : Polynomial (sourcePrimitiveCoefficientField f)),
      P.eval 0 = 1 ∧
      primitiveGoodAnnihilator N f s * aeval (primitiveGoodAnnihilator N f s)
        (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ)) = 0 ∧
      LinearMap.range (aeval (primitiveGoodAnnihilator N f s)
        (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ))) =
        Submodule.span ℂ {f.toCuspForm} ∧
      IsIdempotentElem (aeval (primitiveGoodAnnihilator N f s)
        (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ))) := by
  letI := cuspPeterssonCore N 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := S)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N 2).toCore
  obtain ⟨s, hsym, hker⟩ := exists_primitive_good_annihilator N f
  obtain ⟨R, hR, hRH⟩ := primitiveGoodAnnihilator_coefficient_polynomial N f s
  obtain ⟨P, hP, hHP⟩ := exists_mapped_kernel_projector_polynomial
    (algebraMap (sourcePrimitiveCoefficientField f) ℂ) (primitiveGoodAnnihilator N f s)
    R hR hRH (symmetric_apply_eq_zero_of_square _ hsym)
  have hP' : (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ)).eval 0 = 1 := by
    rw [eval_zero_map, hP, map_one]
  exact ⟨s, P, hP, hHP, (kernel_projector_polynomial_range _ _ hP' hHP).trans hker,
    kernel_projector_polynomial_idempotent _ _ hP' hHP⟩

end
end Dubon2026
