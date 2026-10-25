import Dubon2026.SourcePrimitiveGoodAnnihilator
import Dubon2026.SourcePolynomialKernelProjectionLaws
import Dubon2026.SourceSymmetricKernelReduction

/-! DUB-17/18 -> primitive Frobenius determinant -> actual primitive
component. Finite good-prime multiplicity one and Petersson positivity
produce an idempotent polynomial in the actual good Hecke annihilator,
with range precisely the prescribed primitive cusp line. Coefficient-field
and original Tate transport remain separate obligations. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2

theorem exists_primitive_good_polynomial_projection (f : PrimitiveCuspForm N 2) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N}) (P : ℂ[X]),
      P.eval 0 = 1 ∧
      primitiveGoodAnnihilator N f s * aeval (primitiveGoodAnnihilator N f s) P = 0 ∧
      LinearMap.range (aeval (primitiveGoodAnnihilator N f s) P) =
        Submodule.span ℂ {f.toCuspForm} ∧
      IsIdempotentElem (aeval (primitiveGoodAnnihilator N f s) P) := by
  letI : FiniteDimensional ℂ S := ModularDimension.cuspForm_finiteDimensional (Gamma0 N) 2
  letI := cuspPeterssonCore N 2
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := S)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N 2).toCore
  obtain ⟨s, hsym, hker⟩ := exists_primitive_good_annihilator N f
  obtain ⟨P, hP, hHP⟩ := exists_kernel_projector_polynomial
    (primitiveGoodAnnihilator N f s)
    (symmetric_apply_eq_zero_of_square _ hsym)
  refine ⟨s, P, hP, hHP, ?_, kernel_projector_polynomial_idempotent _ P hP hHP⟩
  exact (kernel_projector_polynomial_range _ P hP hHP).trans hker

end
end Dubon2026
