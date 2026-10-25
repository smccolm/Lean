import Dubon2026.SourceKernelPowerReduction
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> primitive projector. A native finite-dimensional
annihilator and the proved zero-power reduction construct a polynomial
which is one at zero and whose operator image lies in the actual kernel.
No diagonalization or projector is assumed. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_kernel_projector_polynomial_of_isIntegral (H : Module.End K V)
    (hI : IsIntegral K H)
    (hH : ∀ x, H (H x) = 0 → H x = 0) :
    ∃ P : K[X], P.eval 0 = 1 ∧ H * aeval H P = 0 := by
  obtain ⟨P, hP, hPH⟩ := hI
  change aeval H P = 0 at hPH
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP.ne_zero 0
  have hQ0 : Q.eval 0 ≠ 0 := by
    simpa only [map_zero, sub_zero, X_dvd_iff, coeff_zero_eq_eval_zero] using hQ
  have hHQ : H * aeval H Q = 0 := by
    apply LinearMap.ext
    intro x
    apply end_pow_zero_implies_apply_zero H hH (P.rootMultiplicity 0)
    rw [hPQ] at hPH
    have he := congrArg (fun T : Module.End K V => T x) hPH
    simpa only [map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero,
      sub_zero, Module.End.mul_apply, LinearMap.zero_apply] using he
  refine ⟨C (Q.eval 0)⁻¹ * Q, ?_, ?_⟩
  · simp only [eval_mul, eval_C, inv_mul_cancel₀ hQ0]
  · rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, hHQ, smul_zero]

theorem exists_kernel_projector_polynomial [FiniteDimensional K V] (H : Module.End K V)
    (hH : ∀ x, H (H x) = 0 → H x = 0) :
    ∃ P : K[X], P.eval 0 = 1 ∧ H * aeval H P = 0 :=
  exists_kernel_projector_polynomial_of_isIntegral H
    (LinearMap.exists_monic_and_aeval_eq_zero K H) hH

end
end Dubon2026
