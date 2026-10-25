import Dubon2026.SourcePolynomialKernelProjection

/-! DUB-17/18 -> arithmetic primitive projector. Root factorization takes
place over the coefficient field; only polynomial evaluation is mapped to
the complex operator space. Thus the resulting projector retains its actual
arithmetic coefficients for the original Tate comparison. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {K L V : Type*} [Field K] [Field L] [AddCommGroup V] [Module L V]

theorem exists_mapped_kernel_projector_polynomial (ι : K →+* L) (H : Module.End L V)
    (P : K[X]) (hP : P.Monic) (hPH : aeval H (P.map ι) = 0)
    (hH : ∀ x, H (H x) = 0 → H x = 0) :
    ∃ Q : K[X], Q.eval 0 = 1 ∧ H * aeval H (Q.map ι) = 0 := by
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP.ne_zero 0
  have hQ0 : Q.eval 0 ≠ 0 := by
    simpa only [map_zero, sub_zero, X_dvd_iff, coeff_zero_eq_eval_zero] using hQ
  have hHQ : H * aeval H (Q.map ι) = 0 := by
    apply LinearMap.ext
    intro x
    apply end_pow_zero_implies_apply_zero H hH (P.rootMultiplicity 0)
    rw [hPQ] at hPH
    have he := congrArg (fun T : Module.End L V => T x) hPH
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, map_mul, map_pow, map_sub, aeval_X,
      aeval_C, map_zero, sub_zero, Module.End.mul_apply, LinearMap.zero_apply] using he
  refine ⟨C (Q.eval 0)⁻¹ * Q, ?_, ?_⟩
  · simp only [eval_mul, eval_C, inv_mul_cancel₀ hQ0]
  · rw [Polynomial.map_mul, Polynomial.map_C, map_mul, aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, hHQ, smul_zero]

end
end Dubon2026
