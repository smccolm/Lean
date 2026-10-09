import Dubon2026.UniversalMatrixPolynomial
import Dubon2026.HomogeneousFiniteSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Every original homogeneous matrix coefficient is a genuine polynomial -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every actual linear functional of an original homogeneous orbit is a genuine polynomial in the original matrix entries. -/
theorem homogeneousMatrixCoefficient_polynomial (n : ℕ)
    (p : homogeneousSubmodule (Fin 2) ℂ n) (L : homogeneousSubmodule (Fin 2) ℂ n →ₗ[ℂ] ℂ) :
    ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ a : Matrix (Fin 2) (Fin 2) ℂ,
      L (homogeneousMatrixAction n a p) = MvPolynomial.eval (fun ij => a ij.1 ij.2) q := by
  let C : (Fin 2 →₀ ℕ) → homogeneousSubmodule (Fin 2) ℂ n →ₗ[ℂ] ℂ :=
    fun d => (MvPolynomial.lcoeff ℂ d).comp (homogeneousSubmodule (Fin 2) ℂ n).subtype
  have hm : L ∈ Submodule.span ℂ (Set.range C) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have hz : v = 0 := by
      apply Subtype.ext
      apply MvPolynomial.ext
      intro d
      have hd := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv d)
      simpa only [Submodule.coe_zero, MvPolynomial.coeff_zero] using hd
    rw [hz]
    exact LinearMap.mem_ker.mpr (map_zero L)
  induction hm using Submodule.span_induction with
  | mem K hK =>
      obtain ⟨d, rfl⟩ := hK
      exact ⟨matrixCoefficientPolynomial p.val d, fun a => (matrixCoefficientPolynomial_eval p.val d a).symm⟩
  | zero => exact ⟨0, fun a => by simp⟩
  | add K L _ _ hK hL =>
      obtain ⟨q, hq⟩ := hK
      obtain ⟨r, hr⟩ := hL
      exact ⟨q + r, fun a => by simp only [LinearMap.add_apply, map_add, hq, hr]⟩
  | smul c K _ hK =>
      obtain ⟨q, hq⟩ := hK
      exact ⟨MvPolynomial.C c * q, fun a => by simp only [LinearMap.smul_apply, smul_eq_mul, hq, map_mul, MvPolynomial.eval_C]⟩

end
end Dubon2026
