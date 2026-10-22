import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
The raw 2g-loop reciprocity matrix gives the regular-period image as a kernel.
Rank-nullity and the bilinear relation suffice; a symplectic normal form is
unnecessary. The geometric reciprocity and generation theorems remain upstream.
-/
namespace Dubon2026.SourceFunctionField.PeriodCorrection
noncomputable section
open Matrix

theorem period_range_eq_reciprocity_kernel {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : Function.Injective A.mulVecLin) (hQ : IsUnit Q.det)
    (hRR : (A.transpose * Q) * A = 0) :
    LinearMap.range A.mulVecLin = LinearMap.ker (A.transpose * Q).mulVecLin := by
  have hrA : Module.finrank ℂ (LinearMap.range A.mulVecLin) = n := by
    simpa using LinearMap.finrank_range_of_inj hA
  have hrB : Module.finrank ℂ (LinearMap.range (A.transpose * Q).mulVecLin) = n := by
    change (A.transpose * Q).rank = n
    rw [rank_mul_eq_left_of_isUnit_det Q A.transpose hQ, rank_transpose]
    exact hrA
  have hd := (A.transpose * Q).mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_sum,
    Fintype.card_fin, hrB] at hd
  apply Submodule.eq_of_le_of_finrank_eq
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul, hRR, Matrix.mulVecLin_zero]
  · omega

theorem exists_period_correction_of_reciprocity_kernel {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : Function.Injective A.mulVecLin) (hQ : IsUnit Q.det)
    (hRR : (A.transpose * Q) * A = 0)
    (v : Fin n ⊕ Fin n → ℂ) (hv : (A.transpose * Q).mulVec v = 0) :
    ∃ c : Fin n → ℂ, A.mulVec c = v := by
  have hm : v ∈ LinearMap.ker (A.transpose * Q).mulVecLin := hv
  rw [← period_range_eq_reciprocity_kernel A Q hA hQ hRR] at hm
  exact hm

end
end Dubon2026.SourceFunctionField.PeriodCorrection
