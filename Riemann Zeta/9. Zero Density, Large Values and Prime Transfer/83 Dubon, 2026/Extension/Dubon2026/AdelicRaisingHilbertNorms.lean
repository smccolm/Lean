import Dubon2026.AdelicUnitaryInfinitesimal
import Mathlib.Data.Nat.Factorial.Basic

/-! # Actual orthogonality and exact Hilbert norms of the original raising derivatives -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups BigOperators

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Distinct original raising derivatives are orthogonal for the genuine Hilbert inner product. -/
theorem adelicRaisingJet_inner_zero (hf : f ≠ 0) (m n : ℕ) (hmn : m ≠ n) :
    inner ℂ (adelicRaisingJet f m).val (adelicRaisingJet f n).val = 0 := by
  apply symmetric_weight_inner_zero (adelicComplexSl2Action f compactSl2H)
    (adelicCompactSl2H_symmetric f) (adelicRaisingJet f m) (adelicRaisingJet f n)
    ((k : ℂ) + 2 * m) ((k : ℂ) + 2 * n) _
    (adelicRaisingJet_weight f hf m) (adelicRaisingJet_weight f hf n)
  intro he
  apply hmn
  have he' : (m : ℂ) = n := by linear_combination he / 2
  exact_mod_cast he'

/-- The original Hilbert norms have their exact lowest-weight factorial recurrence. -/
theorem adelicRaisingJet_norm_sq_succ (hf : f ≠ 0) (n : ℕ) :
    ‖(adelicRaisingJet f (n + 1)).val‖ ^ 2 =
      ((n : ℝ) + 1) * ((k : ℝ) + n) * ‖(adelicRaisingJet f n).val‖ ^ 2 := by
  have hc : ((n : ℂ) + 1) * (-(k : ℂ) - n) =
      -Complex.ofReal (((n : ℝ) + 1) * ((k : ℝ) + n)) := by push_cast; ring
  exact raising_norm_sq_recurrence (adelicComplexSl2Action f compactSl2E)
    (adelicComplexSl2Action f compactSl2F) (adelicCompactSl2E_F_inner f)
    (adelicRaisingJet f n) (adelicRaisingJet f (n + 1)) (((n : ℝ) + 1) * ((k : ℝ) + n))
    (adelicRaisingJet_raise f n)
    ((adelicRaisingJet_lower f hf n).trans
      (congrArg (fun a : ℂ => a • adelicRaisingJet f n) hc))

/-- Every original raising derivative has the exact factorial-times-rising-product squared norm of the original completed cusp generator. -/
theorem adelicRaisingJet_norm_sq (hf : f ≠ 0) (n : ℕ) :
    ‖(adelicRaisingJet f n).val‖ ^ 2 =
      (n.factorial : ℝ) * (∏ j ∈ Finset.range n, ((k : ℝ) + j)) *
        ‖adelicCyclicHilbertGenerator f‖ ^ 2 := by
  induction n with
  | zero => simp only [adelicRaisingJet_zero, adelicSmoothGenerator, Nat.factorial_zero,
      Nat.cast_one, Finset.range_zero, Finset.prod_empty, one_mul]
  | succ n ih =>
      rw [adelicRaisingJet_norm_sq_succ f hf, ih, Nat.factorial_succ, Finset.prod_range_succ]
      push_cast
      ring

end
end Dubon2026
