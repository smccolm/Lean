import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The local logarithm reconstructs actual meromorphic primitives away from the
poles. Its exponential and derivative use native complex logarithm theorems;
different centers change its value by an integral multiple of two pi i.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open Complex Set Metric
open scoped Real

/-- A local logarithm centered away from the cell center. -/
noncomputable def Lg (q c w : ℂ) : ℂ := Complex.log ((w - q) / (c - q)) + Complex.log (c - q)

theorem Lg_self (q c : ℂ) : Lg q c c = Complex.log (c - q) := by
  unfold Lg
  by_cases h : c - q = 0
  · rw [h]; simp
  · rw [div_self h, Complex.log_one, zero_add]

theorem exp_Lg {q c w : ℂ} (hc : c ≠ q) (hw : w ≠ q) : exp (Lg q c w) = w - q := by
  have hc' : c - q ≠ 0 := sub_ne_zero.2 hc
  have hw' : w - q ≠ 0 := sub_ne_zero.2 hw
  rw [Lg, exp_add, exp_log hc', exp_log (div_ne_zero hw' hc'), div_mul_cancel₀ _ hc']


theorem Lg_sub_Lg {q c c' w : ℂ} (hc : c ≠ q) (hc' : c' ≠ q) (hw : w ≠ q) :
    ∃ n : ℤ, Lg q c w - Lg q c' w = n * (2 * π * I) := by
  have h : exp (Lg q c w) = exp (Lg q c' w) := by rw [exp_Lg hc hw, exp_Lg hc' hw]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  exact ⟨n, by rw [hn]; ring⟩

theorem hasDerivAt_Lg {q c w : ℂ} (hw : w ∈ ball c ‖c - q‖) :
    HasDerivAt (Lg q c) (1 / (w - q)) w := by
  have hc : c - q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact (Set.notMem_empty w) (by rwa [Metric.ball_zero] at hw)
  have hslit : (w - q) / (c - q) ∈ slitPlane := by
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    have h1 : ‖(w - q) / (c - q) - 1‖ < 1 := by
      rw [div_sub_one hc, norm_div, div_lt_one (norm_pos_iff.2 hc)]
      have : w - q - (c - q) = w - c := by ring
      rw [this, ← dist_eq_norm]
      exact hw
    have h2 := abs_re_le_norm ((w - q) / (c - q) - 1)
    rw [sub_re, one_re] at h2
    have h3 : |((w - q) / (c - q)).re - 1| < 1 := lt_of_le_of_lt h2 h1
    have h4 := (abs_lt.1 h3).1
    linarith
  have hf : HasDerivAt (fun w => (w - q) / (c - q)) (1 / (c - q)) w := by
    have := ((hasDerivAt_id w).sub_const q).div_const (c - q)
    simpa using this
  have h := hf.clog hslit
  have heq : 1 / (c - q) / ((w - q) / (c - q)) = 1 / (w - q) := by
    have hwq : w - q ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hslit
      exact zero_notMem_slitPlane hslit
    field_simp
  rw [heq] at h
  have hLg : Lg q c = fun w => Complex.log ((w - q) / (c - q)) + Complex.log (c - q) := rfl
  rw [hLg]
  exact h.add_const (Complex.log (c - q))

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
