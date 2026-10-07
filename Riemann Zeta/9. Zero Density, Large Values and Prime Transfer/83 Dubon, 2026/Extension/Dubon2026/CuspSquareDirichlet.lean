import Dubon2026.CuspEnergyBound
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # Absolute convergence of the actual cusp-form square Dirichlet series -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup Filter Asymptotics
open scoped MatrixGroups CongruenceSubgroup Topology

noncomputable section

/-- The unconditional Petersson/Parseval bound gives the correct half-plane of absolute convergence. -/
theorem cusp_square_lseries_summable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : (k : ℝ) < s.re) :
    LSeriesSummable (fun n => ((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ)) s := by
  obtain ⟨C, _, hC⟩ := exists_cusp_coefficient_energy_upper f
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := (k : ℝ))
    (hf := fun n => sq_nonneg _) _ (by exact_mod_cast hk) hs
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hsum,
    Real.rpow_intCast, abs_of_nonneg (zpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) k)] using hC N hN

/-- The real nonnegative square series converges for every real exponent above the weight. -/
theorem summable_cusp_square_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℝ} (hs : (k : ℝ) < s) :
    Summable (fun n : ℕ => ‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-s)) := by
  have hh := (cusp_square_lseries_summable f hk (s := (s : ℂ)) hs).norm
  apply hh.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · simp only [if_neg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖cuspCoefficients f n‖), Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]

end
end Dubon2026
