import Dubon2026.CuspPeriodNormalizedEnergy
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Deriv

/-! # Actual convergent Rankin series for arbitrary cusp periods -/

namespace Dubon2026

open UpperHalfPlane Filter Asymptotics Set
open scoped MatrixGroups Topology

noncomputable section

/-- The actual normalized square q-expansion at any positive cusp period gives an absolutely convergent Dirichlet series for Re(s)>1. -/
theorem normalized_cusp_period_square_lseries_summable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((‖normalizedCuspPeriodCoefficients f h n‖ ^ 2 : ℝ) : ℂ)) s := by
  obtain ⟨C, _, hb⟩ := exists_normalized_cusp_period_square_upper f hh hΓ hk
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
    (hf := fun n => sq_nonneg _) _ (by norm_num) hs
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  exact Filter.Eventually.of_forall (fun N => by
    have hn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspPeriodCoefficients f h n‖ ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, Real.rpow_one,
      abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hb N)

/-- The genuine Rankin series for the normalized q-expansion at the specified period. -/
def cuspPeriodRankinSeries {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (s : ℂ) : ℂ :=
  LSeries (fun n => ((‖normalizedCuspPeriodCoefficients f h n‖ ^ 2 : ℝ) : ℂ)) s

/-- The actual period Rankin series is analytic throughout its genuine convergence half-plane. -/
theorem cuspPeriodRankinSeries_analyticOnNhd
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k) :
    AnalyticOnNhd ℂ (cuspPeriodRankinSeries f h) {s : ℂ | 1 < s.re} := by
  have hb : LSeries.abscissaOfAbsConv (fun n =>
      ((‖normalizedCuspPeriodCoefficients f h n‖ ^ 2 : ℝ) : ℂ)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => normalized_cusp_period_square_lseries_summable f hh hΓ hk (s := (y : ℂ)) hy)
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact hb.trans_lt (by exact_mod_cast hs)

/-- At period one the actual coefficient construction agrees exactly with the existing Gamma0 normalization. -/
theorem normalizedCuspPeriodCoefficients_one_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    normalizedCuspPeriodCoefficients f 1 = normalizedCuspCoefficients f := rfl

/-- The genuine period-one Rankin function agrees with the already audited original series. -/
theorem cuspPeriodRankinSeries_one_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    cuspPeriodRankinSeries f 1 = cuspRankinSeries f := rfl

end
end Dubon2026
