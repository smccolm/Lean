import Dubon2026.RectangularDualSeriesReal
import Dubon2026.LatticeCuspFunctionalEquation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! # The genuine rectangular dual series throughout its complex convergence half-plane -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup Filter Set
open scoped MatrixGroups Topology

noncomputable section

/-- The exact common-period Gamma completion is holomorphic in the convergence half-plane. -/
theorem differentiableAt_cuspTraceRankinFactor {N : ℕ} [NeZero N] {k : ℤ} (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (cuspTraceRankinFactor N k) s := by
  have hbase : (4 * Real.pi / N : ℝ) > 0 :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr (Nat.pos_of_neZero N))
  have ha : DifferentiableAt ℂ (fun t : ℂ => t + (k : ℂ) - 1) s :=
    (differentiableAt_id.add_const _).sub_const _
  have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s (by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hGk : DifferentiableAt ℂ Complex.Gamma (s + (k : ℂ) - 1) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re,
        Complex.neg_re, Complex.natCast_re] at hr
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      linarith [Nat.cast_nonneg (α := ℝ) n])
  exact ((differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hG).mul
      ((ha.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hbase.ne'))).mul (hGk.comp s ha))

/-- The actual rescaled convolution series is analytic by its proved absolute convergence. -/
theorem rectangularDualSeries_analyticOnNhd {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) :
    AnalyticOnNhd ℂ (LSeries (rectangularDualCoefficients f)) {s : ℂ | 1 < s.re} := by
  have hb : LSeries.abscissaOfAbsConv (rectangularDualCoefficients f) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => rectangularDual_lseriesSummable f hk (s := (y : ℂ)) hy)
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact hb.trans_lt (by exact_mod_cast hs)

/-- The literal rectangular cusp integral is analytic on the convergence half-plane, from the proved integrated continuation. -/
theorem rectangularLatticeCuspCompleted_analyticOnNhd {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) :
    AnalyticOnNhd ℂ (rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _))
      {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  apply (differentiableAt_rectangularLatticeCuspCompleted f _ _ _ _ ?_ ?_).differentiableWithinAt
  · intro h
    simp only [h, Complex.zero_re, mem_setOf_eq] at hs
    linarith
  · intro h
    simp only [h, Complex.one_re, mem_setOf_eq, lt_self_iff_false] at hs

/-- The actual completed rescaled series is analytic, with its precise normalization. -/
theorem rectangularDualFactor_mul_series_analyticOnNhd {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) :
    AnalyticOnNhd ℂ (fun s => rectangularDualFactor a b k s * LSeries (rectangularDualCoefficients f) s)
      {s : ℂ | 1 < s.re} := by
  have hF : AnalyticOnNhd ℂ (rectangularDualFactor a b k) {s : ℂ | 1 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact ((differentiableAt_cuspTraceRankinFactor hk hs).const_mul _).differentiableWithinAt
  exact hF.mul (rectangularDualSeries_analyticOnNhd f hk)

/-- The genuine rectangular lattice integral equals the actual dual Dirichlet series throughout Re(s)>1, by analytic continuation of the proved real-axis unfolding. -/
theorem rectangularLatticeCuspCompleted_eq_dual {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) s =
      rectangularDualFactor a b k s * LSeries (rectangularDualCoefficients f) s := by
  have ht : Tendsto Complex.ofReal (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [Complex.ofReal_ofNat] using
        (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change (x : ℂ) ≠ (2 : ℂ)
      exact_mod_cast ne_of_gt hx
  have he : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) z =
        rectangularDualFactor a b k z * LSeries (rectangularDualCoefficients f) z := by
    apply ht.frequently
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 2 < x at hx
    exact rectangularLatticeCuspCompleted_eq_dual_real f hk (by linarith)
  exact (rectangularLatticeCuspCompleted_analyticOnNhd f).eqOn_of_preconnected_of_frequently_eq
    (rectangularDualFactor_mul_series_analyticOnNhd f hk) (convex_halfSpace_re_gt 1).isPreconnected
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num) he hs

/-- The actual reflected rectangular lattice integral is the absolutely convergent series of the genuine rescaled cusp coefficients on Re(s)<0. -/
theorem rectangularLatticeCuspCompleted_reflected_dual {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : s.re < 0) :
    rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) s =
      rectangularDualFactor a b k (1 - s) * LSeries (rectangularDualCoefficients f) (1 - s) := by
  rw [← rectangularLatticeCuspCompleted_functional_equation f (a * b) b
    (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) s]
  exact rectangularLatticeCuspCompleted_eq_dual f hk (by simp only [Complex.sub_re, Complex.one_re]; linarith)

end
end Dubon2026
