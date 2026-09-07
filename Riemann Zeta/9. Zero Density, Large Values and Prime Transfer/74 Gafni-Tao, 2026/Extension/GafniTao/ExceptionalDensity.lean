import GafniTao.UniformDensityConsequences

/-!
# From exceptional exponents to density zero

This file works with the literal Lebesgue measure of the source exceptional
set.  It proves the first, quantitative half of the paper's countable
diagonalization: `mu(theta) < 1` makes every fixed discrepancy threshold a
density-zero family on `[X,2X]`.
-/

open Asymptotics Filter Topology

namespace GafniTao

noncomputable section

/-- A fixed power strictly below one gives vanishing relative measure. -/
theorem FixedPowerBound.tendsto_div_id_zero
    {f : ℝ → ℝ} {xi : ℝ} (h : FixedPowerBound f xi) (hxi : xi < 1) :
    Tendsto (fun X => f X / X) atTop (𝓝 0) := by
  rcases h with ⟨C, hC, hBound⟩
  have hBigO : (fun X => f X) =O[atTop] (fun X : ℝ => X ^ xi) := by
    apply IsBigO.of_bound C
    filter_upwards [hBound, eventually_gt_atTop (0 : ℝ)] with X hX hXpos
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hXpos.le _)] using hX
  have hLittle : (fun X => f X) =o[atTop] (fun X : ℝ => X) := by
    have hpowers := rpow_isLittleO_rpow hxi
    have hone : (fun X : ℝ => X ^ (1 : ℝ)) =ᶠ[atTop] fun X => X :=
      Eventually.of_forall fun X => by simp only [Real.rpow_one]
    exact hBigO.trans_isLittleO (hpowers.congr' EventuallyEq.rfl hone)
  exact hLittle.tendsto_div_nhds_zero

/-- The actual source exceptional sets have dyadic density zero at every
fixed positive discrepancy threshold. -/
def DyadicExceptionalDensityZero (theta : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    Tendsto (fun X => exceptionalMeasure delta X theta / X) atTop (𝓝 0)

/-- Exact bridge advertised after Definition 1.1: `mu(theta) < 1` controls
the literal exceptional-set measure, not a sampled proxy. -/
theorem exceptionalExponent_lt_one_dyadicDensityZero
    {theta : ℝ} (hmu : exceptionalExponent theta < (1 : EReal)) :
    DyadicExceptionalDensityZero theta := by
  intro delta hdelta
  have hDelta : exceptionalExponentDelta delta theta < (1 : EReal) :=
    (exceptionalExponentDelta_le_exceptionalExponent hdelta).trans_lt hmu
  obtain ⟨xi, hxiLower, hxiUpper⟩ := EReal.exists_between_coe_real hDelta
  have hBound : FixedPowerBound
      (fun X => exceptionalMeasure delta X theta) xi :=
    fixedPowerBound_of_leastFixedPowerExponent_lt hxiLower
  exact hBound.tendsto_div_id_zero (by exact_mod_cast hxiUpper)

/-- The almost-all exponent consequence of a uniform ordinary zero-density
coefficient, stated directly for the genuine Lebesgue exceptional sets. -/
theorem gafniTaoTheorem11_almostAll_dyadic
    {C B Tzero theta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hC : 0 < C) (hAzero : 0 < Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hUniform : UniformOrdinaryDensityExponent Azero)
    (hthetaThreshold : 1 - 2 / Azero < theta) :
    DyadicExceptionalDensityZero theta :=
  exceptionalExponent_lt_one_dyadicDensityZero
    (exceptionalExponent_lt_one_of_uniform_density hDensity hC hAzero
      hthetaLower hthetaUpper hUniform hthetaThreshold)

/-- The actual frozen Guth--Maynard/Ingham chain supplies the uniform
coefficient used by the source corollary. -/
theorem uniformOrdinaryDensityExponent_thirty_thirteenths :
    UniformOrdinaryDensityExponent (30 / 13) := by
  intro sigma hsigma hsigmaUpper
  exact zeroDensityExponent_le_thirty_thirteenths hsigma hsigmaUpper.le

/-- Native Gafni--Tao/Guth--Maynard almost-all threshold, at the level of the
literal exceptional-set Lebesgue measures. -/
theorem gafniTaoTheorem11_almostAll_guthMaynard_native
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    DyadicExceptionalDensityZero theta := by
  obtain ⟨c, Tzero, Tdensity, hc, _hZeroFree, hDensity⟩ :=
    exists_pintz_nearOne_log_density_native
  apply gafniTaoTheorem11_almostAll_dyadic hDensity
    pintzNearOneDensityCoefficient_pos (by norm_num : (0 : ℝ) < 30 / 13)
    (by linarith) hthetaUpper uniformOrdinaryDensityExponent_thirty_thirteenths
  rw [← two_fifteenths_eq_uniform_almost_all_threshold]
  exact htheta

end

end GafniTao
