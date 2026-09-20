import TaoTrudgianYang2025.ZetaMomentTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Height losses and source-window normalization for the zeta moment transfer

The logarithmic convolution loss is absorbed with explicit epsilon
quantifiers. A dyadic critical-line moment hypothesis remains an explicit
analytic input; it is not proved by this normalization.
-/

noncomputable section

open Filter MeasureTheory Set

namespace TaoTrudgianYang2025

theorem zetaMomentLogLoss_le_seven_log {T : ℝ}
    (hT : 4 ≤ T) (hExp : Real.exp 1 ≤ T) :
    zetaMomentLogLoss T ≤ 7 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hc : (⌈2 * T⌉₊ : ℝ) < 2 * T + 1 := Nat.ceil_lt_add_one (by positivity)
  have harg : 0 < (⌈2 * T⌉₊ : ℝ) + 1 := by positivity
  have hlog := Real.log_le_log harg (by linarith : (⌈2 * T⌉₊ : ℝ) + 1 ≤ 4 * T)
  rw [Real.log_mul (by norm_num) hTpos.ne'] at hlog
  have hfour := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hT
  have hone : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExp
  unfold zetaMomentLogLoss
  linarith

/-- Every fixed power of the literal, rounded logarithmic loss is subpower.
The threshold depends on the power and epsilon, not on the ordinate set. -/
theorem eventually_zetaMomentLogLoss_pow_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T ^ n ≤ T ^ ε := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hε).const_mul_left
    ((7 : ℝ) ^ n)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (Real.exp 1)] with T hbound hT hExp
  have hTpos : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  simp only [Real.rpow_natCast, Real.norm_eq_abs, one_mul] at hbound
  rw [abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hlog n)),
    abs_of_nonneg (Real.rpow_nonneg hTpos.le ε)] at hbound
  calc
    _ ≤ (7 * Real.log T) ^ n :=
      pow_le_pow_left₀ (zetaMomentLogLoss_pos T).le (zetaMomentLogLoss_le_seven_log hT hExp) n
    _ = 7 ^ n * Real.log T ^ n := mul_pow _ _ _
    _ ≤ _ := hbound

/-- The source window is bounded by three genuine dyadic critical-line
moments. The last window is enlarged using nonnegativity, not identified
with a different interval. -/
theorem zetaTwelfthMoment_le_three_dyadic {T : ℝ} (hT : 0 < T) :
    zetaTwelfthMoment T ≤
      (∫ u in T / 2..T, zetaMomentCriticalNorm u ^ 12) +
      (∫ u in T..2 * T, zetaMomentCriticalNorm u ^ 12) +
      (∫ u in 2 * T..4 * T, zetaMomentCriticalNorm u ^ 12) := by
  have hc := continuous_zetaMomentCriticalNorm.pow 12
  have hlast : (∫ u in 2 * T..3 * T, zetaMomentCriticalNorm u ^ 12) ≤
      ∫ u in 2 * T..4 * T, zetaMomentCriticalNorm u ^ 12 := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall fun u => pow_nonneg (norm_nonneg _) 12
    · exact hc.intervalIntegrable _ _
  unfold zetaTwelfthMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (T / 2) T)
    (hc.intervalIntegrable T (3 * T)),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable T (2 * T))
      (hc.intervalIntegrable (2 * T) (3 * T))]
  linarith

/-- A finite dyadic moment bound gives the source-window bound with the
exact scaling constant retained. This does not establish the dyadic input. -/
theorem zetaTwelfthMoment_le_of_dyadic
    {C M T₀ T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hT : 0 < T) (hStart : 2 * T₀ ≤ T)
    (hDyadic : ∀ H : ℝ, T₀ ≤ H → 0 < H →
      (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ M) :
    zetaTwelfthMoment T ≤ C * (2 + (2 : ℝ) ^ M) * T ^ M := by
  have hhalf := hDyadic (T / 2) (by linarith) (by positivity)
  have hmiddle := hDyadic T (by linarith) hT
  have hlast := hDyadic (2 * T) (by linarith) (by positivity)
  have hhalfPow : (T / 2) ^ M ≤ T ^ M :=
    Real.rpow_le_rpow (by positivity) (by linarith) hM
  have hmulPow : (2 * T) ^ M = (2 : ℝ) ^ M * T ^ M :=
    Real.mul_rpow (by norm_num) hT.le
  have h := zetaTwelfthMoment_le_three_dyadic hT
  have hh : 2 * (T / 2) = T := by ring
  have ht : 2 * (2 * T) = 4 * T := by ring
  rw [hh] at hhalf
  rw [ht, hmulPow] at hlast
  have hhalf' := hhalf.trans (mul_le_mul_of_nonneg_left hhalfPow hC)
  nlinarith

/-- The complete logarithmic/source-window normalization for a genuine
dyadic twelfth-moment hypothesis. The exponent epsilon is quantified before
the dyadic height and all constants are absorbed uniformly at large height. -/
theorem eventually_zetaMomentLoss_twelfth_of_dyadic
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      zetaMomentLogLoss T ^ 12 * zetaTwelfthMoment T ≤ T ^ (2 + ε) := by
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨C, T₀, hC, hbound⟩ := hDyadic (ε / 3) hthird
  let K : ℝ := C * (2 + (2 : ℝ) ^ (2 + ε / 3))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hconst : ∀ᶠ T : ℝ in atTop, K ≤ T ^ (ε / 3) :=
    (tendsto_rpow_atTop hthird).eventually (eventually_ge_atTop K)
  filter_upwards [eventually_zetaMomentLogLoss_pow_le_rpow 12 hthird,
    hconst, eventually_ge_atTop (2 * T₀), eventually_gt_atTop (0 : ℝ)] with
      T hlog hconstant hStart hT
  have hmoment : zetaTwelfthMoment T ≤ K * T ^ (2 + ε / 3) :=
    zetaTwelfthMoment_le_of_dyadic hC (by linarith) hT hStart hbound
  calc
    _ ≤ zetaMomentLogLoss T ^ 12 * (K * T ^ (2 + ε / 3)) :=
      mul_le_mul_of_nonneg_left hmoment (pow_nonneg (zetaMomentLogLoss_pos T).le 12)
    _ ≤ T ^ (ε / 3) * (T ^ (ε / 3) * T ^ (2 + ε / 3)) :=
      mul_le_mul hlog (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hT.le _))
        (mul_nonneg hK (Real.rpow_nonneg hT.le _)) (Real.rpow_nonneg hT.le _)
    _ = _ := by
      rw [← Real.rpow_add hT, ← Real.rpow_add hT]
      congr 1
      ring

/-- Actual-pattern consumption of the dyadic moment normalization. The
height threshold is uniform in the pattern and in its pointwise entry
constant. Both upstream inputs remain visible in this modular signature;
`ZetaTwelfthFromMoment` supplies the proved Perron entry. -/
theorem zetaPattern_twelfth_cardinality_of_dyadic_and_convolution
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ P : ZetaLargeValuePattern, T₀ ≤ P.T →
      ∀ C : ℝ, 0 < C →
        (∀ t ∈ P.ordinates, P.V ≤ C * Real.sqrt P.N * zetaMomentConvolution P.T t) →
        (P.ordinates.card : ℝ) * P.V ^ 12 ≤ C ^ 12 * P.N ^ 6 * P.T ^ (2 + ε) := by
  obtain ⟨T₀, hbound⟩ := Filter.eventually_atTop.1
    (eventually_zetaMomentLoss_twelfth_of_dyadic hDyadic hε)
  refine ⟨max 1 T₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro P hT C hC hEntry
  have hmoment := hbound P.T ((le_max_right _ _).trans hT)
  have hfinite := P.twelfth_cardinality_of_convolution hC hEntry
  calc
    _ ≤ C ^ 12 * P.N ^ 6 * (zetaMomentLogLoss P.T ^ 12 * zetaTwelfthMoment P.T) := by
      simpa only [mul_assoc] using hfinite
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment
      (mul_nonneg (pow_nonneg hC.le 12) (pow_nonneg (zero_lt_one.trans P.one_lt_N).le 6))

end TaoTrudgianYang2025
