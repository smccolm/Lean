import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import RiemannZeta.GuthMaynard.HughesYoungConsumer
import RiemannZeta.GuthMaynard.HughesYoungFubini

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Integrated Hughes--Young consumption of DFI

This module composes the exact finite Fubini bridge with the source-normalized
DFI theorem.  It keeps the small-contour Gamma loss and the complete
shift-dependent Ramanujan contribution visible under the ordinate integral.
-/

/-- The explicit small-contour ordinate envelope obtained from the
Hughes--Young Gamma-ratio estimate. -/
noncomputable def hughesYoungSmallLineEnvelope
    (C T c u : ℝ) : ℝ :=
  c⁻¹ * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)

theorem hughesYoungSmallLineEnvelope_pos
    {C T c : ℝ} (hT : 0 < T) (hc : 0 < c) (u : ℝ) :
    0 < hughesYoungSmallLineEnvelope C T c u := by
  unfold hughesYoungSmallLineEnvelope
  positivity

theorem continuous_hughesYoungSmallLineEnvelope
    (C T c : ℝ) : Continuous (hughesYoungSmallLineEnvelope C T c) := by
  unfold hughesYoungSmallLineEnvelope
  have harg : Continuous (fun u : ℝ => 6 * (|u| + 1)) := by fun_prop
  have hlog : Continuous (fun u : ℝ => Real.log (6 * (|u| + 1))) :=
    harg.log (fun u => by positivity)
  exact continuous_const.mul
    ((Real.continuous_exp.comp
      (((continuous_const.sub
        (continuous_const.mul (continuous_id.pow 2))).add
          (continuous_const.mul hlog)))).mul
      ((continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))).pow 8))

/-- The ordinate-dependent part left after multiplying the small-line
envelope by the Gaussian normalization in the scaled DFI consumer. -/
noncomputable def hughesYoungIntegratedOrdinateFactor
    (C c u : ℝ) : ℝ :=
  Real.exp
      (100 * c ^ 2 - 82 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
    (25 + 8 * u ^ 2) ^ 8

theorem continuous_hughesYoungIntegratedOrdinateFactor
    (C c : ℝ) : Continuous (hughesYoungIntegratedOrdinateFactor C c) := by
  unfold hughesYoungIntegratedOrdinateFactor
  have harg : Continuous (fun u : ℝ => 6 * (|u| + 1)) := by fun_prop
  have hlog : Continuous (fun u : ℝ => Real.log (6 * (|u| + 1))) :=
    harg.log (fun u => by positivity)
  exact
    (Real.continuous_exp.comp
      (((continuous_const.sub
        (continuous_const.mul (continuous_id.pow 2))).add
          (continuous_const.mul hlog)))).mul
      ((continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))).pow 8)

/-- Exact separation of the Hughes--Young small-line normalization into
the scale variables and the single ordinate factor that is integrated
uniformly below. -/
theorem hughesYoungScaledDFINormalization_smallLine_eq
    (C T c u X Y : ℝ) (h k : ℕ) :
    hughesYoungScaledDFINormalization c u X Y
        (hughesYoungSmallLineEnvelope C T c u) h k =
      (c⁻¹ * T ^ (4 * C * c) *
          ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
          ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) *
        hughesYoungIntegratedOrdinateFactor C c u := by
  unfold hughesYoungScaledDFINormalization hughesYoungSmallLineEnvelope
    hughesYoungIntegratedOrdinateFactor
  conv_rhs =>
    rw [show
        100 * c ^ 2 - 82 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1)) =
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) + 2 * u ^ 2 by ring,
      Real.exp_add]
  ring

/-- The source small contour used in the Hughes--Young error calculation. -/
noncomputable def hughesYoungSmallContour (T : ℝ) : ℝ :=
  (Real.log T)⁻¹

theorem hughesYoungSmallContour_spec
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    0 < hughesYoungSmallContour T ∧ hughesYoungSmallContour T ≤ 1 ∧
      (hughesYoungSmallContour T)⁻¹ = Real.log T := by
  have hlog1 : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hlog0 : 0 < Real.log T := zero_lt_one.trans_le hlog1
  unfold hughesYoungSmallContour
  refine ⟨inv_pos.mpr hlog0, (inv_le_one₀ hlog0).2 hlog1, ?_⟩
  exact inv_inv _

theorem rpow_smallContour_four_mul_eq
    (C : ℝ) {T : ℝ} (hT : Real.exp 1 ≤ T) :
    T ^ (4 * C * hughesYoungSmallContour T) = Real.exp (4 * C) := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog1 : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hlogne : Real.log T ≠ 0 := ne_of_gt (zero_lt_one.trans_le hlog1)
  rw [Real.rpow_def_of_pos hT0]
  unfold hughesYoungSmallContour
  congr 1
  field_simp

/-- Uniform Gaussian domination of the full small-line ordinate factor.
The two `exp(u^2)` losses pay for the real power and the degree-eight
polynomial, leaving the integrable Gaussian `exp(-80 u^2)`. -/
theorem exists_hughesYoungIntegratedOrdinateFactor_le_gaussian
    {C : ℝ} (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {c : ℝ}, 0 < c → c ≤ 1 → ∀ u : ℝ,
      hughesYoungIntegratedOrdinateFactor C c u ≤
        K * Real.exp (-80 * u ^ 2) := by
  let n : ℕ := Nat.ceil (4 * C)
  let K : ℝ := Real.exp 100 *
    (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
    (33 ^ 8 * hughesYoungGaussianPowerConstant 8)
  have hK : 0 < K := by
    dsimp only [K]
    exact mul_pos
      (mul_pos (Real.exp_pos 100)
        (mul_pos (by positivity)
          (mul_pos (by positivity) (hughesYoungGaussianPowerConstant_pos n))))
      (mul_pos (by positivity) (hughesYoungGaussianPowerConstant_pos 8))
  refine ⟨K, hK, ?_⟩
  intro c hc hc1 u
  let B : ℝ := 6 * (|u| + 1)
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    have hu : 0 ≤ |u| := abs_nonneg u
    nlinarith
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have hk0 : 0 ≤ 4 * C * c := by positivity
  have hkceil : 4 * C * c ≤ (n : ℝ) := by
    have hcc : 4 * C * c ≤ 4 * C := by
      exact mul_le_of_le_one_right (by positivity) hc1
    exact hcc.trans (Nat.le_ceil (4 * C))
  have hBpow : B ^ (4 * C * c) ≤ B ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hB1 hkceil
  have hexplog : Real.exp (4 * C * c * Real.log B) =
      B ^ (4 * C * c) := by
    rw [Real.rpow_def_of_pos hB0]
    congr 1
    ring
  have habspow : (|u| + 1) ^ n ≤
      2 ^ n * hughesYoungGaussianPowerConstant n * Real.exp (u ^ 2) := by
    convert abs_add_pow_le_gaussian u 1 (by norm_num) n using 1
    all_goals norm_num
  have hBnat : B ^ n ≤
      (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
        Real.exp (u ^ 2) := by
    dsimp only [B]
    rw [mul_pow]
    calc
      6 ^ n * (|u| + 1) ^ n ≤
          6 ^ n *
            (2 ^ n * hughesYoungGaussianPowerConstant n *
              Real.exp (u ^ 2)) := by
        exact mul_le_mul_of_nonneg_left habspow (by positivity)
      _ = (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
          Real.exp (u ^ 2) := by ring
  have hlogpow : Real.exp (4 * C * c * Real.log B) ≤
      (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
        Real.exp (u ^ 2) := by
    rw [hexplog]
    exact hBpow.trans hBnat
  have hpolybase : 25 + 8 * u ^ 2 ≤ 33 * (u ^ 2 + 1) := by
    nlinarith [sq_nonneg u]
  have hpolyPow := pow_le_pow_left₀ (by positivity) hpolybase 8
  have hpolyGauss := pow_add_one_le_gaussianPowerConstant_mul_exp
    (sq_nonneg u) 8
  have hpoly : (25 + 8 * u ^ 2) ^ 8 ≤
      (33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
        Real.exp (u ^ 2) := by
    calc
      (25 + 8 * u ^ 2) ^ 8 ≤ (33 * (u ^ 2 + 1)) ^ 8 := hpolyPow
      _ = 33 ^ 8 * (u ^ 2 + 1) ^ 8 := by rw [mul_pow]
      _ ≤ 33 ^ 8 *
          (hughesYoungGaussianPowerConstant 8 * Real.exp (u ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hpolyGauss (by positivity)
      _ = (33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
          Real.exp (u ^ 2) := by ring
  have hcSq : c ^ 2 ≤ 1 := by nlinarith
  have hcExp : Real.exp (100 * c ^ 2) ≤ Real.exp 100 := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hGn : 0 ≤ hughesYoungGaussianPowerConstant n :=
    (hughesYoungGaussianPowerConstant_pos n).le
  have hG8 : 0 ≤ hughesYoungGaussianPowerConstant 8 :=
    (hughesYoungGaussianPowerConstant_pos 8).le
  unfold hughesYoungIntegratedOrdinateFactor
  rw [show
      100 * c ^ 2 - 82 * u ^ 2 + 4 * C * c * Real.log (6 * (|u| + 1)) =
        100 * c ^ 2 + (-82 * u ^ 2) + 4 * C * c * Real.log B by
      dsimp only [B]
      ring,
    Real.exp_add, Real.exp_add]
  calc
    Real.exp (100 * c ^ 2) * Real.exp (-82 * u ^ 2) *
          Real.exp (4 * C * c * Real.log B) *
          (25 + 8 * u ^ 2) ^ 8 ≤
        Real.exp 100 * Real.exp (-82 * u ^ 2) *
          ((6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
            Real.exp (u ^ 2)) *
          ((33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
            Real.exp (u ^ 2)) := by
      gcongr
    _ = K * Real.exp (-80 * u ^ 2) := by
      dsimp only [K]
      have hexp :
          Real.exp 100 * Real.exp (-82 * u ^ 2) * Real.exp (u ^ 2) *
              Real.exp (u ^ 2) =
            Real.exp 100 * Real.exp (-80 * u ^ 2) := by
        calc
          Real.exp 100 * Real.exp (-82 * u ^ 2) * Real.exp (u ^ 2) *
                Real.exp (u ^ 2) =
              Real.exp (100 + (-82 * u ^ 2) + u ^ 2 + u ^ 2) := by
                rw [Real.exp_add, Real.exp_add, Real.exp_add]
          _ = Real.exp (100 + (-80 * u ^ 2)) := by
            congr 1
            ring
          _ = Real.exp 100 * Real.exp (-80 * u ^ 2) := Real.exp_add _ _
      calc
        Real.exp 100 * Real.exp (-82 * u ^ 2) *
              (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n) *
                Real.exp (u ^ 2)) *
              (33 ^ 8 * hughesYoungGaussianPowerConstant 8 *
                Real.exp (u ^ 2)) =
            (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
              (33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
              (Real.exp 100 * Real.exp (-82 * u ^ 2) *
                Real.exp (u ^ 2) * Real.exp (u ^ 2)) := by ring
        _ = (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
              (33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
              (Real.exp 100 * Real.exp (-80 * u ^ 2)) := by rw [hexp]
        _ = Real.exp 100 *
              (6 ^ n * (2 ^ n * hughesYoungGaussianPowerConstant n)) *
              (33 ^ 8 * hughesYoungGaussianPowerConstant 8) *
              Real.exp (-80 * u ^ 2) := by ring

theorem integrable_hughesYoungIntegratedOrdinateFactor
    {C : ℝ} (hC : 0 < C) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Integrable (hughesYoungIntegratedOrdinateFactor C c) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_hughesYoungIntegratedOrdinateFactor_le_gaussian hC
  have hgauss : Integrable (fun u : ℝ => K * Real.exp (-80 * u ^ 2)) := by
    apply Integrable.const_mul
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  apply hgauss.mono'
  · exact (continuous_hughesYoungIntegratedOrdinateFactor C c).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_pos]
    · exact hbound hc hc1 u
    · unfold hughesYoungIntegratedOrdinateFactor
      positivity

/-- The complete ordinate factor has a bound independent of both the contour
height and the small positive contour abscissa.  This is the uniform
integrability statement needed when Hughes--Young removes the truncated
Mellin contour. -/
theorem exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le
    {C : ℝ} (hC : 0 < C) :
    ∃ L : ℝ, 0 < L ∧ ∀ {c H : ℝ}, 0 < c → c ≤ 1 → 0 ≤ H →
      (∫ u in -H..H, hughesYoungIntegratedOrdinateFactor C c u) ≤ L := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_hughesYoungIntegratedOrdinateFactor_le_gaussian hC
  let L : ℝ := K * Real.sqrt (Real.pi / 80)
  have hsqrt : 0 < Real.sqrt (Real.pi / 80) := by positivity
  have hL : 0 < L := mul_pos hK hsqrt
  refine ⟨L, hL, ?_⟩
  intro c H hc hc1 hH
  have hHH : -H ≤ H := by linarith
  have hf : Integrable (hughesYoungIntegratedOrdinateFactor C c) :=
    integrable_hughesYoungIntegratedOrdinateFactor hC hc hc1
  have hg : Integrable (fun u : ℝ => K * Real.exp (-80 * u ^ 2)) := by
    apply Integrable.const_mul
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  have hinterval :
      (∫ u in -H..H, hughesYoungIntegratedOrdinateFactor C c u) ≤
        ∫ u in -H..H, K * Real.exp (-80 * u ^ 2) := by
    apply intervalIntegral.integral_mono_on hHH hf.intervalIntegrable
      hg.intervalIntegrable
    intro u _
    exact hpoint hc hc1 u
  have hfull :
      (∫ u in -H..H, K * Real.exp (-80 * u ^ 2)) ≤
        ∫ u : ℝ, K * Real.exp (-80 * u ^ 2) := by
    rw [intervalIntegral.integral_of_le hHH]
    apply setIntegral_le_integral hg
    filter_upwards with u
    positivity
  calc
    (∫ u in -H..H, hughesYoungIntegratedOrdinateFactor C c u) ≤
        ∫ u in -H..H, K * Real.exp (-80 * u ^ 2) := hinterval
    _ ≤ ∫ u : ℝ, K * Real.exp (-80 * u ^ 2) := hfull
    _ = K * Real.sqrt (Real.pi / 80) := by
      rw [integral_const_mul, integral_gaussian]
    _ = L := rfl

/-- The finite arithmetic coefficient left after the common ordinate factor
is removed from the summed DFI error and central-series bounds. -/
noncomputable def hughesYoungIntegratedDFIArithmeticTotal
    (C T P X Y ε : ℝ) (h k a b : ℕ) (s : Finset ℤ) : ℝ :=
  ∑ r ∈ s,
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * (dfiTheorem1ErrorScale P X Y ε +
        hughesYoungCentralArithmeticScale X Y a b r.natAbs +
        hughesYoungCentralArithmeticScale Y X b a r.natAbs))

/-- Pointwise factorization of the integrated DFI majorant. -/
theorem hughesYoungIntegratedDFIMajorant_eq
    (Cγ C T c P X Y ε : ℝ) (h k a b : ℕ) (s : Finset ℤ) (u : ℝ) :
    T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y
              (hughesYoungSmallLineEnvelope Cγ T c u) h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
      (T * (c⁻¹ * T ^ (4 * Cγ * c) *
          ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
          ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) *
        hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s) *
          hughesYoungIntegratedOrdinateFactor Cγ c u := by
  simp_rw [hughesYoungScaledDFINormalization_smallLine_eq]
  unfold hughesYoungIntegratedDFIArithmeticTotal
  let D : ℝ := c⁻¹ * T ^ (4 * Cγ * c) *
    ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
    ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)
  let F : ℤ → ℝ := fun r =>
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * (dfiTheorem1ErrorScale P X Y ε +
        hughesYoungCentralArithmeticScale X Y a b r.natAbs +
        hughesYoungCentralArithmeticScale Y X b a r.natAbs))
  change T * (∑ r ∈ s,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
        (C * (dfiTheorem1ErrorScale P X Y ε +
          hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
    (T * D * ∑ r ∈ s, F r) *
      hughesYoungIntegratedOrdinateFactor Cγ c u
  calc
    T * (∑ r ∈ s,
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
          (C * (dfiTheorem1ErrorScale P X Y ε +
            hughesYoungCentralArithmeticScale X Y a b r.natAbs +
            hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
      T * (∑ r ∈ s,
        (D * hughesYoungIntegratedOrdinateFactor Cγ c u) * F r) := by
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          dsimp only [F]
          ring
    _ = T * ((D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
        ∑ r ∈ s, F r) := by
          congr 1
          exact (Finset.mul_sum s F
            (D * hughesYoungIntegratedOrdinateFactor Cγ c u)).symm
    _ = (T * D * ∑ r ∈ s, F r) *
        hughesYoungIntegratedOrdinateFactor Cγ c u := by ring

/-- Uniform removal of the ordinate integral from the complete summed DFI
majorant.  No contour-height factor remains. -/
theorem exists_uniform_integral_hughesYoungIntegratedDFIMajorant_le
    {Cγ : ℝ} (hCγ : 0 < Cγ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {C T c H P X Y ε : ℝ} {h k a b : ℕ} {s : Finset ℤ},
      0 < C → Real.exp 1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ P → 1 ≤ X → 1 ≤ Y → 0 < ε → 0 < h → 0 < k →
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y
              (hughesYoungSmallLineEnvelope Cγ T c u) h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) ≤
        (T * (c⁻¹ * T ^ (4 * Cγ * c) *
          ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
          ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) *
          hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s) * L := by
  obtain ⟨L, hL, hfactor⟩ :=
    exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le hCγ
  refine ⟨L, hL, ?_⟩
  intro C T c H P X Y ε h k a b s hC hT hc hc1 hH hP hX hY hε hh hk
  let D : ℝ := T * (c⁻¹ * T ^ (4 * Cγ * c) *
    ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
    ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) *
    hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hE : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
    unfold dfiTheorem1ErrorScale
    positivity
  have htotal :
      0 ≤ hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s := by
    unfold hughesYoungIntegratedDFIArithmeticTotal
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (norm_nonneg _)
      (mul_nonneg hC.le
        (add_nonneg
          (add_nonneg hE
            (hughesYoungCentralArithmeticScale_nonneg hX hY a b r.natAbs))
          (hughesYoungCentralArithmeticScale_nonneg hY hX b a r.natAbs)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have heq :
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y
              (hughesYoungSmallLineEnvelope Cγ T c u) h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
        D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ c u) := by
    calc
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y
              (hughesYoungSmallLineEnvelope Cγ T c u) h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
          ∫ u in -H..H, D *
            hughesYoungIntegratedOrdinateFactor Cγ c u := by
              apply intervalIntegral.integral_congr
              intro u _
              exact hughesYoungIntegratedDFIMajorant_eq
                Cγ C T c P X Y ε h k a b s u
      _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ c u) := by
            rw [intervalIntegral.integral_const_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hfactor hc hc1 hH) hD

/-- Hughes--Young's choice `c = 1 / log T` converts the apparent real-power
loss into a fixed constant and leaves exactly one logarithm. -/
theorem exists_uniform_integral_hughesYoungSmallContourDFIMajorant_le
    {Cγ : ℝ} (hCγ : 0 < Cγ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {C T H P X Y ε : ℝ} {h k a b : ℕ} {s : Finset ℤ},
      0 < C → Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ P → 1 ≤ X → 1 ≤ Y → 0 < ε → 0 < h → 0 < k →
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) h k *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s) * L := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_uniform_integral_hughesYoungIntegratedDFIMajorant_le hCγ
  refine ⟨L, hL, ?_⟩
  intro C T H P X Y ε h k a b s hC hT hH hP hX hY hε hh hk
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hraw := hbound (C := C) (T := T) (c := hughesYoungSmallContour T)
    (H := H) (P := P) (X := X) (Y := Y) (ε := ε)
    (h := h) (k := k) (a := a) (b := b) (s := s)
    hC hT hc hc1 hH hP hX hY hε hh hk
  rw [hcinv, rpow_smallContour_four_mul_eq Cγ hT] at hraw
  exact hraw

/-- Complete near-shift estimate after the height/Mellin Fubini interchange.
The left side is the actual integrated AFE source weight with its dyadic
localizers.  The right side is the literal DFI Theorem 1 error plus the two
signed equation-(27) central-series bounds, integrated against the explicit
small-line Gaussian envelope. -/
theorem exists_uniform_norm_sum_hughesYoungIntegratedSourceWeight_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C : ℝ, 0 < Cγ ∧ 0 < C ∧
      ∀ {T c H X Y P U Q : ℝ} {h k : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      1 ≤ P →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧
        |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (fun x y =>
              (hughesYoungDyadicCutoffAt X x : ℂ) *
                (hughesYoungDyadicCutoffAt Y y : ℂ) *
                hughesYoungIntegratedSourceWeight T c H h k x y)
            a b M N r‖ ≤
        ∫ u in -H..H, T *
          (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization c u X Y
                (hughesYoungSmallLineEnvelope Cγ T c u) h k *
              (C * (dfiTheorem1ErrorScale P X Y ε +
                hughesYoungCentralArithmeticScale X Y a b r.natAbs +
                hughesYoungCentralArithmeticScale Y X b a r.natAbs))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨C, hC, hdfi⟩ :=
    exists_uniform_norm_sum_hughesYoungCleanedShiftWeight_full_dfi
      ε hε0 hε4
  refine ⟨Cγ, C, hCγ, hC, ?_⟩
  intro T c H X Y P U Q h k s hT hc hc1 hH hX hY hh hhX hk hkY
    hP hscale hQ hU hQsq a b M N ha hb hab hM hN haX hbY hs
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    (∑ r ∈ s, dfiDyadicShiftedDivisorSum
      (hughesYoungCleanedShiftWeight T c u X Y h k r) a b M N r)
  let G : ℝ → ℝ := fun u => T *
    (∑ r ∈ s,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y (A u) h k *
        (C * (dfiTheorem1ErrorScale P X Y ε +
          hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs)))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos hT0 hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hFcont : Continuous F := by
    exact continuous_const.mul
      (continuous_finsetSum s fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_cleaned_ordinate
          hT0 hc X Y hh hk ha hb r)
  have hGcont : Continuous G := by
    dsimp only [G]
    apply continuous_const.mul
    apply continuous_finsetSum s
    intro _r _hr
    apply (continuous_const.mul ?_).mul continuous_const
    unfold hughesYoungScaledDFINormalization
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((h : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ G u := by
    intro u
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hraw := hdfi hT hc hc1 hX hY hh hhX hk hkY hP
      (hApos u) hderiv hscale hQ hU hQsq a b M N ha hb hab hM hN
      haX hbY hs
    dsimp only [F, G]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hraw hT0.le
  rw [sum_dfiDyadicShiftedDivisorSum_integratedSource_eq_integral_cleaned
    hT0 hc H X Y hh hk ha hb s]
  change ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, G u
  have hHH : -H ≤ H := by linarith
  calc
    ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, ‖F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hHH
    _ ≤ ∫ u in -H..H, G u := by
      apply intervalIntegral.integral_mono_on hHH
        (hFcont.norm.intervalIntegrable (-H) H)
        (hGcont.intervalIntegrable (-H) H)
      intro u hu
      exact hpoint u

/-- Source-facing Hughes--Young near-shift theorem with the small contour
already chosen and the ordinate integral completely removed.  This composes
the exact AFE-to-DFI Fubini identity, DFI Theorem 1 including both signed
central series, and the uniform Gaussian calculation above. -/
theorem exists_uniform_norm_sum_hughesYoungSmallContourSource_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U Q : ℝ} {h k : ℕ} {s : Finset ℤ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      1 ≤ P →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧
        |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (fun x y =>
              (hughesYoungDyadicCutoffAt X x : ℂ) *
                (hughesYoungDyadicCutoffAt Y y : ℂ) *
                hughesYoungIntegratedSourceWeight T
                  (hughesYoungSmallContour T) H h k x y)
            a b M N r‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((h : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((k : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s) * L := by
  obtain ⟨Cγ, C, hCγ, hC, hsource⟩ :=
    exists_uniform_norm_sum_hughesYoungIntegratedSourceWeight_full_dfi
      ε hε0 hε4
  obtain ⟨L, hL, hmajor⟩ :=
    exists_uniform_integral_hughesYoungSmallContourDFIMajorant_le hCγ
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U Q h k s hT hH hX hY hh hhX hk hkY hP
    hscale hQ hU hQsq a b M N ha hb hab hM hN haX hbY hs
  obtain ⟨hc, hc1, _⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
  have hfirst := hsource hT1 hc hc1 hH hX hY hh hhX hk hkY hP
    hscale hQ hU hQsq a b M N ha hb hab hM hN haX hbY hs
  have hsecond := hmajor (C := C) (T := T) (H := H) (P := P)
    (X := X) (Y := Y) (ε := ε) (h := h) (k := k) (a := a) (b := b)
    (s := s) hC hT hH hP hX hY hε0 hh hk
  exact hfirst.trans hsecond

end RiemannZeta.GuthMaynard
