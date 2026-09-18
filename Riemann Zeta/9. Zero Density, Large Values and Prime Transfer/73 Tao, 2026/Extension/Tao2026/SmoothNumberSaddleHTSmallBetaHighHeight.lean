import Tao2026.SmoothNumberSaddleHTVariableDiskScale

/-!
# High-height small-beta origin residue

This module instantiates the zero-free variable disk at the actual translated
HT height.  It yields the missing uniform `D(A) * log log A` bound for the
physical zeta logarithmic derivative, and hence for the origin residue, in
the high-height half of the small-beta branch.
-/

open Filter Topology Set Complex

namespace Tao2026

noncomputable section

theorem five_le_exp_exp_one :
    (5 : ℝ) ≤ Real.exp (Real.exp 1) := by
  have heTwo : (2 : ℝ) < Real.exp 1 :=
    Real.exp_one_gt_two
  have hmono : Real.exp 2 < Real.exp (Real.exp 1) :=
    Real.exp_lt_exp.mpr heTwo
  have hexpTwo : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [hexpTwo] at hmono
  nlinarith [Real.exp_one_gt_d9]

/-- Shrinking the VK constant preserves the rectangle zero-free theorem. -/
theorem VinogradovKorobovRectangleZeroFree.mono_constant
    {c c' H : ℝ} (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hc' : 0 ≤ c') (hcc' : c' ≤ c) :
    GafniTao.VinogradovKorobovRectangleZeroFree c' H := by
  intro T hHT
  have hTBase : Real.exp (Real.exp 1) ≤ T := hH.trans hHT
  have hD := GafniTao.vinogradovKorobovDenominator_pos hTBase
  have hcNonneg : 0 ≤ c := hc'.trans hcc'
  have hwidth := hZeroFree hHT
  have hfrac : c' / GafniTao.vinogradovKorobovDenominator T ≤
      c / GafniTao.vinogradovKorobovDenominator T :=
    div_le_div_of_nonneg_right hcc' hD.le
  refine ⟨div_nonneg hc' hD.le, hfrac.trans hwidth.2.1, ?_⟩
  intro rho hrho
  have hright := hwidth.2.2 hrho
  linarith

/-- Choose native constants with the stronger width cap `1/2`. -/
theorem exists_smoothSaddleHT_native_vK_halfWidth :
    ∃ c H : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ ⦃T : ℝ⦄, H ≤ T →
        c / GafniTao.vinogradovKorobovDenominator T ≤ 1 / 2 := by
  obtain ⟨c₀, H, hc₀, hH, hZeroFree₀⟩ :=
    exists_smoothSaddleHT_native_vinogradovKorobovRectangleZeroFree
  let c := c₀ / 2
  have hc : 0 < c := div_pos hc₀ (by norm_num)
  have hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H :=
    VinogradovKorobovRectangleZeroFree.mono_constant hH hZeroFree₀ hc.le
      (by dsimp [c]; linarith)
  refine ⟨c, H, hc, hH, hZeroFree, ?_⟩
  intro T hHT
  have hTBase : Real.exp (Real.exp 1) ≤ T := hH.trans hHT
  have hD := GafniTao.vinogradovKorobovDenominator_pos hTBase
  have hcap := (hZeroFree₀ hHT).2.1
  dsimp [c]
  rw [show (c₀ / 2) /
      GafniTao.vinogradovKorobovDenominator T =
        (c₀ / GafniTao.vinogradovKorobovDenominator T) / 2 by ring]
  linarith

/-- Monotonicity of the iterated logarithm above its natural base. -/
theorem fordVKLogLog_mono
    {A B : ℝ} (hA : Real.exp (Real.exp 1) ≤ A) (hAB : A ≤ B) :
    GafniTao.fordVKLogLog A ≤ GafniTao.fordVKLogLog B := by
  have hAPos : 0 < A := (Real.exp_pos _).trans_le hA
  have hBPos : 0 < B := hAPos.trans_le hAB
  have hlogA : 0 < Real.log A := by
    exact Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
      exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hA)
  have hlogB : 0 < Real.log B := by
    exact hlogA.trans_le
      (Real.strictMonoOn_log.monotoneOn hAPos hBPos hAB)
  unfold GafniTao.fordVKLogLog
  exact Real.strictMonoOn_log.monotoneOn hlogA hlogB
    (Real.strictMonoOn_log.monotoneOn hAPos hBPos hAB)

/-- Uniform high-height logarithmic-derivative estimate throughout the HT
small-beta branch. -/
theorem exists_smoothSaddleHT_eventually_highHeight_logDeriv_le_vk_logLog
    {epsilon : ℝ} (hEpsilon : 0 < epsilon)
    (hEpsilonOne : epsilon < 1) :
    ∃ c H C : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧ 0 < C ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
        0 < beta →
        beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
        H ≤ |t| →
        |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
        ‖deriv riemannZeta (smoothSaddleHTSourceExponent beta t) /
            riemannZeta (smoothSaddleHTSourceExponent beta t)‖ ≤
          C * (GafniTao.vinogradovKorobovDenominator
              (|t| + smoothSaddleHTContourHeight y epsilon) *
            GafniTao.fordVKLogLog
              (|t| + smoothSaddleHTContourHeight y epsilon)) := by
  obtain ⟨c, H, hc, hH, hZeroFree, hHalf⟩ :=
    exists_smoothSaddleHT_native_vK_halfWidth
  let C := smoothSaddleHTVariableDiskPhysicalCoefficient c
  have hC : 0 < C :=
    smoothSaddleHTVariableDiskPhysicalCoefficient_pos hc
  refine ⟨c, H, C, hc, hH, hC, hZeroFree, ?_⟩
  let R : ℝ := Real.exp (Real.exp (max (c / 2) 1))
  have hRBase : Real.exp (Real.exp 1) ≤ R := by
    dsimp [R]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (le_max_right _ _))
  have hUR : GafniTao.fordVKLogLog R = max (c / 2) 1 := by
    unfold GafniTao.fordVKLogLog
    dsimp [R]
    rw [Real.log_exp, Real.log_exp]
  filter_upwards
      [eventually_ge_atTop (2 : ℕ),
      eventually_three_mul_smoothSaddleHTContourShift_le_vk_actualHeight
        hc hEpsilon hEpsilonOne,
      eventually_three_mul_smoothSaddleHTContourShift_le_one hEpsilonOne,
      eventually_smoothSaddleHT_native_contourHeight (H := H) hEpsilonOne,
      eventually_smoothSaddleHT_native_contourHeight (H := R) hEpsilonOne,
      eventually_smoothSaddleHT_native_contourHeight (H := (1 : ℝ))
        hEpsilonOne] with y hy hWidth hDepth hHeight hRHeight hOneHeight
  intro beta t hbeta hbetaUpper htHigh htCeiling
  let A : ℝ := |t| + smoothSaddleHTContourHeight y epsilon
  let w : ℝ := c / GafniTao.vinogradovKorobovDenominator A
  have hHA : H ≤ A := by simpa [A] using hHeight t
  have hABase : Real.exp (Real.exp 1) ≤ A := hH.trans hHA
  have hHalfA : w ≤ 1 / 2 := by
    simpa [w, A] using hHalf hHA
  have hWidthA : 3 * smoothSaddleHTContourShift y epsilon ≤ w := by
    simpa [w, A] using hWidth t htCeiling
  have hRadius : 2 * w ≤ smoothSaddleHTContourHeight y epsilon := by
    have hwTwo : 2 * w ≤ 1 := by linarith
    have hOne : 1 ≤ smoothSaddleHTContourHeight y epsilon := by
      have := hOneHeight 0
      simpa using this
    exact hwTwo.trans hOne
  have hbetaThird : beta ≤ 2 * w / 3 := by
    have hshiftNonneg :=
      (smoothSaddleHTContourShift_pos hy epsilon).le
    nlinarith
  have hRA : R ≤ A := by simpa [A] using hRHeight t
  have hUA : max (c / 2) 1 ≤ GafniTao.fordVKLogLog A := by
    rw [← hUR]
    exact fordVKLogLog_mono hRBase hRA
  have hcU : c / 2 ≤ GafniTao.fordVKLogLog A :=
    (le_max_left _ _).trans hUA
  have hUOne : 1 ≤ GafniTao.fordVKLogLog A :=
    (le_max_right _ _).trans hUA
  have htFive : 5 ≤ |t| := five_le_exp_exp_one.trans (hH.trans htHigh)
  exact norm_riemannZeta_logDeriv_smoothSaddleHTSourceExponent_le_vk_logLog
    hZeroFree hc hHA hABase hHalfA htFive hRadius hbeta.le hbetaThird
      hcU hUOne

/-- High-height form for the actual origin residue used by the shifted HT
contour. -/
theorem exists_smoothSaddleHT_eventually_highHeight_originResidue_le_vk_logLog
    {epsilon : ℝ} (hEpsilon : 0 < epsilon)
    (hEpsilonOne : epsilon < 1) :
    ∃ c H C : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧ 0 < C ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
        0 < beta →
        beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
        H ≤ |t| →
        |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
        ‖smoothSaddleHTShiftedOriginResidue
            (smoothSaddleHTSourceExponent beta t)‖ ≤
          C * (GafniTao.vinogradovKorobovDenominator
              (|t| + smoothSaddleHTContourHeight y epsilon) *
            GafniTao.fordVKLogLog
              (|t| + smoothSaddleHTContourHeight y epsilon)) := by
  obtain ⟨c, H, C, hc, hH, hC, hZeroFree, hlog⟩ :=
    exists_smoothSaddleHT_eventually_highHeight_logDeriv_le_vk_logLog
      hEpsilon hEpsilonOne
  refine ⟨c, H, C, hc, hH, hC, hZeroFree, ?_⟩
  filter_upwards
      [hlog, eventually_ge_atTop (2 : ℕ),
      eventually_three_mul_smoothSaddleHTContourShift_le_one hEpsilonOne,
      eventually_three_mul_smoothSaddleHTContourShift_le_vk_actualHeight
        hc hEpsilon hEpsilonOne] with y hlog hy hdepth hwidth
  intro beta t hbeta hbetaUpper htHigh htCeiling
  have hshift := smoothSaddleHTContourShift_pos hy epsilon
  have hdepth' : beta + smoothSaddleHTContourShift y epsilon ≤ 1 := by
    linarith
  have hwidth' : beta + smoothSaddleHTContourShift y epsilon ≤
      c / GafniTao.vinogradovKorobovDenominator
        (|t| + smoothSaddleHTContourHeight y epsilon) := by
    exact (by linarith :
      beta + smoothSaddleHTContourShift y epsilon ≤
        3 * smoothSaddleHTContourShift y epsilon) |>.trans
          (hwidth t htCeiling)
  have htStrict : |t| < smoothSaddleHTContourHeight y epsilon :=
    htCeiling.trans_lt
      (smoothSaddleHTFrequencyCeiling_lt_contourHeight y epsilon)
  have hheight : H ≤ |t| + smoothSaddleHTContourHeight y epsilon := by
    have hTPos := smoothSaddleHTContourHeight_pos y epsilon
    linarith
  have hright := smoothSaddleHTContourRight_gt hy beta
  have heq :=
    smoothSaddleHTShiftedOriginResidue_sourceExponent_eq_neg_logDeriv_of_vK
      hZeroFree hshift hbeta hright htStrict hdepth' hheight hwidth'
  rw [heq, norm_neg, logDeriv_apply]
  exact hlog beta t hbeta hbetaUpper htHigh htCeiling

/-- Complete small-beta origin-residue bound.  The low-height compact term
and the high-height variable-disk term both collapse to the source pole
scale `1/beta`. -/
theorem exists_smoothSaddleHT_eventually_originResidue_le_div_beta
    {epsilon : ℝ} (hEpsilon : 0 < epsilon)
    (hEpsilonOne : epsilon < 1) :
    ∃ c H K : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧ 0 < K ∧
      GafniTao.VinogradovKorobovRectangleZeroFree c H ∧
      ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
        0 < beta →
        beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
        |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
        ‖smoothSaddleHTShiftedOriginResidue
            (smoothSaddleHTSourceExponent beta t)‖ ≤ K / beta := by
  obtain ⟨c, H, C₁, hc, hH, hC₁, hZeroFree, hHigh⟩ :=
    exists_smoothSaddleHT_eventually_highHeight_originResidue_le_vk_logLog
      hEpsilon hEpsilonOne
  obtain ⟨C₀, hC₀, hLow⟩ :=
    exists_norm_smoothSaddleHTShiftedOriginResidue_lowHeight_le
      hc hH hZeroFree
  let K : ℝ := max C₁ (C₀ + 1)
  have hK : 0 < K := hC₁.trans_le (le_max_left _ _)
  have hD := GafniTao.vinogradovKorobovDenominator_pos hH
  have hcompactScale : 0 < c / (4 * GafniTao.vinogradovKorobovDenominator H) :=
    div_pos hc (mul_pos (by norm_num) hD)
  refine ⟨c, H, K, hc, hH, hK, hZeroFree, ?_⟩
  filter_upwards
      [hHigh,
      eventually_vk_actualHeight_mul_logLog_le_div_beta
        (c := (1 : ℝ)) (by norm_num) hEpsilon hEpsilonOne,
      eventually_smoothSaddleHTContourShift_le_const
        hcompactScale hEpsilonOne,
      eventually_three_mul_smoothSaddleHTContourShift_le_one
        hEpsilonOne,
      eventually_ge_atTop (2 : ℕ)] with y hHigh hAbsorb hCompact hDepth hy
  intro beta t hbeta hbetaUpper htCeiling
  have hbetaOne : beta ≤ 1 := by
    have hshiftNonneg : 0 ≤ smoothSaddleHTContourShift y epsilon :=
      (smoothSaddleHTContourShift_pos hy epsilon).le
    linarith
  by_cases htLow : |t| ≤ H
  · have hbetaCompact :
        beta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) := by
      calc
        beta ≤ 2 * smoothSaddleHTContourShift y epsilon := hbetaUpper
        _ ≤ 2 * (c / (4 * GafniTao.vinogradovKorobovDenominator H)) :=
          mul_le_mul_of_nonneg_left hCompact (by norm_num)
        _ = c / (2 * GafniTao.vinogradovKorobovDenominator H) := by ring
    have hres := hLow hbeta hbetaCompact htLow
    rw [le_div_iff₀ hbeta]
    calc
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ * beta ≤
        (C₀ + 1 / beta) * beta :=
          mul_le_mul_of_nonneg_right hres hbeta.le
      _ = C₀ * beta + 1 := by field_simp
      _ ≤ C₀ + 1 := by nlinarith
      _ ≤ K := le_max_right _ _
  · have htHigh : H ≤ |t| := le_of_not_ge htLow
    have hres := hHigh beta t hbeta hbetaUpper htHigh htCeiling
    have hDU := hAbsorb beta t hbeta hbetaUpper htCeiling
    rw [le_div_iff₀ hbeta]
    calc
      ‖smoothSaddleHTShiftedOriginResidue
          (smoothSaddleHTSourceExponent beta t)‖ * beta ≤
        (C₁ * (GafniTao.vinogradovKorobovDenominator
            (|t| + smoothSaddleHTContourHeight y epsilon) *
          GafniTao.fordVKLogLog
            (|t| + smoothSaddleHTContourHeight y epsilon))) * beta :=
          mul_le_mul_of_nonneg_right hres hbeta.le
      _ ≤ C₁ := by
        have hC₁Nonneg := hC₁.le
        rw [mul_assoc]
        have := mul_le_mul_of_nonneg_left
          (show (GafniTao.vinogradovKorobovDenominator
              (|t| + smoothSaddleHTContourHeight y epsilon) *
            GafniTao.fordVKLogLog
              (|t| + smoothSaddleHTContourHeight y epsilon)) * beta ≤ 1 by
            exact (le_div_iff₀ hbeta).mp hDU)
          hC₁Nonneg
        simpa using this
      _ ≤ K := le_max_left _ _

end

end Tao2026
