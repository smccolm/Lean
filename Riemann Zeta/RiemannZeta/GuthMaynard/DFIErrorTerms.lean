import RiemannZeta.GuthMaynard.DFIEquation24DoubleDual
import Mathlib.Analysis.Analytic.IteratedFDeriv
import RiemannZeta.GuthMaynard.DFIEquation29
import RiemannZeta.GuthMaynard.DFIEquation30
import RiemannZeta.GuthMaynard.KloostermanComposite
import RiemannZeta.GuthMaynard.ArithmeticCoefficients

/-!
# DFI equations (24)--(30): quantitative error assembly

This module estimates the eight non-main branches isolated by the exact
equation-(24) decomposition.  It keeps the complete Weil--Estermann factor
and the Mellin--Voronoi weights visible so that the source truncations from
equation (29) can be inserted without an assumed error certificate.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

/-- The native divisor bound in the exact normed form required by the two
Voronoi frequency sums in DFI equation (29). -/
theorem exists_norm_divisorWeight_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ‖divisorWeight n‖ ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := divisorCountBound_native ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  simpa [divisorWeight] using hdiv n hn

/-- Algebraic normalization of the divisor loss, the Voronoi quarter-power,
and `k` integrations by parts into the frequency exponent used in the two
tails of DFI equation (29). -/
theorem rpow_mul_neg_quarter_mul_div_pow
    {x z ε : ℝ} {k : ℕ} (hx : 0 < x) :
    x ^ ε * x ^ (-(1 / 4 : ℝ)) * (z / x) ^ k =
      z ^ k * x ^ (ε - 1 / 4 - k) := by
  have hquarter :
      x ^ ε * x ^ (-(1 / 4 : ℝ)) = x ^ (ε - 1 / 4) := by
    rw [← Real.rpow_add hx]
    ring
  calc
    x ^ ε * x ^ (-(1 / 4 : ℝ)) * (z / x) ^ k =
        z ^ k * ((x ^ ε * x ^ (-(1 / 4 : ℝ))) / x ^ k) := by
      rw [div_pow]
      ring
    _ = z ^ k * (x ^ (ε - 1 / 4) / x ^ k) := by
      rw [hquarter]
    _ = z ^ k * x ^ (ε - 1 / 4 - k) := by
      congr 1
      exact (Real.rpow_sub_natCast (ne_of_gt hx) (ε - 1 / 4) k).symm

/-- One frequency of the full DFI equation-(29) recurrence, after inserting
the native divisor bound.  This is the exact algebra used twice in the
double-tail corner. -/
theorem divisor_recurrence_frequency_le
    {C ε R S D Z : ℝ} {n k : ℕ}
    (hn : 0 < n) (hC : 0 ≤ C) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hdiv : ‖divisorWeight n‖ ≤ C * (n : ℝ) ^ ε)
    (hrec : R ^ k * S ^ k ≤
      (4 * D) ^ k * (Z / (n : ℝ)) ^ k) :
    ‖divisorWeight n‖ *
        (R ^ k * (S ^ k * (n : ℝ) ^ (-(1 / 4 : ℝ)))) ≤
      C * (4 * D) ^ k * Z ^ k *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnε : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hnR.le _
  have hnq : 0 ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg hnR.le _
  calc
    ‖divisorWeight n‖ *
        (R ^ k * (S ^ k * (n : ℝ) ^ (-(1 / 4 : ℝ)))) =
      ‖divisorWeight n‖ *
        ((R ^ k * S ^ k) * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
    _ ≤ (C * (n : ℝ) ^ ε) *
        (((4 * D) ^ k * (Z / (n : ℝ)) ^ k) *
          (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
      gcongr
    _ = C * (4 * D) ^ k *
        (((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) *
          (Z / (n : ℝ)) ^ k) := by ring
    _ = C * (4 * D) ^ k * Z ^ k *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      rw [show (n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          (Z / (n : ℝ)) ^ k =
          Z ^ k * (n : ℝ) ^ (ε - 1 / 4 - k) by
        exact rpow_mul_neg_quarter_mul_div_pow hnR]
      ring

/-- Explicit norm of the logarithmic main operator on a positive compact
interval, in the form used for the mixed terms of DFI (24). -/
noncomputable def dfiVoronoiMainIntervalNorm
    (q : ℕ) (A B : ℝ) : ℝ :=
  (q : ℝ)⁻¹ * (B - A) *
    (|Real.log A| + |Real.log B| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|)

/-- Quantitative operator norm for the logarithmic main term in the divisor
Voronoi formula.  The estimate is deliberately stated on the actual support
interval: it is the device used below to integrate the source-uniform
equation-(29) bounds through the untransformed variable of each mixed branch
in DFI (24). -/
theorem norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    {A B K : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (q : ℕ) (hq : 0 < q) {g : ℝ → ℂ}
    (hSupport : Function.support g ⊆ Set.Icc A B)
    (hBound : ∀ x ∈ Set.Icc A B, ‖g x‖ ≤ K) :
    ‖dfiVoronoiMainTerm q g‖ ≤
      (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  let W : ℝ := |Real.log A| + |Real.log B| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPoint (x : ℝ) (hx : x ∈ Set.Icc A B) :
      ‖((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g x‖ ≤ W * K := by
    have hxpos : 0 < x := hA.trans_le hx.1
    have hlogLower : Real.log A ≤ Real.log x :=
      Real.log_le_log hA hx.1
    have hlogUpper : Real.log x ≤ Real.log B :=
      Real.log_le_log hxpos hx.2
    have hlogAbs : |Real.log x| ≤ |Real.log A| + |Real.log B| := by
      rw [abs_le]
      constructor
      · have hnegA : -|Real.log A| ≤ Real.log A := neg_abs_le _
        linarith [abs_nonneg (Real.log B)]
      · have hBabs : Real.log B ≤ |Real.log B| := le_abs_self _
        linarith [abs_nonneg (Real.log A)]
    have hWeight :
        ‖(dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)‖ ≤ W := by
      have hlogq : ‖Complex.log (q : ℂ)‖ = |Real.log q| := by
        calc
          ‖Complex.log (q : ℂ)‖ = ‖(Real.log q : ℂ)‖ := by
            exact congrArg norm Complex.natCast_log |>.symm
          _ = |Real.log q| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      rw [dfiSafeLog_eq_log hx.1]
      calc
        ‖(Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)‖ ≤
            ‖(Real.log x : ℂ) +
              2 * Real.eulerMascheroniConstant‖ +
              ‖2 * Complex.log (q : ℂ)‖ := by
          exact norm_sub_le _ _
        _ ≤ ‖(Real.log x : ℂ)‖ +
              ‖(2 * Real.eulerMascheroniConstant : ℂ)‖ +
              ‖2 * Complex.log (q : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
        _ = |Real.log x| + 2 * |Real.eulerMascheroniConstant| +
            2 * |Real.log q| := by
          simp only [norm_mul, norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs]
          rw [hlogq]
        _ ≤ W := by
          dsimp [W]
          linarith
    rw [norm_mul]
    exact mul_le_mul hWeight (hBound x hx) (norm_nonneg _) hW
  rw [dfiVoronoiMainTerm_eq_Icc hA q hSupport, norm_mul]
  have hIntegral := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume)
    (f := fun x : ℝ =>
      ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * g x)
    (s := Set.Icc A B) isCompact_Icc.measure_lt_top hPoint
  rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hAB)] at hIntegral
  calc
    ‖((q : ℂ)⁻¹)‖ *
        ‖∫ x in Set.Icc A B,
          ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)) * g x‖ ≤
        (q : ℝ)⁻¹ * ((W * K) * (B - A)) := by
      rw [norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = (q : ℝ)⁻¹ * (B - A) * W * K := by ring

/-- The logarithmic main operator controlled by the actual `L¹` mass of
its input.  This is the form used with DFI equation (30), where replacing
the mass by a pointwise supremum would lose the source exponent. -/
theorem norm_dfiVoronoiMainTerm_le_integral_norm
    {A B : ℝ} (hA : 0 < A)
    (q : ℕ) (hq : 0 < q) {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g)
    (hSupport : Function.support g ⊆ Set.Icc A B) :
    ‖dfiVoronoiMainTerm q g‖ ≤
      (q : ℝ)⁻¹ *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        (∫ x in Set.Icc A B, ‖g x‖) := by
  let W : ℝ := |Real.log A| + |Real.log B| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hWeightContinuous : ContinuousOn (fun x : ℝ =>
      ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * g x) (Set.Icc A B) := by
    have hLog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ))
        (Set.Icc A B) := by
      exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono (fun x (hx : x ∈ Set.Icc A B) =>
          ne_of_gt (hA.trans_le hx.1)))
    have hSafe : Set.EqOn (fun x : ℝ => (dfiSafeLog A x : ℂ))
        (fun x : ℝ => (Real.log x : ℂ)) (Set.Icc A B) := by
      intro x hx
      change ((dfiSafeLog A x : ℝ) : ℂ) = (Real.log x : ℂ)
      rw [dfiSafeLog_eq_log hx.1]
    exact ((hLog.congr hSafe).add continuousOn_const |>.sub
      continuousOn_const).mul hg.continuous.continuousOn
  have hIntegrable : IntegrableOn (fun x : ℝ =>
      ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * g x) (Set.Icc A B) :=
    hWeightContinuous.integrableOn_compact isCompact_Icc
  have hNormIntegrable : IntegrableOn (fun x : ℝ => W * ‖g x‖)
      (Set.Icc A B) :=
    (hg.continuous.norm.const_mul W).continuousOn.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) (hx : x ∈ Set.Icc A B) :
      ‖((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g x‖ ≤ W * ‖g x‖ := by
    have hxpos : 0 < x := hA.trans_le hx.1
    have hlogLower : Real.log A ≤ Real.log x := Real.log_le_log hA hx.1
    have hlogUpper : Real.log x ≤ Real.log B := Real.log_le_log hxpos hx.2
    have hlogAbs : |Real.log x| ≤ |Real.log A| + |Real.log B| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log A), abs_nonneg (Real.log B)]
      · linarith [le_abs_self (Real.log B), abs_nonneg (Real.log A)]
    have hlogq : ‖Complex.log (q : ℂ)‖ = |Real.log q| := by
      calc
        ‖Complex.log (q : ℂ)‖ = ‖(Real.log q : ℂ)‖ := by
          exact congrArg norm Complex.natCast_log |>.symm
        _ = |Real.log q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [dfiSafeLog_eq_log hx.1]
    calc
      ‖(Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)‖ ≤
          ‖(Real.log x : ℂ)‖ +
            ‖(2 * Real.eulerMascheroniConstant : ℂ)‖ +
            ‖2 * Complex.log (q : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
      _ = |Real.log x| + 2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log q| := by
        simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        rw [hlogq]
      _ ≤ W := by dsimp [W]; linarith
  rw [dfiVoronoiMainTerm_eq_Icc hA q hSupport, norm_mul,
    norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∫ x in Set.Icc A B,
        ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g x‖ ≤
        (q : ℝ)⁻¹ * ∫ x in Set.Icc A B, W * ‖g x‖ := by
      gcongr
      apply norm_integral_le_of_norm_le hNormIntegrable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hPoint x hx
    _ = (q : ℝ)⁻¹ * W * (∫ x in Set.Icc A B, ‖g x‖) := by
      rw [integral_const_mul]
      ring

/-- Generic `L¹` convolution geometry behind DFI equation (30).  A bounded
function supported on an `X`-by-`Y` rectangle, multiplied by any integrable
difference kernel, has total mass bounded by the shorter side times the
kernel mass. -/
theorem integral_integral_norm_mul_abs_difference_le_min
    {F : ℝ → ℝ → ℂ} {K : ℝ → ℝ} {X Y C U h : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (hC : 0 ≤ C) (hBound : ∀ x y, ‖F x y‖ ≤ C)
    (hDifference : ∀ x y, F x y ≠ 0 → x - y - h ∈ Set.Icc (-U) U)
    (hK : Continuous K)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (∫ x : ℝ, ∫ y : ℝ, ‖F x y‖ * |K (x - y - h)|) ≤
      min X Y * C * (∫ u : ℝ in Set.Icc (-U) U, |K u|) := by
  let H : ℝ × ℝ → ℝ := fun p => ‖F p.1 p.2‖ * |K (p.1 - p.2 - h)|
  have hHcont : Continuous H := by
    dsimp only [H]
    exact hF.norm.mul (hK.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFne : F p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact hSupport hFne
  have hHint : Integrable H (volume.prod volume) :=
    hHcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) hHsupport)
  let TK : ℝ → ℝ :=
    Set.indicator (Set.Icc (-U) U) (fun u => |K u|)
  have hTKint : Integrable TK := by
    dsimp only [TK]
    exact (hK.abs.continuousOn.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  let D : ℝ := ∫ u : ℝ in Set.Icc (-U) U, |K u|
  have hD : 0 ≤ D := integral_nonneg fun _ => abs_nonneg _
  have hAffine (x : ℝ) :
      (∫ y : ℝ, TK (x - y - h)) = D := by
    have hshift := MeasureTheory.integral_add_right_eq_self
      (μ := volume) (fun y : ℝ => TK (-y)) (h - x)
    have hneg := MeasureTheory.integral_neg_eq_self TK volume
    calc
      (∫ y : ℝ, TK (x - y - h)) =
          ∫ y : ℝ, TK (-(y + (h - x))) := by
            apply integral_congr_ae
            filter_upwards [] with y
            congr 1
            ring
      _ = ∫ y : ℝ, TK (-y) := hshift
      _ = ∫ u : ℝ, TK u := hneg
      _ = D := by
        dsimp only [TK, D]
        exact integral_indicator measurableSet_Icc
  have hTranslate (y : ℝ) :
      (∫ x : ℝ, TK (x - y - h)) = D := by
    calc
      (∫ x : ℝ, TK (x - y - h)) =
          ∫ x : ℝ, TK (x + (-y - h)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            congr 1
            ring
      _ = ∫ x : ℝ, TK x :=
        MeasureTheory.integral_add_right_eq_self
          (μ := volume) TK (-y - h)
      _ = D := by
        dsimp only [TK, D]
        exact integral_indicator measurableSet_Icc
  have hKaffineInt (x : ℝ) : Integrable fun y : ℝ => TK (x - y - h) := by
    have hcomp := hTKint.comp_neg.comp_add_right (h - x)
    simpa only [show ∀ y : ℝ, -(y + (h - x)) = x - y - h by
      intro y
      ring] using hcomp
  have hKtranslateInt (y : ℝ) : Integrable fun x : ℝ => TK (x - y - h) := by
    have hcomp := hTKint.comp_add_right (-y - h)
    simpa only [show ∀ x : ℝ, x + (-y - h) = x - y - h by
      intro x
      ring] using hcomp
  have hOuterX : Integrable (fun x : ℝ => ∫ y : ℝ, H (x, y)) :=
    hHint.integral_prod_left
  let RX : ℝ → ℝ := Set.indicator (Set.Icc X (2 * X)) (fun _ => C * D)
  have hRXint : Integrable RX := by
    dsimp only [RX]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hInnerX (x : ℝ) : (∫ y : ℝ, H (x, y)) ≤ RX x := by
    by_cases hx : x ∈ Set.Icc X (2 * X)
    · simp only [RX, Set.indicator_of_mem hx]
      have hSlice : Integrable fun y : ℝ => H (x, y) :=
        (hHcont.comp (by fun_prop)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
            (fun y hy => (hHsupport hy).2))
      have hMajor : Integrable fun y : ℝ => C * TK (x - y - h) :=
        (hKaffineInt x).const_mul C
      calc
        (∫ y : ℝ, H (x, y)) ≤ ∫ y : ℝ, C * TK (x - y - h) := by
          apply integral_mono hSlice hMajor
          intro y
          dsimp only [H]
          by_cases hFzero : F x y = 0
          · rw [hFzero, norm_zero, zero_mul]
            exact mul_nonneg hC (by
              dsimp only [TK]
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hu := hDifference x y hFzero
            have htk : TK (x - y - h) = |K (x - y - h)| := by
              simp only [TK, Set.indicator_of_mem hu]
            rw [htk]
            exact mul_le_mul_of_nonneg_right (hBound x y) (abs_nonneg _)
        _ = C * D := by rw [integral_const_mul, hAffine x]
    · have hzero : (fun y : ℝ => H (x, y)) = 0 := by
        funext y
        have hFzero : F x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support (Function.uncurry F) := by
            simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
          exact hx (hSupport hp).1
        simp [H, hFzero]
      simp [hzero, RX, hx]
  have hXbound : (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ X * C * D := by
    calc
      (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ ∫ x : ℝ, RX x :=
        integral_mono hOuterX hRXint hInnerX
      _ = X * C * D := by
        dsimp only [RX]
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal]
        · ring
        · nlinarith
  have hOuterY : Integrable (fun y : ℝ => ∫ x : ℝ, H (x, y)) :=
    hHint.integral_prod_right
  let RY : ℝ → ℝ := Set.indicator (Set.Icc Y (2 * Y)) (fun _ => C * D)
  have hRYint : Integrable RY := by
    dsimp only [RY]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hInnerY (y : ℝ) : (∫ x : ℝ, H (x, y)) ≤ RY y := by
    by_cases hy : y ∈ Set.Icc Y (2 * Y)
    · simp only [RY, Set.indicator_of_mem hy]
      have hSlice : Integrable fun x : ℝ => H (x, y) :=
        (hHcont.comp (by fun_prop)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
            (fun x hx => (hHsupport hx).1))
      have hMajor : Integrable fun x : ℝ => C * TK (x - y - h) :=
        (hKtranslateInt y).const_mul C
      calc
        (∫ x : ℝ, H (x, y)) ≤ ∫ x : ℝ, C * TK (x - y - h) := by
          apply integral_mono hSlice hMajor
          intro x
          dsimp only [H]
          by_cases hFzero : F x y = 0
          · rw [hFzero, norm_zero, zero_mul]
            exact mul_nonneg hC (by
              dsimp only [TK]
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hu := hDifference x y hFzero
            have htk : TK (x - y - h) = |K (x - y - h)| := by
              simp only [TK, Set.indicator_of_mem hu]
            rw [htk]
            exact mul_le_mul_of_nonneg_right (hBound x y) (abs_nonneg _)
        _ = C * D := by rw [integral_const_mul, hTranslate y]
    · have hzero : (fun x : ℝ => H (x, y)) = 0 := by
        funext x
        have hFzero : F x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support (Function.uncurry F) := by
            simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
          exact hy (hSupport hp).2
        simp [H, hFzero]
      simp [hzero, RY, hy]
  have hYbound : (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ Y * C * D := by
    rw [integral_integral_swap hHint]
    calc
      (∫ y : ℝ, ∫ x : ℝ, H (x, y)) ≤ ∫ y : ℝ, RY y :=
        integral_mono hOuterY hRYint hInnerY
      _ = Y * C * D := by
        dsimp only [RY]
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal]
        · ring
        · nlinarith
  change (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ min X Y * C * D
  rcases le_total X Y with hXY | hYX
  · rw [min_eq_left hXY]
    exact hXbound
  · rw [min_eq_right hYX]
    exact hYbound

/-- Exact two-variable Jacobian for the positive affine rescaling used in
DFI equation (23).  The whole-line formulation applies directly to the
derivative masses entering equation (29). -/
theorem integral_integral_norm_comp_mul_eq
    (F : ℝ → ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, ∫ y : ℝ, ‖F (a * x) (b * y)‖) =
      (a * b)⁻¹ * (∫ X : ℝ, ∫ Y : ℝ, ‖F X Y‖) := by
  have hInner (x : ℝ) :
      (∫ y : ℝ, ‖F (a * x) (b * y)‖) =
        b⁻¹ * ∫ Y : ℝ, ‖F (a * x) Y‖ := by
    simpa only [smul_eq_mul, abs_of_pos (inv_pos.mpr hb)] using
      (MeasureTheory.Measure.integral_comp_mul_left
        (fun Y : ℝ => ‖F (a * x) Y‖) b)
  rw [integral_congr_ae (Filter.Eventually.of_forall hInner),
    integral_const_mul]
  have hOuter :
      (∫ x : ℝ, ∫ Y : ℝ, ‖F (a * x) Y‖) =
        a⁻¹ * ∫ X : ℝ, ∫ Y : ℝ, ‖F X Y‖ := by
    simpa only [smul_eq_mul, abs_of_pos (inv_pos.mpr ha)] using
      (MeasureTheory.Measure.integral_comp_mul_left
        (fun X : ℝ => ∫ Y : ℝ, ‖F X Y‖) a)
  rw [hOuter]
  field_simp [ha.ne', hb.ne']

/-- Triangle inequality for a finite family of smooth two-variable functions
with a common compact rectangular support, after both integrations. -/
theorem integral_integral_norm_finsetSum_le
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    {A B C D : ℝ}
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i)))
    (hSupport : ∀ i ∈ s,
      Function.support (Function.uncurry (F i)) ⊆
        Set.Icc A B ×ˢ Set.Icc C D) :
    (∫ x : ℝ, ∫ y : ℝ, ‖∑ i ∈ s, F i x y‖) ≤
      ∑ i ∈ s, ∫ x : ℝ, ∫ y : ℝ, ‖F i x y‖ := by
  let G : ℝ → ℝ → ℂ := fun x y => ∑ i ∈ s, F i x y
  have hG : Continuous (Function.uncurry G) := by
    dsimp only [G, Function.uncurry_apply_pair]
    fun_prop
  have hGSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc A B ×ˢ Set.Icc C D := by
    intro p hp
    by_contra hout
    have hall : ∀ i ∈ s, F i p.1 p.2 = 0 := by
      intro i hi
      by_contra hne
      exact hout (hSupport i hi (by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hne))
    apply hp
    change (∑ i ∈ s, F i p.1 p.2) = 0
    exact Finset.sum_eq_zero fun i hi => hall i hi
  have hGI : Integrable (fun p : ℝ × ℝ => ‖G p.1 p.2‖)
      (volume.prod volume) :=
    hG.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) (by
          intro p hp
          have hne : G p.1 p.2 ≠ 0 := by simpa using hp
          exact hGSupport (by simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)))
  have hFI : ∀ i ∈ s, Integrable
      (fun p : ℝ × ℝ => ‖F i p.1 p.2‖) (volume.prod volume) := by
    intro i hi
    exact (hF i hi).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) (by
          intro p hp
          have hne : F i p.1 p.2 ≠ 0 := by simpa using hp
          exact hSupport i hi (by simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)))
  have hInner (x : ℝ) :
      (∫ y : ℝ, ‖G x y‖) ≤ ∑ i ∈ s, ∫ y : ℝ, ‖F i x y‖ := by
    have hGi : Integrable fun y : ℝ => ‖G x y‖ :=
      (hG.comp (continuous_const.prodMk continuous_id)).norm
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (by
            intro y hy
            have hne : G x y ≠ 0 := by simpa using hy
            exact (hGSupport (show
              (x, y) ∈ Function.support (Function.uncurry G) by
                simpa only [Function.mem_support,
                  Function.uncurry_apply_pair] using hne)).2))
    have hFis : ∀ i ∈ s, Integrable fun y : ℝ => ‖F i x y‖ := by
      intro i hi
      exact ((hF i hi).comp (continuous_const.prodMk continuous_id)).norm
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (by
            intro y hy
            have hne : F i x y ≠ 0 := by simpa using hy
            exact (hSupport i hi (show
              (x, y) ∈ Function.support (Function.uncurry (F i)) by
                simpa only [Function.mem_support,
                  Function.uncurry_apply_pair] using hne)).2))
    calc
      (∫ y : ℝ, ‖G x y‖) ≤ ∫ y : ℝ, ∑ i ∈ s, ‖F i x y‖ := by
        apply integral_mono hGi (integrable_finsetSum s hFis)
        intro y
        dsimp only [G]
        exact norm_sum_le _ _
      _ = ∑ i ∈ s, ∫ y : ℝ, ‖F i x y‖ :=
        integral_finsetSum s hFis
  have hLeft : Integrable (fun x : ℝ => ∫ y : ℝ, ‖G x y‖) :=
    hGI.integral_prod_left
  have hRight : Integrable
      (fun x : ℝ => ∑ i ∈ s, ∫ y : ℝ, ‖F i x y‖) := by
    apply integrable_finsetSum
    intro i hi
    exact (hFI i hi).integral_prod_left
  calc
    (∫ x : ℝ, ∫ y : ℝ, ‖∑ i ∈ s, F i x y‖) =
        ∫ x : ℝ, ∫ y : ℝ, ‖G x y‖ := by rfl
    _ ≤ ∫ x : ℝ, ∑ i ∈ s, ∫ y : ℝ, ‖F i x y‖ :=
      integral_mono hLeft hRight hInner
    _ = ∑ i ∈ s, ∫ x : ℝ, ∫ y : ℝ, ‖F i x y‖ := by
      rw [integral_finsetSum s]
      intro i hi
      exact (hFI i hi).integral_prod_left

/-- Integrated equation-(21) Leibniz rule with the sharp convolution
geometry kept term by term.  This is the analytic bridge from derivative
profiles for the physical source and the delta kernel to the `L¹` profile
required by equation (29). -/
theorem integral_integral_norm_dfiLocalizedWeight_le_convolution
    {G : ℝ → ℝ → ℂ} {δ : ℝ → ℝ} {X Y U h : ℝ}
    (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (hDifference : ∀ x y, G x y ≠ 0 → x - y - h ∈ Set.Icc (-U) U)
    (hδ : ContDiff ℝ ∞ δ) (i : ℕ) {C : ℕ → ℝ}
    (hC : ∀ r ≤ i, 0 ≤ C r)
    (hBound : ∀ r ≤ i, ∀ x y, ‖dfiMixedDeriv r 0 G x y‖ ≤ C r)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i 0
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
      min X Y * ∑ r ∈ Finset.range (i + 1),
        (i.choose r : ℝ) * C r *
          (∫ u : ℝ in Set.Icc (-U) U, ‖iteratedDeriv (i - r) δ u‖) := by
  let δc : ℝ → ℂ := fun u => (δ u : ℂ)
  let T : ℕ → ℝ → ℝ → ℂ := fun r x y =>
    (i.choose r : ℂ) * dfiMixedDeriv r 0 G x y *
      iteratedDeriv (i - r) δc (x - y - h)
  have hδc : ContDiff ℝ ∞ δc := Complex.ofRealCLM.contDiff.comp hδ
  have hLeib (x y : ℝ) :
      dfiMixedDeriv i 0 (dfiLocalizedWeight G δc h) x y =
        ∑ r ∈ Finset.range (i + 1), T r x y := by
    simpa [δc, T] using dfiEquation21Leibniz hG hδc h x y i 0
  have hTsmooth (r : ℕ) : Continuous (Function.uncurry (T r)) := by
    dsimp only [T, Function.uncurry_apply_pair]
    have hFr := (contDiff_uncurry_dfiMixedDeriv hG r 0).continuous
    have hKr := (hδc.continuous_iteratedDeriv (i - r)
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top (i - r))))).comp
        (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 - p.2 - h))
    exact (continuous_const.mul hFr).mul hKr
  have hTsupport (r : ℕ) :
      Function.support (Function.uncurry (T r)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFrne : dfiMixedDeriv r 0 G p.1 p.2 ≠ 0 := by
      intro hz
      apply hp
      change T r p.1 p.2 = 0
      simp [T, hz]
    have hts : tsupport (Function.uncurry G) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc)
    exact hts (support_dfiMixedDeriv_subset_tsupport hG r 0 (by
      simpa only [Function.mem_support,
        Function.uncurry_apply_pair] using hFrne))
  change (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i 0 (dfiLocalizedWeight G δc h) x y‖) ≤ _
  have hrewrite :
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i 0 (dfiLocalizedWeight G δc h) x y‖) =
      ∫ x : ℝ, ∫ y : ℝ,
        ‖∑ r ∈ Finset.range (i + 1), T r x y‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hLeib]
  rw [hrewrite]
  have htriangle := integral_integral_norm_finsetSum_le
    (Finset.range (i + 1)) T
    (fun r _hr => hTsmooth r) (fun r _hr => hTsupport r)
  apply htriangle.trans
  calc
    (∑ r ∈ Finset.range (i + 1),
        ∫ x : ℝ, ∫ y : ℝ, ‖T r x y‖) ≤
        ∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) *
            (min X Y * C r *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv (i - r) δ u‖)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hri : r ≤ i := by simpa using hr
      let Fr : ℝ → ℝ → ℂ := dfiMixedDeriv r 0 G
      let Kr : ℝ → ℝ := iteratedDeriv (i - r) δ
      have hFrCont : Continuous (Function.uncurry Fr) :=
        (contDiff_uncurry_dfiMixedDeriv hG r 0).continuous
      have hFrSupport : Function.support (Function.uncurry Fr) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
        exact (support_dfiMixedDeriv_subset_tsupport hG r 0).trans
          (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
      have hDiffClosed : IsClosed {p : ℝ × ℝ |
          p.1 - p.2 - h ∈ Set.Icc (-U) U} :=
        isClosed_Icc.preimage (by fun_prop)
      have hGDiffSupport : Function.support (Function.uncurry G) ⊆
          {p : ℝ × ℝ | p.1 - p.2 - h ∈ Set.Icc (-U) U} := by
        intro p hp
        exact hDifference p.1 p.2 (by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hp)
      have hFrDiff : ∀ x y, Fr x y ≠ 0 →
          x - y - h ∈ Set.Icc (-U) U := by
        intro x y hne
        exact (closure_minimal hGDiffSupport hDiffClosed)
          (support_dfiMixedDeriv_subset_tsupport hG r 0 (show
            (x, y) ∈ Function.support
              (Function.uncurry (dfiMixedDeriv r 0 G)) by
                simpa only [Fr, Function.mem_support,
                  Function.uncurry_apply_pair] using hne))
      have hKrCont : Continuous Kr :=
        hδ.continuous_iteratedDeriv (i - r)
          (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top (i - r))))
      have hconv := integral_integral_norm_mul_abs_difference_le_min
        hFrCont hFrSupport (hC r hri) (hBound r hri) hFrDiff hKrCont hX hY
      have hNorm (x y : ℝ) :
          ‖T r x y‖ = (i.choose r : ℝ) * (‖Fr x y‖ * |Kr (x - y - h)|) := by
        dsimp only [T, Fr, Kr, δc]
        rw [iteratedDeriv_ofReal_comp δ hδ (i - r), norm_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        rw [show ‖(i.choose r : ℂ)‖ = (i.choose r : ℝ) by simp]
        ring
      calc
        (∫ x : ℝ, ∫ y : ℝ, ‖T r x y‖) =
            (i.choose r : ℝ) *
              (∫ x : ℝ, ∫ y : ℝ,
                ‖Fr x y‖ * |Kr (x - y - h)|) := by
          rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
            rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hNorm x y),
              integral_const_mul]), integral_const_mul]
        _ ≤ (i.choose r : ℝ) *
            (min X Y * C r *
              (∫ u : ℝ in Set.Icc (-U) U, |Kr u|)) := by
          exact mul_le_mul_of_nonneg_left hconv (Nat.cast_nonneg _)
        _ = (i.choose r : ℝ) *
            (min X Y * C r *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv (i - r) δ u‖)) := by
          simp only [Kr, Real.norm_eq_abs]
    _ = min X Y * ∑ r ∈ Finset.range (i + 1),
        (i.choose r : ℝ) * C r *
          (∫ u : ℝ in Set.Icc (-U) U,
            ‖iteratedDeriv (i - r) δ u‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Fully mixed integrated equation-(21) Leibniz rule.  Unlike the
one-coordinate specializations, this retains the sharp diagonal convolution
mass while differentiating in both variables.  It is the literal integrated
form of DFI (28) needed when both Voronoi frequencies lie outside (29). -/
theorem integral_integral_norm_dfiLocalizedWeight_mixed_le_convolution
    {G : ℝ → ℝ → ℂ} {δ : ℝ → ℝ} {X Y U h : ℝ}
    (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (hDifference : ∀ x y, G x y ≠ 0 → x - y - h ∈ Set.Icc (-U) U)
    (hδ : ContDiff ℝ ∞ δ) (i j : ℕ) {C : ℕ → ℕ → ℝ}
    (hC : ∀ r ≤ i, ∀ s ≤ j, 0 ≤ C r s)
    (hBound : ∀ r ≤ i, ∀ s ≤ j, ∀ x y,
      ‖dfiMixedDeriv r s G x y‖ ≤ C r s)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
      min X Y * ∑ s ∈ Finset.range (j + 1),
        ∑ r ∈ Finset.range (i + 1),
          (j.choose s : ℝ) * (i.choose r : ℝ) * C r s *
            (∫ u : ℝ in Set.Icc (-U) U,
              ‖iteratedDeriv ((i - r) + (j - s)) δ u‖) := by
  let δc : ℝ → ℂ := fun u => (δ u : ℂ)
  let S : Finset (ℕ × ℕ) :=
    (Finset.range (j + 1)).product (Finset.range (i + 1))
  let T : (ℕ × ℕ) → ℝ → ℝ → ℂ := fun p x y =>
    (j.choose p.1 : ℂ) * (i.choose p.2 : ℂ) *
      (((-1 : ℝ) ^ (j - p.1)) : ℂ) *
      dfiMixedDeriv p.2 p.1 G x y *
      iteratedDeriv ((i - p.2) + (j - p.1)) δc (x - y - h)
  have hδc : ContDiff ℝ ∞ δc := Complex.ofRealCLM.contDiff.comp hδ
  have hLeib (x y : ℝ) :
      dfiMixedDeriv i j (dfiLocalizedWeight G δc h) x y =
        ∑ p ∈ S, T p x y := by
    rw [dfiEquation21Leibniz hG hδc]
    change (∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
      T (s, r) x y) = ∑ p ∈ S, T p x y
    dsimp only [S]
    exact (Finset.sum_product (β := ℂ)
      (Finset.range (j + 1)) (Finset.range (i + 1))
      (fun p => T p x y)).symm
  have hTsmooth (p : ℕ × ℕ) : Continuous (Function.uncurry (T p)) := by
    dsimp only [T, Function.uncurry_apply_pair]
    have hFr := (contDiff_uncurry_dfiMixedDeriv hG p.2 p.1).continuous
    have hKr := (hδc.continuous_iteratedDeriv
      ((i - p.2) + (j - p.1))
      (WithTop.coe_le_coe.mpr
        (le_of_lt (ENat.coe_lt_top ((i - p.2) + (j - p.1)))))).comp
          (by fun_prop : Continuous (fun z : ℝ × ℝ => z.1 - z.2 - h))
    exact ((((continuous_const.mul continuous_const).mul continuous_const).mul hFr).mul hKr)
  have hTsupport (p : ℕ × ℕ) :
      Function.support (Function.uncurry (T p)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro z hz
    have hFrne : dfiMixedDeriv p.2 p.1 G z.1 z.2 ≠ 0 := by
      intro hzero
      apply hz
      change T p z.1 z.2 = 0
      simp [T, hzero]
    exact ((support_dfiMixedDeriv_subset_tsupport hG p.2 p.1).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))) (by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hFrne)
  change (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i j (dfiLocalizedWeight G δc h) x y‖) ≤ _
  have hrewrite : (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i j (dfiLocalizedWeight G δc h) x y‖) =
      ∫ x : ℝ, ∫ y : ℝ, ‖∑ p ∈ S, T p x y‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hLeib]
  rw [hrewrite]
  have htriangle := integral_integral_norm_finsetSum_le S T
    (fun p _hp => hTsmooth p) (fun p _hp => hTsupport p)
  apply htriangle.trans
  calc
    (∑ p ∈ S, ∫ x : ℝ, ∫ y : ℝ, ‖T p x y‖) ≤
        ∑ p ∈ S,
          (j.choose p.1 : ℝ) * (i.choose p.2 : ℝ) *
            (min X Y * C p.2 p.1 *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv ((i - p.2) + (j - p.1)) δ u‖)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : p ∈ (Finset.range (j + 1)).product
          (Finset.range (i + 1)) := by simpa only [S] using hp
      have hpmem := Finset.mem_product.mp hp'
      have hsj : p.1 ≤ j := by simpa using hpmem.1
      have hri : p.2 ≤ i := by simpa using hpmem.2
      let Fp : ℝ → ℝ → ℂ := dfiMixedDeriv p.2 p.1 G
      let Kp : ℝ → ℝ := iteratedDeriv ((i - p.2) + (j - p.1)) δ
      have hFpCont : Continuous (Function.uncurry Fp) :=
        (contDiff_uncurry_dfiMixedDeriv hG p.2 p.1).continuous
      have hFpSupport : Function.support (Function.uncurry Fp) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        (support_dfiMixedDeriv_subset_tsupport hG p.2 p.1).trans
          (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
      have hDiffClosed : IsClosed {z : ℝ × ℝ |
          z.1 - z.2 - h ∈ Set.Icc (-U) U} :=
        isClosed_Icc.preimage (by fun_prop)
      have hGDiffSupport : Function.support (Function.uncurry G) ⊆
          {z : ℝ × ℝ | z.1 - z.2 - h ∈ Set.Icc (-U) U} := by
        intro z hz
        exact hDifference z.1 z.2 (by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hz)
      have hFpDiff : ∀ x y, Fp x y ≠ 0 →
          x - y - h ∈ Set.Icc (-U) U := by
        intro x y hne
        exact (closure_minimal hGDiffSupport hDiffClosed)
          (support_dfiMixedDeriv_subset_tsupport hG p.2 p.1 (show
            (x, y) ∈ Function.support (Function.uncurry Fp) by
              simpa only [Fp, Function.mem_support,
                Function.uncurry_apply_pair] using hne))
      have hKpCont : Continuous Kp :=
        hδ.continuous_iteratedDeriv ((i - p.2) + (j - p.1))
          (WithTop.coe_le_coe.mpr
            (le_of_lt (ENat.coe_lt_top ((i - p.2) + (j - p.1)))))
      have hconv := integral_integral_norm_mul_abs_difference_le_min
        hFpCont hFpSupport (hC p.2 hri p.1 hsj)
          (hBound p.2 hri p.1 hsj) hFpDiff hKpCont hX hY
      have hNorm (x y : ℝ) :
          ‖T p x y‖ = (j.choose p.1 : ℝ) * (i.choose p.2 : ℝ) *
            (‖Fp x y‖ * |Kp (x - y - h)|) := by
        dsimp only [T, Fp, Kp, δc]
        rw [iteratedDeriv_ofReal_comp δ hδ
          ((i - p.2) + (j - p.1)), norm_mul, norm_mul, norm_mul,
          norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simp only [Complex.norm_natCast, norm_pow]
        rw [show ‖(((-1 : ℝ) : ℂ))‖ = 1 by norm_num, one_pow]
        simp only [mul_one]
        rw [add_comm (i - p.2) (j - p.1)]
        ring
      calc
        (∫ x : ℝ, ∫ y : ℝ, ‖T p x y‖) =
            (j.choose p.1 : ℝ) * (i.choose p.2 : ℝ) *
              (∫ x : ℝ, ∫ y : ℝ,
                ‖Fp x y‖ * |Kp (x - y - h)|) := by
          rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
            rw [integral_congr_ae
              (Filter.Eventually.of_forall fun y => hNorm x y),
              integral_const_mul]), integral_const_mul]
        _ ≤ (j.choose p.1 : ℝ) * (i.choose p.2 : ℝ) *
            (min X Y * C p.2 p.1 *
              (∫ u : ℝ in Set.Icc (-U) U, |Kp u|)) := by
          exact mul_le_mul_of_nonneg_left hconv (by positivity)
        _ = (j.choose p.1 : ℝ) * (i.choose p.2 : ℝ) *
            (min X Y * C p.2 p.1 *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv ((i - p.2) + (j - p.1)) δ u‖)) := by
          simp only [Kp, Real.norm_eq_abs]
    _ = ∑ s ∈ Finset.range (j + 1),
        ∑ r ∈ Finset.range (i + 1),
          (j.choose s : ℝ) * (i.choose r : ℝ) *
            (min X Y * C r s *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv ((i - r) + (j - s)) δ u‖)) := by
      dsimp only [S]
      exact Finset.sum_product (β := ℝ)
        (Finset.range (j + 1)) (Finset.range (i + 1)) _
    _ = min X Y * ∑ s ∈ Finset.range (j + 1),
        ∑ r ∈ Finset.range (i + 1),
          (j.choose s : ℝ) * (i.choose r : ℝ) * C r s *
            (∫ u : ℝ in Set.Icc (-U) U,
              ‖iteratedDeriv ((i - r) + (j - s)) δ u‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Second-variable counterpart of the integrated equation-(21) Leibniz
rule.  It is derived by an exact coordinate swap; evenness of the kernel
removes the resulting sign in the displacement. -/
theorem integral_integral_norm_dfiLocalizedWeight_second_le_convolution
    {G : ℝ → ℝ → ℂ} {δ : ℝ → ℝ} {X Y U h : ℝ}
    (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (hDifference : ∀ x y, G x y ≠ 0 → x - y - h ∈ Set.Icc (-U) U)
    (hδ : ContDiff ℝ ∞ δ) (hδeven : ∀ u, δ (-u) = δ u)
    (j : ℕ) {C : ℕ → ℝ}
    (hC : ∀ r ≤ j, 0 ≤ C r)
    (hBound : ∀ r ≤ j, ∀ x y, ‖dfiMixedDeriv 0 r G x y‖ ≤ C r)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv 0 j
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
      min X Y * ∑ r ∈ Finset.range (j + 1),
        (j.choose r : ℝ) * C r *
          (∫ u : ℝ in Set.Icc (-U) U, ‖iteratedDeriv (j - r) δ u‖) := by
  let Gs : ℝ → ℝ → ℂ := fun y x => G x y
  let H : ℝ → ℝ → ℂ :=
    dfiLocalizedWeight G (fun u => (δ u : ℂ)) h
  let Hs : ℝ → ℝ → ℂ :=
    dfiLocalizedWeight Gs (fun u => (δ u : ℂ)) (-h)
  have hGs : ContDiff ℝ ∞ (Function.uncurry Gs) := by
    simpa only [Gs, Function.uncurry_apply_pair] using hG.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)))
  have hSupportGs : Function.support (Function.uncurry Gs) ⊆
      Set.Icc Y (2 * Y) ×ˢ Set.Icc X (2 * X) := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry G) by
        simpa only [Gs, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hDifferenceGs : ∀ x y, Gs x y ≠ 0 →
      x - y - (-h) ∈ Set.Icc (-U) U := by
    intro x y hne
    have hu := hDifference y x (by simpa only [Gs] using hne)
    constructor <;> linarith [hu.1, hu.2]
  have hBoundGs : ∀ r ≤ j, ∀ x y,
      ‖dfiMixedDeriv r 0 Gs x y‖ ≤ C r := by
    intro r hr x y
    simpa only [Gs, dfiMixedDeriv, iteratedDeriv_zero] using hBound r hr y x
  have hraw := integral_integral_norm_dfiLocalizedWeight_le_convolution
    hGs hSupportGs hDifferenceGs hδ j hC hBoundGs hY hX
  have hHsH (x y : ℝ) : Hs y x = H x y := by
    dsimp only [Hs, H, Gs, dfiLocalizedWeight]
    rw [show y - x - -h = -(x - y - h) by ring, hδeven]
  have hMixed (x y : ℝ) :
      dfiMixedDeriv j 0 Hs y x = dfiMixedDeriv 0 j H x y := by
    simp only [dfiMixedDeriv, iteratedDeriv_zero]
    have heq : (fun y' => Hs y' x) = H x := by
      funext y'
      exact hHsH x y'
    rw [heq]
  have hHsmooth : ContDiff ℝ ∞ (Function.uncurry H) := by
    dsimp only [H]
    unfold dfiLocalizedWeight Function.uncurry
    exact hG.mul ((Complex.ofRealCLM.contDiff.comp hδ).comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hHsupport : Function.support (Function.uncurry H) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hGne : G p.1 p.2 ≠ 0 := by
      intro hz
      apply hp
      simp [H, Function.uncurry, dfiLocalizedWeight, hz]
    exact hSupport (by
      simpa only [Function.mem_support,
        Function.uncurry_apply_pair] using hGne)
  have hFint : Integrable
      (Function.uncurry (fun x y => ‖dfiMixedDeriv 0 j H x y‖))
      (volume.prod volume) :=
    (contDiff_uncurry_dfiMixedDeriv hHsmooth 0 j).continuous.norm
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact
          (isCompact_Icc.prod isCompact_Icc) (by
            intro p hp
            change ‖dfiMixedDeriv 0 j H p.1 p.2‖ ≠ 0 at hp
            have hne : dfiMixedDeriv 0 j H p.1 p.2 ≠ 0 :=
              norm_ne_zero_iff.mp hp
            exact ((support_dfiMixedDeriv_subset_tsupport hHsmooth 0 j).trans
              (closure_minimal hHsupport
                (isClosed_Icc.prod isClosed_Icc))) (by
                  simpa only [Function.mem_support,
                    Function.uncurry_apply_pair] using hne)))
  have hswap :
      (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j H x y‖) =
        ∫ y : ℝ, ∫ x : ℝ, ‖dfiMixedDeriv j 0 Hs y x‖ := by
    calc
      _ = ∫ y : ℝ, ∫ x : ℝ, ‖dfiMixedDeriv 0 j H x y‖ :=
        MeasureTheory.integral_integral_swap hFint
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hMixed]
  change (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j H x y‖) ≤ _
  rw [hswap]
  simpa only [min_comm] using hraw

/-- The finite derivative-profile constant actually constructed in the proof
of the delta-kernel `L¹` estimate.  Naming it prevents later DFI estimates
from hiding a scale-dependent choice behind an existential quantifier. -/
noncomputable def dfiDeltaKernelDerivativeFiniteConstant
    (Dw : ℕ → ℝ) (J : ℕ) : ℝ :=
  (24 * max (Dw 0) (Dw 1)) * (2 / Real.log 2 + 4) +
    ∑ k ∈ Finset.range (J + 1),
      4 * Dw k * (1 / Real.log 2 + 4)

/-- Profile-explicit, scale-uniform delta-kernel derivative-mass estimate. -/
theorem integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
    {Q U : ℝ} {w : DFIDeltaWeight Q} {Dw : ℕ → ℝ}
    (hw : DFIDeltaWeightProfile w Dw) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (J : ℕ) :
    ∀ (q k : ℕ), 0 < q → k ≤ J →
      (∫ u : ℝ in Set.Icc (-U) U,
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
      dfiDeltaKernelDerivativeFiniteConstant Dw J * Real.log Q *
        ((((q : ℝ) * Q)⁻¹) ^ k) := by
  let K0 : ℝ := (24 * max (Dw 0) (Dw 1)) * (2 / Real.log 2 + 4)
  let A : ℝ := 1 / Real.log 2 + 4
  let K : ℕ → ℝ := fun k => 4 * Dw k * A
  let C : ℝ := K0 + ∑ k ∈ Finset.range (J + 1), K k
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hK0 : 0 < K0 := by
    dsimp [K0]
    have hm : 0 < max (Dw 0) (Dw 1) :=
      (hw.positive 0).trans_le (le_max_left _ _)
    positivity
  have hK : ∀ k, 0 < K k := by
    intro k
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) (hw.positive k)) hA
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg hK0
      (Finset.sum_nonneg fun k _hk => (hK k).le)
  intro q k hq hkJ
  change (∫ u : ℝ in Set.Icc (-U) U,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
    C * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ k)
  have hQpos : 0 < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  by_cases hk0 : k = 0
  · subst k
    have hzero := integral_abs_dfiDeltaKernel_Icc_le_log_of_profile
      hw hQ hU q hq
    have hK0C : K0 ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg fun r _hr => (hK r).le)
    calc
      (∫ u : ℝ in Set.Icc (-U) U,
          ‖iteratedDeriv 0 (dfiDeltaKernel w q) u‖) =
          ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro u _hu
            simp [Real.norm_eq_abs]
      _ ≤ K0 * Real.log Q := by simpa only [K0] using hzero
      _ ≤ C * Real.log Q := mul_le_mul_of_nonneg_right hK0C hlogQ
      _ = C * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ 0) := by ring
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let N : ℕ := ⌈U⌉₊
    have hU0 : 0 ≤ U := by rw [hU]; positivity
    have hUN : U ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil U
    have hSubset : Set.Icc (-U) U ⊆ Set.Icc (-(N : ℝ)) (N : ℝ) := by
      intro u hu
      exact ⟨by linarith [hu.1], hu.2.trans hUN⟩
    have hCont : Continuous
        (fun u : ℝ => ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) :=
      ((contDiff_dfiDeltaKernel w q hq).continuous_iteratedDeriv k
        (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))).norm
    have hInt : IntegrableOn
        (fun u : ℝ => ‖iteratedDeriv k (dfiDeltaKernel w q) u‖)
        (Set.Icc (-(N : ℝ)) (N : ℝ)) :=
      hCont.continuousOn.integrableOn_compact isCompact_Icc
    have hmono :
        (∫ u : ℝ in Set.Icc (-U) U,
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
        ∫ u : ℝ in Set.Icc (-(N : ℝ)) (N : ℝ),
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
      apply MeasureTheory.setIntegral_mono_set hInt
      · exact Filter.Eventually.of_forall fun u => norm_nonneg _
      · exact hSubset.eventuallyLE
    have hraw := integral_Icc_norm_iteratedDeriv_dfiDeltaKernel_le_of_profile
      hw q k N hq hkpos
    have hharm := harmonic_dfiDeltaRadius_ceil_sq_le_log hQ hU
    have hcoef : 0 ≤ 4 * Dw k * Q * (Q ^ (k + 1))⁻¹ := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (hw.positive k).le) hQpos.le)
        (inv_nonneg.mpr (pow_nonneg hQpos.le _))
    have hqpow : 0 ≤ (((q : ℝ) ^ k)⁻¹) := by positivity
    have hKC : K k ≤ C := by
      have hkmem : k ∈ Finset.range (J + 1) := by simp [hkJ]
      have hsum : K k ≤ ∑ r ∈ Finset.range (J + 1), K r :=
        Finset.single_le_sum (fun r _hr => (hK r).le) hkmem
      dsimp [C]
      exact hsum.trans (le_add_of_nonneg_left hK0.le)
    calc
      (∫ u : ℝ in Set.Icc (-U) U,
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
          ∫ u : ℝ in Set.Icc (-(N : ℝ)) (N : ℝ),
            ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := hmono
      _ ≤ (4 * Dw k * Q * (Q ^ (k + 1))⁻¹) *
          (((q : ℝ) ^ k)⁻¹) *
            (harmonic (dfiDeltaRadius Q (N + 1)) : ℝ) := by
              simpa only [N, Nat.cast_add, Nat.cast_one] using hraw
      _ ≤ (4 * Dw k * Q * (Q ^ (k + 1))⁻¹) *
          (((q : ℝ) ^ k)⁻¹) * (A * Real.log Q) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa only [N, A] using hharm)
              (mul_nonneg hcoef hqpow)
      _ = K k * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ k) := by
            dsimp [K]
            simp only [inv_pow, mul_pow, pow_succ]
            field_simp [hQpos.ne', show (q : ℝ) ≠ 0 by positivity]
      _ ≤ C * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ k) := by
            gcongr

theorem dfiDeltaKernelDerivativeFiniteConstant_pos
    {Q : ℝ} {w : DFIDeltaWeight Q} {Dw : ℕ → ℝ}
    (hw : DFIDeltaWeightProfile w Dw) (J : ℕ) :
    0 < dfiDeltaKernelDerivativeFiniteConstant Dw J := by
  unfold dfiDeltaKernelDerivativeFiniteConstant
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : 0 < max (Dw 0) (Dw 1) :=
    (hw.positive 0).trans_le (le_max_left _ _)
  have hfirst : 0 < (24 * max (Dw 0) (Dw 1)) *
      (2 / Real.log 2 + 4) := by positivity
  exact add_pos_of_pos_of_nonneg hfirst
    (Finset.sum_nonneg fun k _hk => by
      have hk : 0 < Dw k := hw.positive k
      positivity)

/-- Existential compatibility wrapper for the profile-explicit delta-kernel
estimate.  New source-uniform arguments should use the direct theorem above. -/
theorem exists_integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
    {Q U : ℝ} {w : DFIDeltaWeight Q} {Dw : ℕ → ℝ}
    (hw : DFIDeltaWeightProfile w Dw) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q k : ℕ), 0 < q → k ≤ J →
      (∫ u : ℝ in Set.Icc (-U) U,
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
      C * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ k) := by
  refine ⟨dfiDeltaKernelDerivativeFiniteConstant Dw J, ?_, ?_⟩
  · exact dfiDeltaKernelDerivativeFiniteConstant_pos hw J
  · exact integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
      hw hQ hU J

/-- Sharp physical `L¹` derivative profile for the complete equation-(23)
weight before the divisor-coordinate rescaling.  The shorter support length
is retained, and every derivative costs the source frequency `(qQ)⁻¹`. -/
theorem exists_integral_integral_norm_dfiEquation23Physical_derivative_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (i : ℕ), i ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i 0
          (dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
            (fun u => (dfiDeltaKernel w q u : ℂ)) h) x y‖) ≤
        C * min X Y * Real.log Q *
          ((((q : ℝ) * Q)⁻¹) ^ i) := by
  obtain ⟨Kδ, hKδ, hδmass⟩ :=
    exists_integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
      hwC hQ hU J
  let A : ℕ → ℝ := fun r =>
    dfiEquation2FiniteConstant Cf r *
      dfiCutoffFiniteConstant Cψ r * 2 ^ r
  let Asum : ℝ := ∑ r ∈ Finset.range (J + 1), A r
  let C : ℝ := Asum * Kδ * 3 ^ J
  have hA : ∀ r, 0 < A r := by
    intro r
    dsimp [A]
    have hcut : 0 < dfiCutoffFiniteConstant Cψ r := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk => hψC.positive k) ⟨0, by simp⟩
    exact mul_pos (mul_pos (hfC.finiteConstant_pos r) hcut)
      (pow_pos (by norm_num) r)
  have hAsum : 0 < Asum := by
    dsimp [Asum]
    exact Finset.sum_pos (fun r _hr => hA r) ⟨0, by simp⟩
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q hq hqQ h i hiJ
  let G : ℝ → ℝ → ℂ := dfiLocalizedWeight f ψ h
  let δ : ℝ → ℝ := dfiDeltaKernel w q
  let B : ℝ := ((q : ℝ) * Q)⁻¹
  have hQpos : 0 < Q := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : ContDiff ℝ ∞ (Function.uncurry G) := by
    dsimp [G]
    exact contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    dsimp [G]
    exact support_uncurry_dfiLocalizedWeight_subset hbox
  have hDifference : ∀ x y, G x y ≠ 0 →
      x - y - (h : ℝ) ∈ Set.Icc (-U) U := by
    intro x y hne
    have hψne : ψ (x - y - (h : ℝ)) ≠ 0 := by
      intro hz
      exact hne (by simp [G, dfiLocalizedWeight, hz])
    have hu := hψ.support_subset hψne
    exact ⟨hu.1.le, hu.2.le⟩
  have hδsmooth : ContDiff ℝ ∞ δ := by
    dsimp [δ]
    exact contDiff_dfiDeltaKernel w q hq
  have hUinv : U⁻¹ ≤ 2 * B := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQpos
    have hqQle : (q : ℝ) * Q ≤ 2 * U := by
      rw [hU]
      nlinarith [mul_le_mul_of_nonneg_right hqQ hQpos.le]
    have hhalf : 0 < ((q : ℝ) * Q) / 2 := by positivity
    have hhalfU : ((q : ℝ) * Q) / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (((q : ℝ) * Q) / 2)⁻¹ := inv_anti₀ hhalf hhalfU
      _ = 2 * B := by dsimp [B]; field_simp [hqQpos.ne']
  let Cr : ℕ → ℝ := fun r => Asum * (2 * B) ^ r
  have hCr : ∀ r ≤ i, 0 ≤ Cr r := by
    intro r _hr
    dsimp [Cr]
    positivity
  have hSource : ∀ r ≤ i, ∀ x y,
      ‖dfiMixedDeriv r 0 G x y‖ ≤ Cr r := by
    intro r hri x y
    have hrJ : r ≤ J := hri.trans hiJ
    have hrmem : r ∈ Finset.range (J + 1) := by simp [hrJ]
    have hAr : A r ≤ Asum := by
      dsimp [Asum]
      exact Finset.single_le_sum (fun s _hs => (hA s).le) hrmem
    have hraw :=
      (dfiEquation21_of_profiles_uniform_in_shift
        hf hfC hbox hψ hψC hscale r 0 (h : ℝ) x y).2
    calc
      ‖dfiMixedDeriv r 0 G x y‖ ≤ A r * U⁻¹ ^ r := by
        simpa only [G, A, max_eq_left (Nat.zero_le r), add_zero] using hraw
      _ ≤ Asum * U⁻¹ ^ r :=
        mul_le_mul_of_nonneg_right hAr
          (pow_nonneg (inv_nonneg.mpr hψ.U_pos.le) _)
      _ ≤ Asum * (2 * B) ^ r := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr hψ.U_pos.le) hUinv r) hAsum.le
      _ = Cr r := by rfl
  have hphysical := integral_integral_norm_dfiLocalizedWeight_le_convolution
    hG hSupport hDifference hδsmooth i hCr hSource
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  calc
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i 0
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
        min X Y * ∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) * Cr r *
            (∫ u : ℝ in Set.Icc (-U) U,
              ‖iteratedDeriv (i - r) δ u‖) := hphysical
    _ ≤ min X Y * ∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) * Cr r *
            (Kδ * Real.log Q * (B ^ (i - r))) := by
      apply mul_le_mul_of_nonneg_left _ (le_min
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y))
      apply Finset.sum_le_sum
      intro r hr
      have hri : r ≤ i := by simpa using hr
      exact mul_le_mul_of_nonneg_left
        (hδmass q (i - r) hq ((Nat.sub_le i r).trans hiJ))
        (mul_nonneg (Nat.cast_nonneg _) (hCr r hri))
    _ = min X Y * (Asum * Kδ * Real.log Q * B ^ i * 3 ^ i) := by
      have hsum :
          (∑ r ∈ Finset.range (i + 1),
            (i.choose r : ℝ) * Cr r *
              (Kδ * Real.log Q * B ^ (i - r))) =
            Asum * Kδ * Real.log Q * B ^ i *
              ∑ r ∈ Finset.range (i + 1),
                (i.choose r : ℝ) * 2 ^ r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hri : r ≤ i := by simpa using hr
        dsimp [Cr]
        rw [mul_pow]
        have hpowB : B ^ r * B ^ (i - r) = B ^ i := by
          rw [← pow_add, Nat.add_sub_of_le hri]
        rw [← hpowB]
        ring
      have hbinom :
          (∑ r ∈ Finset.range (i + 1),
            (i.choose r : ℝ) * 2 ^ r) = 3 ^ i := by
        have hb := (add_pow (2 : ℝ) 1 i).symm
        calc
          (∑ r ∈ Finset.range (i + 1),
              (i.choose r : ℝ) * 2 ^ r) = (2 + 1) ^ i := by
                simpa only [one_pow, one_mul, mul_one, mul_comm] using hb
          _ = 3 ^ i := by norm_num
      rw [hsum, hbinom]
    _ ≤ min X Y * (Asum * Kδ * Real.log Q * B ^ i * 3 ^ J) := by
      have hpow : (3 : ℝ) ^ i ≤ 3 ^ J := pow_le_pow_right₀ (by norm_num) hiJ
      apply mul_le_mul_of_nonneg_left _ (le_min
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y))
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C * min X Y * Real.log Q * B ^ i := by
      dsimp [C]
      ring

/-- Symmetric sharp physical `L¹` derivative profile for the complete
equation-(23) weight. -/
theorem exists_integral_integral_norm_dfiEquation23Physical_second_derivative_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (j : ℕ), j ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv 0 j
          (dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
            (fun u => (dfiDeltaKernel w q u : ℂ)) h) x y‖) ≤
        C * min X Y * Real.log Q *
          ((((q : ℝ) * Q)⁻¹) ^ j) := by
  obtain ⟨Kδ, hKδ, hδmass⟩ :=
    exists_integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
      hwC hQ hU J
  let A : ℕ → ℝ := fun r =>
    dfiEquation2FiniteConstant Cf r *
      dfiCutoffFiniteConstant Cψ r * 2 ^ r
  let Asum : ℝ := ∑ r ∈ Finset.range (J + 1), A r
  let C : ℝ := Asum * Kδ * 3 ^ J
  have hA : ∀ r, 0 < A r := by
    intro r
    dsimp [A]
    have hcut : 0 < dfiCutoffFiniteConstant Cψ r := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk => hψC.positive k) ⟨0, by simp⟩
    exact mul_pos (mul_pos (hfC.finiteConstant_pos r) hcut)
      (pow_pos (by norm_num) r)
  have hAsum : 0 < Asum := by
    dsimp [Asum]
    exact Finset.sum_pos (fun r _hr => hA r) ⟨0, by simp⟩
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q hq hqQ h j hjJ
  let G : ℝ → ℝ → ℂ := dfiLocalizedWeight f ψ h
  let δ : ℝ → ℝ := dfiDeltaKernel w q
  let B : ℝ := ((q : ℝ) * Q)⁻¹
  have hQpos : 0 < Q := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : ContDiff ℝ ∞ (Function.uncurry G) := by
    dsimp [G]
    exact contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    dsimp [G]
    exact support_uncurry_dfiLocalizedWeight_subset hbox
  have hDifference : ∀ x y, G x y ≠ 0 →
      x - y - (h : ℝ) ∈ Set.Icc (-U) U := by
    intro x y hne
    have hψne : ψ (x - y - (h : ℝ)) ≠ 0 := by
      intro hz
      exact hne (by simp [G, dfiLocalizedWeight, hz])
    have hu := hψ.support_subset hψne
    exact ⟨hu.1.le, hu.2.le⟩
  have hδsmooth : ContDiff ℝ ∞ δ := by
    dsimp [δ]
    exact contDiff_dfiDeltaKernel w q hq
  have hδeven : ∀ u, δ (-u) = δ u := by
    intro u
    dsimp [δ]
    exact dfiDeltaKernel_neg w q u
  have hUinv : U⁻¹ ≤ 2 * B := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQpos
    have hqQle : (q : ℝ) * Q ≤ 2 * U := by
      rw [hU]
      nlinarith [mul_le_mul_of_nonneg_right hqQ hQpos.le]
    have hhalf : 0 < ((q : ℝ) * Q) / 2 := by positivity
    have hhalfU : ((q : ℝ) * Q) / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (((q : ℝ) * Q) / 2)⁻¹ := inv_anti₀ hhalf hhalfU
      _ = 2 * B := by dsimp [B]; field_simp [hqQpos.ne']
  let Cr : ℕ → ℝ := fun r => Asum * (2 * B) ^ r
  have hCr : ∀ r ≤ j, 0 ≤ Cr r := by
    intro r _hr
    dsimp [Cr]
    positivity
  have hSource : ∀ r ≤ j, ∀ x y,
      ‖dfiMixedDeriv 0 r G x y‖ ≤ Cr r := by
    intro r hrj x y
    have hrJ : r ≤ J := hrj.trans hjJ
    have hrmem : r ∈ Finset.range (J + 1) := by simp [hrJ]
    have hAr : A r ≤ Asum := by
      dsimp [Asum]
      exact Finset.single_le_sum (fun s _hs => (hA s).le) hrmem
    have hraw :=
      (dfiEquation21_of_profiles_uniform_in_shift
        hf hfC hbox hψ hψC hscale 0 r (h : ℝ) x y).2
    calc
      ‖dfiMixedDeriv 0 r G x y‖ ≤ A r * U⁻¹ ^ r := by
        simpa only [G, A, max_eq_right (Nat.zero_le r), zero_add] using hraw
      _ ≤ Asum * U⁻¹ ^ r :=
        mul_le_mul_of_nonneg_right hAr
          (pow_nonneg (inv_nonneg.mpr hψ.U_pos.le) _)
      _ ≤ Asum * (2 * B) ^ r := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr hψ.U_pos.le) hUinv r) hAsum.le
      _ = Cr r := by rfl
  have hphysical :=
    integral_integral_norm_dfiLocalizedWeight_second_le_convolution
      hG hSupport hDifference hδsmooth hδeven j hCr hSource
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  calc
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv 0 j
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
        min X Y * ∑ r ∈ Finset.range (j + 1),
          (j.choose r : ℝ) * Cr r *
            (∫ u : ℝ in Set.Icc (-U) U,
              ‖iteratedDeriv (j - r) δ u‖) := hphysical
    _ ≤ min X Y * ∑ r ∈ Finset.range (j + 1),
          (j.choose r : ℝ) * Cr r *
            (Kδ * Real.log Q * (B ^ (j - r))) := by
      apply mul_le_mul_of_nonneg_left _ (le_min
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y))
      apply Finset.sum_le_sum
      intro r hr
      have hrj : r ≤ j := by simpa using hr
      exact mul_le_mul_of_nonneg_left
        (hδmass q (j - r) hq ((Nat.sub_le j r).trans hjJ))
        (mul_nonneg (Nat.cast_nonneg _) (hCr r hrj))
    _ = min X Y * (Asum * Kδ * Real.log Q * B ^ j * 3 ^ j) := by
      have hsum :
          (∑ r ∈ Finset.range (j + 1),
            (j.choose r : ℝ) * Cr r *
              (Kδ * Real.log Q * B ^ (j - r))) =
            Asum * Kδ * Real.log Q * B ^ j *
              ∑ r ∈ Finset.range (j + 1),
                (j.choose r : ℝ) * 2 ^ r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hrj : r ≤ j := by simpa using hr
        dsimp [Cr]
        rw [mul_pow]
        have hpowB : B ^ r * B ^ (j - r) = B ^ j := by
          rw [← pow_add, Nat.add_sub_of_le hrj]
        rw [← hpowB]
        ring
      have hbinom :
          (∑ r ∈ Finset.range (j + 1),
            (j.choose r : ℝ) * 2 ^ r) = 3 ^ j := by
        have hb := (add_pow (2 : ℝ) 1 j).symm
        calc
          (∑ r ∈ Finset.range (j + 1),
              (j.choose r : ℝ) * 2 ^ r) = (2 + 1) ^ j := by
                simpa only [one_pow, one_mul, mul_one, mul_comm] using hb
          _ = 3 ^ j := by norm_num
      rw [hsum, hbinom]
    _ ≤ min X Y * (Asum * Kδ * Real.log Q * B ^ j * 3 ^ J) := by
      have hpow : (3 : ℝ) ^ j ≤ 3 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
      apply mul_le_mul_of_nonneg_left _ (le_min
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y))
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C * min X Y * Real.log Q * B ^ j := by
      dsimp [C]
      ring

/-- The explicit finite source-profile constant used for all mixed physical
derivatives through order `J` in DFI equation (23). -/
noncomputable def dfiEquation23PhysicalMixedDerivativeFiniteConstant
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ) (J : ℕ) : ℝ :=
  let A : ℕ → ℕ → ℝ := fun r s =>
    dfiEquation2FiniteConstant Cf (max r s) *
      dfiCutoffFiniteConstant Cφ (r + s) * 2 ^ (r + s)
  let Asum : ℝ := ∑ r ∈ Finset.range (J + 1),
    ∑ s ∈ Finset.range (J + 1), A r s
  Asum * dfiDeltaKernelDerivativeFiniteConstant Cw (2 * J) * 2 ^ (4 * J)

/-- The complete mixed sharp physical derivative profile for equation (23).
The delta kernel is integrated before any support-length estimate, so the
shorter physical length from DFI (30) survives simultaneously in both
derivative directions. -/
theorem integral_integral_norm_dfiEquation23Physical_mixed_derivative_le_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (i j : ℕ), i ≤ J → j ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
            (fun u => (dfiDeltaKernel w q u : ℂ)) h) x y‖) ≤
        dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cψ Cw J *
          min X Y * Real.log Q *
          ((((q : ℝ) * Q)⁻¹) ^ (i + j)) := by
  let Kδ := dfiDeltaKernelDerivativeFiniteConstant Cw (2 * J)
  have hKδ : 0 < Kδ := by
    dsimp [Kδ]
    exact dfiDeltaKernelDerivativeFiniteConstant_pos hwC (2 * J)
  have hδmass := integral_norm_iteratedDeriv_dfiDeltaKernel_le_log_profile
    hwC hQ hU (2 * J)
  let A : ℕ → ℕ → ℝ := fun r s =>
    dfiEquation2FiniteConstant Cf (max r s) *
      dfiCutoffFiniteConstant Cψ (r + s) * 2 ^ (r + s)
  let Asum : ℝ := ∑ r ∈ Finset.range (J + 1),
    ∑ s ∈ Finset.range (J + 1), A r s
  let C : ℝ := Asum * Kδ * 2 ^ (4 * J)
  have hA : ∀ r s, 0 < A r s := by
    intro r s
    dsimp [A]
    have hcut : 0 < dfiCutoffFiniteConstant Cψ (r + s) := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk => hψC.positive k) ⟨0, by simp⟩
    exact mul_pos (mul_pos (hfC.finiteConstant_pos (max r s)) hcut)
      (pow_pos (by norm_num) _)
  have hAsum : 0 < Asum := by
    dsimp [Asum]
    have hinner : ∀ r ∈ Finset.range (J + 1),
        0 < ∑ s ∈ Finset.range (J + 1), A r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _hs => hA r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hC : 0 < C := by dsimp [C]; positivity
  intro q hq hqQ h i j hiJ hjJ
  change (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
          (fun u => (dfiDeltaKernel w q u : ℂ)) h) x y‖) ≤
    C * min X Y * Real.log Q * ((((q : ℝ) * Q)⁻¹) ^ (i + j))
  let G : ℝ → ℝ → ℂ := dfiLocalizedWeight f ψ h
  let δ : ℝ → ℝ := dfiDeltaKernel w q
  let B : ℝ := ((q : ℝ) * Q)⁻¹
  have hQpos : 0 < Q := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hB : 0 < B := by dsimp [B]; positivity
  have hG : ContDiff ℝ ∞ (Function.uncurry G) := by
    dsimp [G]
    exact contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    dsimp [G]
    exact support_uncurry_dfiLocalizedWeight_subset hbox
  have hDifference : ∀ x y, G x y ≠ 0 →
      x - y - (h : ℝ) ∈ Set.Icc (-U) U := by
    intro x y hne
    have hψne : ψ (x - y - (h : ℝ)) ≠ 0 := by
      intro hz
      exact hne (by simp [G, dfiLocalizedWeight, hz])
    have hu := hψ.support_subset hψne
    exact ⟨hu.1.le, hu.2.le⟩
  have hδsmooth : ContDiff ℝ ∞ δ := by
    dsimp [δ]
    exact contDiff_dfiDeltaKernel w q hq
  have hUinv : U⁻¹ ≤ 2 * B := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQpos
    have hqQle : (q : ℝ) * Q ≤ 2 * U := by
      rw [hU]
      nlinarith [mul_le_mul_of_nonneg_right hqQ hQpos.le]
    have hhalf : 0 < ((q : ℝ) * Q) / 2 := by positivity
    have hhalfU : ((q : ℝ) * Q) / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (((q : ℝ) * Q) / 2)⁻¹ := inv_anti₀ hhalf hhalfU
      _ = 2 * B := by dsimp [B]; field_simp [hqQpos.ne']
  let Crs : ℕ → ℕ → ℝ := fun r s => Asum * (2 * B) ^ (r + s)
  have hCrs : ∀ r ≤ i, ∀ s ≤ j, 0 ≤ Crs r s := by
    intro r _hr s _hs
    dsimp [Crs]
    positivity
  have hSource : ∀ r ≤ i, ∀ s ≤ j, ∀ x y,
      ‖dfiMixedDeriv r s G x y‖ ≤ Crs r s := by
    intro r hri s hsj x y
    have hrJ : r ≤ J := hri.trans hiJ
    have hsJ : s ≤ J := hsj.trans hjJ
    have hrmem : r ∈ Finset.range (J + 1) := by simp [hrJ]
    have hsmem : s ∈ Finset.range (J + 1) := by simp [hsJ]
    have hAle : A r s ≤ Asum := by
      dsimp [Asum]
      exact (Finset.single_le_sum (fun t _ht => (hA r t).le) hsmem).trans
        (Finset.single_le_sum
          (fun t _ht => Finset.sum_nonneg (fun u _hu => (hA t u).le)) hrmem)
    have hraw :=
      (dfiEquation21_of_profiles_uniform_in_shift
        hf hfC hbox hψ hψC hscale r s (h : ℝ) x y).2
    calc
      ‖dfiMixedDeriv r s G x y‖ ≤ A r s * U⁻¹ ^ (r + s) := by
        simpa only [G, A] using hraw
      _ ≤ Asum * U⁻¹ ^ (r + s) := by
        exact mul_le_mul_of_nonneg_right hAle
          (pow_nonneg (inv_nonneg.mpr hψ.U_pos.le) _)
      _ ≤ Asum * (2 * B) ^ (r + s) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr hψ.U_pos.le) hUinv _) hAsum.le
      _ = Crs r s := rfl
  have hphysical := integral_integral_norm_dfiLocalizedWeight_mixed_le_convolution
    hG hSupport hDifference hδsmooth i j hCrs hSource
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  let Z : ℝ := Asum * Kδ * Real.log Q * (2 * B) ^ (i + j)
  have hterm (s : ℕ) (hs : s ∈ Finset.range (j + 1))
      (r : ℕ) (hr : r ∈ Finset.range (i + 1)) :
      (j.choose s : ℝ) * (i.choose r : ℝ) * Crs r s *
          (∫ u : ℝ in Set.Icc (-U) U,
            ‖iteratedDeriv ((i - r) + (j - s)) δ u‖) ≤
        (j.choose s : ℝ) * (i.choose r : ℝ) * Z := by
    have hsj : s ≤ j := by simpa using hs
    have hri : r ≤ i := by simpa using hr
    have hkJ : (i - r) + (j - s) ≤ 2 * J := by omega
    have hδb := hδmass q ((i - r) + (j - s)) hq hkJ
    have hscalePow :
        (2 * B) ^ (r + s) * B ^ ((i - r) + (j - s)) ≤
          (2 * B) ^ (i + j) := by
      calc
        (2 * B) ^ (r + s) * B ^ ((i - r) + (j - s)) ≤
            (2 * B) ^ (r + s) * (2 * B) ^ ((i - r) + (j - s)) := by
          gcongr
          have hBtwo : B ≤ 2 * B := by nlinarith [hB]
          exact hBtwo
        _ = (2 * B) ^ (i + j) := by
          rw [← pow_add]
          congr 1
          omega
    calc
      (j.choose s : ℝ) * (i.choose r : ℝ) * Crs r s *
          (∫ u : ℝ in Set.Icc (-U) U,
            ‖iteratedDeriv ((i - r) + (j - s)) δ u‖) ≤
          (j.choose s : ℝ) * (i.choose r : ℝ) * Crs r s *
            (Kδ * Real.log Q * B ^ ((i - r) + (j - s))) := by
        exact mul_le_mul_of_nonneg_left (by
          simpa only [δ, B] using hδb) (by
            exact mul_nonneg
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (hCrs r hri s hsj))
      _ = (j.choose s : ℝ) * (i.choose r : ℝ) *
          (Asum * Kδ * Real.log Q *
            ((2 * B) ^ (r + s) * B ^ ((i - r) + (j - s)))) := by
        dsimp [Crs]
        ring
      _ ≤ (j.choose s : ℝ) * (i.choose r : ℝ) * Z := by
        dsimp [Z]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hscalePow
            (mul_nonneg (mul_nonneg hAsum.le hKδ.le) hlogQ))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hchooseI : (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) =
      (2 : ℝ) ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  have hchooseJ : (∑ s ∈ Finset.range (j + 1), (j.choose s : ℝ)) =
      (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  have hsum :
      (∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
        (j.choose s : ℝ) * (i.choose r : ℝ) * Crs r s *
          (∫ u : ℝ in Set.Icc (-U) U,
            ‖iteratedDeriv ((i - r) + (j - s)) δ u‖)) ≤
        (2 : ℝ) ^ (i + j) * Z := by
    calc
      _ ≤ ∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
          (j.choose s : ℝ) * (i.choose r : ℝ) * Z := by
        apply Finset.sum_le_sum
        intro s hs
        apply Finset.sum_le_sum
        intro r hr
        exact hterm s hs r hr
      _ = (2 : ℝ) ^ (i + j) * Z := by
        rw [pow_add]
        calc
          (∑ s ∈ Finset.range (j + 1),
              ∑ r ∈ Finset.range (i + 1),
                (j.choose s : ℝ) * (i.choose r : ℝ) * Z) =
              ∑ s ∈ Finset.range (j + 1),
                (j.choose s : ℝ) *
                  ((∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * Z) := by
            apply Finset.sum_congr rfl
            intro s _hs
            calc
              (∑ r ∈ Finset.range (i + 1),
                  (j.choose s : ℝ) * (i.choose r : ℝ) * Z) =
                  (j.choose s : ℝ) *
                    (∑ r ∈ Finset.range (i + 1),
                      (i.choose r : ℝ) * Z) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro r _hr
                ring
              _ = (j.choose s : ℝ) *
                  ((∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * Z) := by
                rw [Finset.sum_mul]
          _ = (∑ s ∈ Finset.range (j + 1), (j.choose s : ℝ)) *
              ((∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * Z) := by
            exact (Finset.sum_mul (Finset.range (j + 1))
              (fun s => (j.choose s : ℝ))
              ((∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * Z)).symm
          _ = (2 : ℝ) ^ j * ((2 : ℝ) ^ i * Z) := by
            rw [hchooseI, hchooseJ]
          _ = (2 : ℝ) ^ i * 2 ^ j * Z := by ring
  have hpowIJ : (2 : ℝ) ^ (i + j) ≤ 2 ^ (2 * J) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hminXY : 0 ≤ min X Y := le_min
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAsum.le hKδ.le) hlogQ)
      (pow_nonneg (mul_nonneg (by norm_num) hB.le) _)
  let W0 : ℝ := min X Y * Asum * Kδ * Real.log Q * B ^ (i + j)
  have hW0 : 0 ≤ W0 := by
    dsimp [W0]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hminXY hAsum.le) hKδ.le) hlogQ)
      (pow_nonneg hB.le _)
  have hpowTotal :
      (2 : ℝ) ^ (2 * J) * 2 ^ (i + j) ≤ 2 ^ (4 * J) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (∫ x : ℝ, ∫ y : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight G (fun u => (δ u : ℂ)) h) x y‖) ≤
        min X Y * ∑ s ∈ Finset.range (j + 1),
          ∑ r ∈ Finset.range (i + 1),
            (j.choose s : ℝ) * (i.choose r : ℝ) * Crs r s *
              (∫ u : ℝ in Set.Icc (-U) U,
                ‖iteratedDeriv ((i - r) + (j - s)) δ u‖) := hphysical
    _ ≤ min X Y * ((2 : ℝ) ^ (i + j) * Z) := by
      exact mul_le_mul_of_nonneg_left hsum hminXY
    _ ≤ min X Y * (2 ^ (2 * J) * Z) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowIJ hZ) hminXY
    _ ≤ C * min X Y * Real.log Q * B ^ (i + j) := by
      have hleft : min X Y * (2 ^ (2 * J) * Z) =
          W0 * (2 ^ (2 * J) * 2 ^ (i + j)) := by
        dsimp [W0, Z]
        rw [mul_pow]
        ring
      have hright : C * min X Y * Real.log Q * B ^ (i + j) =
          W0 * 2 ^ (4 * J) := by
        dsimp [C, W0]
        ring
      rw [hleft, hright]
      exact mul_le_mul_of_nonneg_left hpowTotal hW0

/-- Existential compatibility wrapper for the source-uniform mixed derivative
estimate. -/
theorem exists_integral_integral_norm_dfiEquation23Physical_mixed_derivative_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (i j : ℕ), i ≤ J → j ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun u => (dfiDeltaKernel w q u : ℂ)) h) x y‖) ≤
        C * min X Y * Real.log Q *
          ((((q : ℝ) * Q)⁻¹) ^ (i + j)) := by
  let C := dfiEquation23PhysicalMixedDerivativeFiniteConstant Cf Cφ Cw J
  have hC : 0 < C := by
    dsimp [C, dfiEquation23PhysicalMixedDerivativeFiniteConstant]
    let A : ℕ → ℕ → ℝ := fun r s =>
      dfiEquation2FiniteConstant Cf (max r s) *
        dfiCutoffFiniteConstant Cφ (r + s) * 2 ^ (r + s)
    have hA : ∀ r s, 0 < A r s := by
      intro r s
      dsimp [A]
      have hcut : 0 < dfiCutoffFiniteConstant Cφ (r + s) := by
        unfold dfiCutoffFiniteConstant
        exact Finset.sum_pos (fun k _hk => hφC.positive k) ⟨0, by simp⟩
      exact mul_pos (mul_pos (hfC.finiteConstant_pos (max r s)) hcut)
        (pow_pos (by norm_num) _)
    have hAsum : 0 < ∑ r ∈ Finset.range (J + 1),
        ∑ s ∈ Finset.range (J + 1), A r s := by
      have hinner : ∀ r ∈ Finset.range (J + 1),
          0 < ∑ s ∈ Finset.range (J + 1), A r s := by
        intro r _hr
        exact Finset.sum_pos (fun s _hs => hA r s) ⟨0, by simp⟩
      exact Finset.sum_pos hinner ⟨0, by simp⟩
    exact mul_pos (mul_pos hAsum
      (dfiDeltaKernelDerivativeFiniteConstant_pos hwC (2 * J)))
      (pow_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  simpa only [C] using
    integral_integral_norm_dfiEquation23Physical_mixed_derivative_le_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU J

/-- Divisor-coordinate form of the complete mixed equation-(28) profile.
The affine Jacobian supplies `(ab)⁻¹`, while the two derivative families
separately supply `a/(qQ)` and `b/(qQ)`. -/
theorem exists_integral_integral_norm_dfiEquation23Weight_mixed_derivative_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (i j : ℕ), i ≤ J → j ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) ≤
        C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
  obtain ⟨C, hC, hmass⟩ :=
    exists_integral_integral_norm_dfiEquation23Physical_mixed_derivative_le
      hf hfC hbox hψ hψC hscale w hwC hQ hU J
  refine ⟨C, hC, ?_⟩
  intro a b ha hb q hq hqQ h i j hiJ hjJ
  let H : ℝ → ℝ → ℂ :=
    dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
      (fun u => (dfiDeltaKernel w q u : ℂ)) h
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f ψ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hH : ContDiff ℝ ∞ (Function.uncurry H) := by
    dsimp only [H]
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q =
        fun x y => H ((a : ℝ) * x) ((b : ℝ) * y) := by
    rfl
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpoint (x y : ℝ) :
      ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ =
        (a : ℝ) ^ i * (b : ℝ) ^ j *
          ‖dfiMixedDeriv i j H ((a : ℝ) * x) ((b : ℝ) * y)‖ := by
    rw [heq, dfiMixedDeriv_affine_scale hH (a : ℝ) (b : ℝ) i j x y]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hjac := integral_integral_norm_comp_mul_eq
    (dfiMixedDeriv i j H) haR hbR
  have hmassH := hmass q hq hqQ h i j hiJ hjJ
  have habpow : 0 ≤ (a : ℝ) ^ i * (b : ℝ) ^ j := by positivity
  calc
    (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) =
        ((a : ℝ) ^ i * (b : ℝ) ^ j) *
          (∫ x : ℝ, ∫ y : ℝ,
            ‖dfiMixedDeriv i j H ((a : ℝ) * x) ((b : ℝ) * y)‖) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [integral_congr_ae
          (Filter.Eventually.of_forall fun y => hpoint x y),
          integral_const_mul]), integral_const_mul]
    _ = ((a : ℝ) ^ i * (b : ℝ) ^ j) * (((a : ℝ) * b)⁻¹ *
          (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i j H x y‖)) := by
      rw [hjac]
    _ ≤ ((a : ℝ) ^ i * (b : ℝ) ^ j) * (((a : ℝ) * b)⁻¹ *
          (C * min X Y * Real.log Q *
            ((((q : ℝ) * Q)⁻¹) ^ (i + j)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmassH
          (inv_nonneg.mpr (mul_nonneg haR.le hbR.le))) habpow
    _ = C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
      rw [pow_add, div_pow, div_pow]
      simp only [div_eq_mul_inv, ← inv_pow]
      ring

/-- The sharp physical derivative mass in the divisor coordinates of
equation (23).  This is the integrated form of equation (28): the Jacobian
contributes `(ab)⁻¹`, while each first-variable derivative contributes
exactly `a/(qQ)`. -/
theorem exists_integral_integral_norm_dfiEquation23Weight_derivative_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (i : ℕ), i ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) ≤
        C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) := by
  obtain ⟨C, hC, hmass⟩ :=
    exists_integral_integral_norm_dfiEquation23Physical_derivative_le
      hf hfC hbox hψ hψC hscale w hwC hQ hU J
  refine ⟨C, hC, ?_⟩
  intro a b ha hb q hq hqQ h i hiJ
  let H : ℝ → ℝ → ℂ :=
    dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
      (fun u => (dfiDeltaKernel w q u : ℂ)) h
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f ψ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hH : ContDiff ℝ ∞ (Function.uncurry H) := by
    dsimp only [H]
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q =
        fun x y => H ((a : ℝ) * x) ((b : ℝ) * y) := by
    rfl
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpoint (x y : ℝ) :
      ‖dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ =
        (a : ℝ) ^ i *
          ‖dfiMixedDeriv i 0 H ((a : ℝ) * x) ((b : ℝ) * y)‖ := by
    rw [heq, dfiMixedDeriv_affine_scale hH (a : ℝ) (b : ℝ) i 0 x y]
    simp
  have hjac := integral_integral_norm_comp_mul_eq
    (dfiMixedDeriv i 0 H) haR hbR
  have hmassH := hmass q hq hqQ h i hiJ
  calc
    (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) =
        (a : ℝ) ^ i *
          (∫ x : ℝ, ∫ y : ℝ,
            ‖dfiMixedDeriv i 0 H ((a : ℝ) * x) ((b : ℝ) * y)‖) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [integral_congr_ae
          (Filter.Eventually.of_forall fun y => hpoint x y), integral_const_mul]),
        integral_const_mul]
    _ = (a : ℝ) ^ i * (((a : ℝ) * b)⁻¹ *
          (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i 0 H x y‖)) := by
      rw [hjac]
    _ ≤ (a : ℝ) ^ i * (((a : ℝ) * b)⁻¹ *
          (C * min X Y * Real.log Q *
            ((((q : ℝ) * Q)⁻¹) ^ i))) := by
      gcongr
    _ = C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) := by
      rw [div_eq_mul_inv, mul_pow]
      ring

/-- Symmetric divisor-coordinate form of the sharp physical derivative
mass.  Each second-variable derivative contributes `b/(qQ)`. -/
theorem exists_integral_integral_norm_dfiEquation23Weight_second_derivative_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (h : ℤ) (j : ℕ), j ≤ J →
      (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) ≤
        C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
  obtain ⟨C, hC, hmass⟩ :=
    exists_integral_integral_norm_dfiEquation23Physical_second_derivative_le
      hf hfC hbox hψ hψC hscale w hwC hQ hU J
  refine ⟨C, hC, ?_⟩
  intro a b ha hb q hq hqQ h j hjJ
  let H : ℝ → ℝ → ℂ :=
    dfiLocalizedWeight (dfiLocalizedWeight f ψ h)
      (fun u => (dfiDeltaKernel w q u : ℂ)) h
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f ψ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hψ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hH : ContDiff ℝ ∞ (Function.uncurry H) := by
    dsimp only [H]
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q =
        fun x y => H ((a : ℝ) * x) ((b : ℝ) * y) := by
    rfl
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpoint (x y : ℝ) :
      ‖dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ =
        (b : ℝ) ^ j *
          ‖dfiMixedDeriv 0 j H ((a : ℝ) * x) ((b : ℝ) * y)‖ := by
    rw [heq, dfiMixedDeriv_affine_scale hH (a : ℝ) (b : ℝ) 0 j x y]
    simp
  have hjac := integral_integral_norm_comp_mul_eq
    (dfiMixedDeriv 0 j H) haR hbR
  have hmassH := hmass q hq hqQ h j hjJ
  calc
    (∫ x : ℝ, ∫ y : ℝ,
        ‖dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖) =
        (b : ℝ) ^ j *
          (∫ x : ℝ, ∫ y : ℝ,
            ‖dfiMixedDeriv 0 j H ((a : ℝ) * x) ((b : ℝ) * y)‖) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [integral_congr_ae
          (Filter.Eventually.of_forall fun y => hpoint x y), integral_const_mul]),
        integral_const_mul]
    _ = (b : ℝ) ^ j * (((a : ℝ) * b)⁻¹ *
          (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j H x y‖)) := by
      rw [hjac]
    _ ≤ (b : ℝ) ^ j * (((a : ℝ) * b)⁻¹ *
          (C * min X Y * Real.log Q *
            ((((q : ℝ) * Q)⁻¹) ^ j))) := by
      gcongr
    _ = C * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
      rw [div_eq_mul_inv, mul_pow]
      ring

/-- Exact differentiation-through-the-main-branch identity used in the
one-sided equation-(29) tails.  This avoids estimating a new Mellin contour:
every first-variable derivative of the `y`-main branch is the same logarithmic
main operator applied to the corresponding source derivative. -/
theorem iteratedDeriv_dfiVoronoiMainTerm_second
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x =
      dfiVoronoiMainTerm q (fun y ↦ dfiMixedDeriv i 0 E x y) := by
  let W : ℝ → ℂ := fun y ↦
    (dfiSafeLog C y : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)
  have hW : Continuous W := by
    dsimp [W]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hC)).add
      continuous_const |>.sub continuous_const
  have hSlice (x' : ℝ) : Function.support (E x') ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show
      (x', y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
  have hDerivSupport : Function.support
      (fun y ↦ dfiMixedDeriv i 0 E x y) ⊆ Set.Icc C D := by
    intro y hy
    by_contra hnot
    have hzero : (fun x' ↦ E x' y) = fun _ ↦ 0 := by
      funext x'
      by_contra hne
      exact hnot (hSupport (show
        (x', y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    change dfiMixedDeriv i 0 E x y ≠ 0 at hy
    simp only [dfiMixedDeriv, iteratedDeriv_zero] at hy
    rw [hzero] at hy
    exact hy (by simp)
  let H : ℝ → ℂ := fun x' ↦ ∫ y in Set.Icc C D, W y * E x' y
  have hMainEq : (fun x' ↦ dfiVoronoiMainTerm q (E x')) =
      fun x' ↦ (q : ℂ)⁻¹ * H x' := by
    funext x'
    rw [dfiVoronoiMainTerm_eq_Icc hC q (hSlice x')]
  have hHsmooth : ContDiff ℝ ∞ H := by
    dsimp [H]
    exact contDiff_integral_Icc_right_mul_left hW hE
  have hHderiv : iteratedDeriv i H x =
      ∫ y in Set.Icc C D, W y * dfiMixedDeriv i 0 E x y := by
    have hHEq : H = dfiWeightedPartialIntegral 0 C D W E := by
      funext x'
      simp [H, dfiWeightedPartialIntegral, dfiPartialX]
    rw [hHEq]
    rw [congrFun (iteratedDeriv_dfiWeightedPartialIntegral i C D hW hE) x]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro y hy
    change W y * dfiPartialX i (Function.uncurry E) (x, y) =
      W y * dfiMixedDeriv i 0 E x y
    congr 1
    rw [dfiPartialX_apply i hE x y]
    simp [dfiMixedDeriv]
  rw [hMainEq]
  rw [iteratedDeriv_const_mul (q : ℂ)⁻¹
    (hHsmooth.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [hHderiv]
  rw [dfiVoronoiMainTerm_eq_Icc hC q hDerivSupport]

/-- A derivative in the first variable cannot enlarge the projection of a
rectangular source support onto the second variable. -/
theorem support_dfiMixedDeriv_first_slice_subset
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i : ℕ) (x : ℝ) :
    Function.support (fun y ↦ dfiMixedDeriv i 0 E x y) ⊆ Set.Icc C D := by
  intro y hy
  by_contra hnot
  have hzero : (fun x' ↦ E x' y) = fun _ ↦ 0 := by
    funext x'
    by_contra hne
    exact hnot (hSupport (show
      (x', y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hne)).2
  change dfiMixedDeriv i 0 E x y ≠ 0 at hy
  simp only [dfiMixedDeriv, iteratedDeriv_zero] at hy
  rw [hzero] at hy
  exact hy (by simp)

/-- The `L¹` norm of every first derivative of a Voronoi main family is
controlled by the literal two-variable mass of the corresponding source
derivative.  In particular, no dyadic support length is introduced. -/
theorem integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_second_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) (i : ℕ) :
    (∫ x in Set.Icc A B,
      ‖iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x‖) ≤
      (q : ℝ)⁻¹ *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i 0 E x y‖) := by
  let Er : ℝ → ℝ → ℂ := dfiMixedDeriv i 0 E
  let W : ℝ := |Real.log C| + |Real.log D| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hEr : ContDiff ℝ ∞ (Function.uncurry Er) := by
    dsimp only [Er]
    exact contDiff_uncurry_dfiMixedDeriv hE i 0
  have hErSupport : Function.support (Function.uncurry Er) ⊆
      Set.Icc A B ×ˢ Set.Icc C D :=
    (support_dfiMixedDeriv_subset_tsupport hE i 0).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  have hSlice (x : ℝ) : DFIVoronoiTestFunction (Er x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hEr.comp (contDiff_prodMk_right x)
    support_subset := by
      intro y hy
      exact (hErSupport (show
        (x, y) ∈ Function.support (Function.uncurry Er) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hy)).2 }
  have hSliceSupport (x : ℝ) :
      Function.support (Er x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hErSupport (show
      (x, y) ∈ Function.support (Function.uncurry Er) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
  have hDerivative (x : ℝ) :
      iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x =
        dfiVoronoiMainTerm q (Er x) := by
    simpa only [Er] using
      iteratedDeriv_dfiVoronoiMainTerm_second hE hC hSupport q i x
  have hInnerContinuous : Continuous (fun x : ℝ ↦
      ∫ y in Set.Icc C D, ‖Er x y‖) :=
    continuous_parametric_integral_of_continuous
      hEr.continuous.norm isCompact_Icc
  have hMainFamily : ContDiff ℝ ∞
      (fun x ↦ dfiVoronoiMainTerm q (E x)) := by
    let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
    have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
      simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
        (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
    simpa only [Eswap] using
      (dfiVoronoiMainTermFamilyTestFunction
        hEswap hC hA hAB (by
          intro p hp
          have hm := hSupport (show
            (p.2, p.1) ∈ Function.support (Function.uncurry E) by
              simpa only [Eswap, Function.mem_support,
                Function.uncurry_apply_pair] using hp)
          exact ⟨hm.2, hm.1⟩) q).smooth
  have hLeft : IntegrableOn (fun x : ℝ ↦
      ‖iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x‖)
      (Set.Icc A B) :=
    (hMainFamily.continuous_iteratedDeriv i
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top i)))).norm
      |>.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun x : ℝ ↦
      (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖Er x y‖))
      (Set.Icc A B) :=
    (hInnerContinuous.const_mul ((q : ℝ)⁻¹ * W)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) :
      ‖iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x‖ ≤
        (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖Er x y‖) := by
    rw [hDerivative]
    simpa only [W] using norm_dfiVoronoiMainTerm_le_integral_norm
      hC q hq (hSlice x) (hSliceSupport x)
  have hFirst :
      (∫ x in Set.Icc A B,
        ‖iteratedDeriv i (fun x' ↦ dfiVoronoiMainTerm q (E x')) x‖) ≤
        (q : ℝ)⁻¹ * W *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖Er x y‖) := by
    calc
      _ ≤ ∫ x in Set.Icc A B,
          (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖Er x y‖) := by
        apply integral_mono_ae hLeft hRight
        filter_upwards with x
        exact hPoint x
      _ = (q : ℝ)⁻¹ * W *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖Er x y‖) := by
        rw [integral_const_mul]
  have hErNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) (volume.prod volume) :=
    hEr.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) (by
          intro p hp
          change ‖Er p.1 p.2‖ ≠ 0 at hp
          exact hErSupport (by
            simpa only [Function.mem_support,
              Function.uncurry_apply_pair] using (norm_ne_zero_iff.mp hp))))
  have hRectangle :
      (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖Er x y‖) ≤
        ∫ x : ℝ, ∫ y : ℝ, ‖Er x y‖ := by
    have hprod :
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖Er x y‖) =
          ∫ p in Set.Icc A B ×ˢ Set.Icc C D,
            ‖Er p.1 p.2‖ ∂(volume.prod volume) := by
      exact (MeasureTheory.setIntegral_prod
        (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) hErNorm.integrableOn).symm
    rw [hprod]
    calc
      (∫ p in Set.Icc A B ×ˢ Set.Icc C D,
          ‖Er p.1 p.2‖ ∂(volume.prod volume)) ≤
          ∫ p : ℝ × ℝ, ‖Er p.1 p.2‖ ∂(volume.prod volume) :=
        MeasureTheory.integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun p => norm_nonneg (Er p.1 p.2)) hErNorm
      _ = ∫ x : ℝ, ∫ y : ℝ, ‖Er x y‖ :=
        MeasureTheory.integral_prod
          (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) hErNorm
  exact hFirst.trans (mul_le_mul_of_nonneg_left hRectangle (by positivity))

/-- Concrete equation-(23) `L¹` derivative profile after taking the
second-variable Voronoi main term.  This is the one-sided source profile
needed in equation (29); its mass is `(ab)⁻¹ min(X,Y)` rather than a
pointwise bound times the full remaining support length. -/
theorem exists_integral_Icc_norm_iteratedDeriv_dfiEquation23_yMain_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (qy : ℕ), 0 < qy → ∀ (h : ℤ) (i : ℕ), i ≤ J →
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ‖iteratedDeriv i (fun x' ↦
          dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x')) x‖) ≤
        K * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) := by
  obtain ⟨K, hK, hmass⟩ :=
    exists_integral_integral_norm_dfiEquation23Weight_derivative_le
      hf hfC hbox hψ hψC hscale w hwC hQ hU J
  refine ⟨K, hK, ?_⟩
  intro a b ha hb q hq hqQ qy hqy h i hiJ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let W : ℝ := |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    dsimp only [E]
    exact contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    dsimp only [E]
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hf.one_le_X
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hYB : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hXrange : X / (a : ℝ) ≤ 2 * X / a := by
    exact div_le_div_of_nonneg_right (by linarith) haR.le
  have hYrange : Y / (b : ℝ) ≤ 2 * Y / b := by
    exact div_le_div_of_nonneg_right (by linarith) hbR.le
  have hraw :=
    integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_second_le
      hE hXA hXrange hYB hYrange hSupport qy hqy i
  have hmass' := hmass a b ha hb q hq hqQ h i hiJ
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    (∫ x in Set.Icc (X / a) (2 * X / a),
        ‖iteratedDeriv i (fun x' ↦
          dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x')) x‖) ≤
        (qy : ℝ)⁻¹ * W *
          (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i 0 E x y‖) := by
      simpa only [E, W] using hraw
    _ ≤ (qy : ℝ)⁻¹ * W *
        (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i)) := by
      exact mul_le_mul_of_nonneg_left hmass'
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg qy)) hW)
    _ = K * (qy : ℝ)⁻¹ * W *
        ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) := by
      dsimp [W]
      ring

/-- Symmetric differentiation-through-the-main-branch identity.  A
second-variable derivative of the `x`-main branch is the first logarithmic
main operator applied to the corresponding source derivative. -/
theorem iteratedDeriv_dfiVoronoiMainTerm_first
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hA : 0 < A)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (i : ℕ) (y : ℝ) :
    iteratedDeriv i
        (fun y' ↦ dfiVoronoiMainTerm q (fun x ↦ E x y')) y =
      dfiVoronoiMainTerm q (fun x ↦ dfiMixedDeriv 0 i E x y) := by
  let Eswap : ℝ → ℝ → ℂ := fun y' x ↦ E x y'
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hraw := iteratedDeriv_dfiVoronoiMainTerm_second
    hEswap hA hSupportSwap q i y
  simpa only [Eswap, dfiMixedDeriv, iteratedDeriv_zero] using hraw

/-- A derivative in the second variable cannot enlarge the projection of a
rectangular source support onto the first variable. -/
theorem support_dfiMixedDeriv_second_slice_subset
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (j : ℕ) (y : ℝ) :
    Function.support (fun x ↦ dfiMixedDeriv 0 j E x y) ⊆ Set.Icc A B := by
  intro x hx
  by_contra hnot
  have hzero : E x = fun _ ↦ 0 := by
    funext y'
    by_contra hne
    exact hnot (hSupport (show
      (x, y') ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hne)).1
  change dfiMixedDeriv 0 j E x y ≠ 0 at hx
  simp only [dfiMixedDeriv, iteratedDeriv_zero] at hx
  rw [hzero] at hx
  exact hx (by simp)

/-- The symmetric `L¹` main-family estimate.  It is the exact
coordinate-swapped counterpart of
`integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_second_le`; compact
support justifies the final Fubini swap, so the source mass remains the
literal two-variable mass. -/
theorem integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_first_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) (j : ℕ) :
    (∫ y in Set.Icc C D,
      ‖iteratedDeriv j
        (fun y' ↦ dfiVoronoiMainTerm q (fun x ↦ E x y')) y‖) ≤
      (q : ℝ)⁻¹ *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j E x y‖) := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hraw :=
    integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_second_le
      hEswap hC hCD hA hAB hSupportSwap q hq j
  let F : ℝ → ℝ → ℝ := fun x y ↦ ‖dfiMixedDeriv 0 j E x y‖
  have hMixed (y x : ℝ) :
      ‖dfiMixedDeriv j 0 Eswap y x‖ = F x y := by
    simp only [Eswap, F, dfiMixedDeriv, iteratedDeriv_zero]
  have hDerivSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiMixedDeriv 0 j E)) :=
    contDiff_uncurry_dfiMixedDeriv hE 0 j
  have hDerivSupport :
      Function.support (Function.uncurry (dfiMixedDeriv 0 j E)) ⊆
        Set.Icc A B ×ˢ Set.Icc C D :=
    (support_dfiMixedDeriv_subset_tsupport hE 0 j).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) :=
    hDerivSmooth.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) (by
          intro p hp
          change ‖dfiMixedDeriv 0 j E p.1 p.2‖ ≠ 0 at hp
          exact hDerivSupport (by
            simpa only [Function.mem_support,
              Function.uncurry_apply_pair] using (norm_ne_zero_iff.mp hp))))
  have hswap :
      (∫ y : ℝ, ∫ x : ℝ, ‖dfiMixedDeriv j 0 Eswap y x‖) =
        ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j E x y‖ := by
    calc
      _ = ∫ y : ℝ, ∫ x : ℝ, F x y := by
        apply integral_congr_ae
        filter_upwards [] with y
        apply integral_congr_ae
        filter_upwards [] with x
        exact hMixed y x
      _ = ∫ x : ℝ, ∫ y : ℝ, F x y :=
        (MeasureTheory.integral_integral_swap hFint).symm
      _ = _ := by rfl
  rw [hswap] at hraw
  simpa only [Eswap] using hraw

/-- Concrete symmetric equation-(23) `L¹` profile after taking the
first-variable Voronoi main term.  Every remaining `y` derivative costs
`b/(qQ)`, while the source mass keeps the sharp `(ab)⁻¹ min(X,Y)` factor. -/
theorem exists_integral_Icc_norm_iteratedDeriv_dfiEquation23_xMain_le
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) (J : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ∀ (qx : ℕ), 0 < qx → ∀ (h : ℤ) (j : ℕ), j ≤ J →
      (∫ y in Set.Icc (Y / b) (2 * Y / b),
        ‖iteratedDeriv j (fun y' ↦
          dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y')) y‖) ≤
        K * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
  obtain ⟨K, hK, hmass⟩ :=
    exists_integral_integral_norm_dfiEquation23Weight_second_derivative_le
      hf hfC hbox hψ hψC hscale w hwC hQ hU J
  refine ⟨K, hK, ?_⟩
  intro a b ha hb q hq hqQ qx hqx h j hjJ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let W : ℝ := |Real.log (X / a)| + |Real.log (2 * X / a)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    dsimp only [E]
    exact contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    dsimp only [E]
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hYB : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hXrange : X / (a : ℝ) ≤ 2 * X / a :=
    div_le_div_of_nonneg_right (by linarith) haR.le
  have hYrange : Y / (b : ℝ) ≤ 2 * Y / b :=
    div_le_div_of_nonneg_right (by linarith) hbR.le
  have hraw :=
    integral_Icc_norm_iteratedDeriv_dfiVoronoiMainTerm_first_le
      hE hXA hXrange hYB hYrange hSupport qx hqx j
  have hmass' := hmass a b ha hb q hq hqQ h j hjJ
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    (∫ y in Set.Icc (Y / b) (2 * Y / b),
        ‖iteratedDeriv j (fun y' ↦
          dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y')) y‖) ≤
        (qx : ℝ)⁻¹ * W *
          (∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j E x y‖) := by
      simpa only [E, W] using hraw
    _ ≤ (qx : ℝ)⁻¹ * W *
        (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j)) := by
      exact mul_le_mul_of_nonneg_left hmass'
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg qx)) hW)
    _ = K * (qx : ℝ)⁻¹ * W *
        ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
      dsimp [W]
      ring

/-- On a support bounded away from zero, the physical quarter-weight costs
exactly the lower-endpoint factor used in DFI (29). -/
theorem dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
    {A B : ℝ} (hA : 0 < A) {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g)
    (hSupport : Function.support g ⊆ Set.Icc A B) :
    dfiBesselQuarterBaseNorm g ≤
      A ^ (-(1 / 4 : ℝ)) * ∫ x in Set.Icc A B, ‖g x‖ := by
  have hSubset : Set.Icc A B ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hA.trans_le hx.1
  have hZero (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ) \ Set.Icc A B) :
      ‖g x‖ / Real.sqrt (Real.sqrt x) = 0 := by
    have hgx : g x = 0 := by
      by_contra hne
      exact hx.2 (hSupport hne)
    simp [hgx]
  have hRewrite : dfiBesselQuarterBaseNorm g =
      ∫ x in Set.Icc A B, ‖g x‖ / Real.sqrt (Real.sqrt x) := by
    unfold dfiBesselQuarterBaseNorm
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hSubset hZero
  have hLeft : IntegrableOn
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) (Set.Icc A B) :=
    hg.integrableOn_besselQuarterWeight.mono_set hSubset
  have hRight : IntegrableOn (fun x : ℝ =>
      A ^ (-(1 / 4 : ℝ)) * ‖g x‖) (Set.Icc A B) :=
    (hg.continuous.norm.const_mul (A ^ (-(1 / 4 : ℝ)))).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hInvA : 1 / Real.sqrt (Real.sqrt A) =
      A ^ (-(1 / 4 : ℝ)) := by
    rw [sqrt_sqrt_eq_rpow_quarter A hA.le, Real.rpow_neg hA.le]
    simp [div_eq_mul_inv]
  rw [hRewrite]
  calc
    (∫ x in Set.Icc A B, ‖g x‖ / Real.sqrt (Real.sqrt x)) ≤
        ∫ x in Set.Icc A B, A ^ (-(1 / 4 : ℝ)) * ‖g x‖ := by
      apply integral_mono_ae hLeft hRight
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hxpos : 0 < x := hA.trans_le hx.1
      have hden : Real.sqrt (Real.sqrt A) ≤ Real.sqrt (Real.sqrt x) := by
        gcongr
        exact hx.1
      calc
        ‖g x‖ / Real.sqrt (Real.sqrt x) =
            ‖g x‖ * (1 / Real.sqrt (Real.sqrt x)) := by ring
        _ ≤ ‖g x‖ * (1 / Real.sqrt (Real.sqrt A)) := by
          exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le
              (Real.sqrt_pos.2 (Real.sqrt_pos.2 hA)) hden)
            (norm_nonneg _)
        _ = A ^ (-(1 / 4 : ℝ)) * ‖g x‖ := by rw [hInvA]; ring
    _ = A ^ (-(1 / 4 : ℝ)) * ∫ x in Set.Icc A B, ‖g x‖ := by
      rw [integral_const_mul]

/-- A uniform pointwise estimate on a compact support gives the elementary
quarter-mass bound used when the other Voronoi frequency has already been
shifted by the DFI (29) recurrence. -/
theorem dfiBesselQuarterBaseNorm_le_of_uniform_norm
    {A B M : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (hSupport : Function.support g ⊆ Set.Icc A B)
    (hPoint : ∀ x, ‖g x‖ ≤ M) :
    dfiBesselQuarterBaseNorm g ≤
      A ^ (-(1 / 4 : ℝ)) * ((B - A) * M) := by
  have hInt :
      (∫ x in Set.Icc A B, ‖g x‖) ≤ ∫ _x in Set.Icc A B, M := by
    apply MeasureTheory.integral_mono_ae
    · exact hg.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
    · exact integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
    · filter_upwards with x
      exact hPoint x
  calc
    dfiBesselQuarterBaseNorm g ≤
        A ^ (-(1 / 4 : ℝ)) * ∫ x in Set.Icc A B, ‖g x‖ :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hA hg hSupport
    _ ≤ A ^ (-(1 / 4 : ℝ)) * ∫ _x in Set.Icc A B, M := by
      gcongr
    _ = A ^ (-(1 / 4 : ℝ)) * ((B - A) * M) := by
      rw [MeasureTheory.setIntegral_const]
      rw [Real.volume_real_Icc_of_le hAB]
      simp only [smul_eq_mul]

/-- Physical quarter-weight norm after `k` exact Bessel recurrences.  The
bound retains the source support length `S`, the quarter-power Bessel
weight, and the full recurrence factor.  It is the norm estimate needed to
turn the exact contour recurrence into DFI's arbitrary-power tail. -/
theorem DFIVoronoiTestFunction.dfiBesselQuarterBaseNorm_besselRecurrenceIterate_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    dfiBesselQuarterBaseNorm
        (dfiEquation29BesselRecurrenceIterate k g) ≤
      S ^ (-(1 / 4 : ℝ)) *
        (S * (A * (D * S * B ^ 2) ^ k)) := by
  let G : ℝ → ℂ := dfiEquation29BesselRecurrenceIterate k g
  let K : ℝ := A * (D * S * B ^ 2) ^ k
  have hG : DFIVoronoiTestFunction G := hg.besselRecurrenceIterate k
  have hGSupport : Function.support G ⊆ Set.Icc S (2 * S) := by
    simpa [G] using hg.support_besselRecurrenceIterate_subset hSupport k
  have hPoint : ∀ x ∈ Set.Icc S (2 * S), ‖G x‖ ≤ K := by
    intro x hx
    have hout := hg.norm_iteratedDeriv_besselRecurrenceIterate_le
      hA hB hS hSB hSupport k 0 (by simpa using hD) (by simpa using hDeriv)
      0 (by simp) x hx
    simpa [G, K] using hout
  have hLeft : IntegrableOn (fun x : ℝ => ‖G x‖) (Set.Icc S (2 * S)) :=
    hG.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun _ : ℝ => K) (Set.Icc S (2 * S)) :=
    integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  have hIntegral : (∫ x in Set.Icc S (2 * S), ‖G x‖) ≤ S * K := by
    calc
      (∫ x in Set.Icc S (2 * S), ‖G x‖) ≤
          ∫ _x in Set.Icc S (2 * S), K := by
        apply integral_mono_ae hLeft hRight
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact hPoint x hx
      _ = (2 * S - S) * K := by
        rw [setIntegral_const, Real.volume_real_Icc]
        simp only [smul_eq_mul]
        rw [max_eq_left (by linarith)]
      _ = S * K := by ring
  calc
    dfiBesselQuarterBaseNorm G ≤
        S ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc S (2 * S), ‖G x‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hS hG hGSupport
    _ ≤ S ^ (-(1 / 4 : ℝ)) * (S * K) := by
      exact mul_le_mul_of_nonneg_left hIntegral (Real.rpow_nonneg hS.le _)
    _ = S ^ (-(1 / 4 : ℝ)) *
        (S * (A * (D * S * B ^ 2) ^ k)) := rfl

/-- Physical quarter-weight norm after `k` recurrences, using an integral
derivative profile.  This is the source-faithful form of the estimate after
DFI (29): the initial mass `A` is retained, with no extra dyadic support
length introduced by a supremum estimate. -/
theorem DFIVoronoiTestFunction.dfiBesselQuarterBaseNorm_besselRecurrenceIterate_le_of_l1
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hL1 : ∀ r ≤ 2 * k,
      (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) ≤ A * B ^ r) :
    dfiBesselQuarterBaseNorm
        (dfiEquation29BesselRecurrenceIterate k g) ≤
      S ^ (-(1 / 4 : ℝ)) * (A * (D * S * B ^ 2) ^ k) := by
  let G : ℝ → ℂ := dfiEquation29BesselRecurrenceIterate k g
  have hG : DFIVoronoiTestFunction G := hg.besselRecurrenceIterate k
  have hGSupport : Function.support G ⊆ Set.Icc S (2 * S) := by
    simpa only [G] using hg.support_besselRecurrenceIterate_subset hSupport k
  have hIntegral := hg.integral_norm_besselRecurrenceIterate_le
    hA hB hS hSB k hD hL1
  calc
    dfiBesselQuarterBaseNorm G ≤
        S ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc S (2 * S), ‖G x‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hS hG hGSupport
    _ ≤ S ^ (-(1 / 4 : ℝ)) * (A * (D * S * B ^ 2) ^ k) := by
      gcongr

/-- Exact arbitrary-depth contour shift followed by the physical Bessel
estimate.  Unlike the earlier generic Mellin-line bounds, this statement
keeps the reciprocal dual frequency inside the recurrence multiplier, so
the source cutoff in DFI (29) can be recovered without surplus scale
powers. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29InitialTransform_le_recurrence
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      ‖dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)‖ ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          (dfiBesselQuarterBaseNorm
            (dfiEquation29BesselRecurrenceIterate k g) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  let G : ℝ → ℂ := dfiEquation29BesselRecurrenceIterate k g
  have hG : DFIVoronoiTestFunction G := hg.besselRecurrenceIterate k
  have heq : dfiEquation29InitialTransform q branch g n =
      (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) ^ k *
        dfiEquation29InitialTransform q branch G n := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n
          (-(1 / 2 : ℝ) - k) :=
        hg.dfiEquation29TransformAt_shift q k branch hn
      _ = (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) ^ k *
          dfiEquation29TransformAt q branch G n (-(1 / 2 : ℝ)) := by
        simpa [G] using
          hg.dfiEquation29TransformAt_sub_nat_besselRecurrence
            q branch hn k (-(1 / 2 : ℝ)) (by norm_num)
      _ = _ := by rw [dfiEquation29TransformAt_initial]
  have hPhysical :=
    hG.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
      q branch hn (hG.integrableOn_besselQuarterWeight_mul_nat n hn)
  rw [dfiBesselQuarterNorm_eq_rpow_mul_base G n hn] at hPhysical
  rw [heq, norm_mul, norm_pow]
  gcongr
  simpa [G, mul_comm] using hPhysical

/-- Fully quantitative equation-(29) transform tail before specializing
the derivative scales of a concrete DFI slice.  Its two `k`-th powers are
the exact contour multiplier and the exact cost of the local Bessel
recurrence; their product is the source tail ratio. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29InitialTransform_le_recurrence_profile
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S))
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          ((S ^ (-(1 / 4 : ℝ)) *
            (S * (A * (D * S * B ^ 2) ^ k))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hRec := hg.norm_dfiEquation29InitialTransform_le_recurrence
    q branch hn k
  rw [norm_dfiEquation29BranchShiftMultiplier q branch n] at hRec
  have hBase := hg.dfiBesselQuarterBaseNorm_besselRecurrenceIterate_le
    hA hB hS hSB hSupport k hD hDeriv
  exact hRec.trans (by gcongr)

/-- Equation-(29) transform tail with an integral derivative profile.  The
right side contains the source `L¹` mass `A` directly, rather than the
pointwise majorant multiplied by the support length. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29InitialTransform_le_recurrence_l1_profile
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S))
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hL1 : ∀ r ≤ 2 * k,
      (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) ≤ A * B ^ r) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          ((S ^ (-(1 / 4 : ℝ)) *
            (A * (D * S * B ^ 2) ^ k)) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hRec := hg.norm_dfiEquation29InitialTransform_le_recurrence
    q branch hn k
  rw [norm_dfiEquation29BranchShiftMultiplier q branch n] at hRec
  have hBase :=
    hg.dfiBesselQuarterBaseNorm_besselRecurrenceIterate_le_of_l1
      hA hB hS hSB hSupport k hD hL1
  exact hRec.trans (by gcongr)

/-- Finite normalized `L¹` envelope of the derivatives consumed by `k`
complete Bessel recurrences.  Division by `B^r` makes every derivative
order contribute on the same source scale. -/
noncomputable def dfiDerivativeL1Envelope
    (g : ℝ → ℂ) (S B : ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (2 * k + 1),
    (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) / B ^ r

theorem dfiDerivativeL1Envelope_nonneg
    (g : ℝ → ℂ) (S : ℝ) {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    0 ≤ dfiDerivativeL1Envelope g S B k := by
  apply Finset.sum_nonneg
  intro r _hr
  apply div_nonneg
  · exact integral_nonneg fun _ ↦ norm_nonneg _
  · exact pow_nonneg hB r

/-- Every derivative represented in the finite envelope recovers its
geometric `B^r` bound. -/
theorem integral_norm_iteratedDeriv_le_envelope_mul_pow
    (g : ℝ → ℂ) (S : ℝ) {B : ℝ} (hB : 0 < B) (k r : ℕ)
    (hr : r ≤ 2 * k) :
    (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) ≤
      dfiDerivativeL1Envelope g S B k * B ^ r := by
  have hrMem : r ∈ Finset.range (2 * k + 1) := by simp [hr]
  have hTerm :
      (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) / B ^ r ≤
        dfiDerivativeL1Envelope g S B k := by
    dsimp only [dfiDerivativeL1Envelope]
    exact Finset.single_le_sum
      (fun s (_hs : s ∈ Finset.range (2 * k + 1)) ↦
        div_nonneg (integral_nonneg fun x : ℝ ↦
          norm_nonneg (iteratedDeriv s g x))
        (pow_nonneg hB.le s)) hrMem
  exact (div_le_iff₀ (pow_pos hB r)).mp hTerm

/-- Envelope form of the equation-(29) recurrence.  Unlike a supremum
profile, this theorem is linear in each source derivative mass and can
therefore be integrated through a second transform. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29InitialTransform_le_recurrence_l1_envelope
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {B S D : ℝ} (hB : 0 < B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S))
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt q *
          ((S ^ (-(1 / 4 : ℝ)) *
            (dfiDerivativeL1Envelope g S B k *
              (D * S * B ^ 2) ^ k)) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  exact hg.norm_dfiEquation29InitialTransform_le_recurrence_l1_profile
    (dfiDerivativeL1Envelope_nonneg g S hB.le k) hB.le hS hSB
      hSupport q branch hn k hD
      (fun r hr ↦ integral_norm_iteratedDeriv_le_envelope_mul_pow
        g S hB k r hr)

/-- Algebraic cancellation of the modulus between the contour multiplier
and the derivative cost.  This is the exact calculation behind DFI's
frequency scale `aX/Q²` (and, after renaming, `bY/Q²`). -/
theorem dfiEquation29_recurrence_ratio
    {Q X : ℝ} (hQ : 0 < Q)
    {a q n : ℕ} (ha : 0 < a) (hq : 0 < q) (hn : 0 < n)
    (D : ℝ) (k : ℕ) :
    (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        (D * (X / a) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k =
      ((D / Real.pi ^ 2) *
        (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hQR : Q ≠ 0 := ne_of_gt hQ
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [← mul_pow]
  congr 1
  field_simp

/-- The recurrence multiplier may use a reduced Voronoi modulus `r`, while
the derivative scale is governed by the original delta modulus `q`.  Since
`r \le q`, DFI's published cutoff ratio remains an upper bound. -/
theorem dfiEquation29_recurrence_ratio_le
    {Q X : ℝ} (hQ : 0 < Q) (hX : 0 ≤ X)
    {a q r n : ℕ} (ha : 0 < a) (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
    (hrq : (r : ℝ) ≤ q) {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        (D * (X / a) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k ≤
      ((D / Real.pi ^ 2) *
        (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k := by
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul :
      ((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ) ≤
        ((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ) := by
    have hden : 0 < 2 * Real.pi := by positivity
    gcongr
  calc
    (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (D * (X / a) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k ≤
        (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (D * (X / a) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k := by
      gcongr
    _ = _ := dfiEquation29_recurrence_ratio hQ ha hq hn D k

/-- Normalize the frequency dependence after the recurrence: the `k`th
cutoff ratio contributes exactly `n⁻ᵏ`, which combines with the divisor and
Bessel quarter powers. -/
theorem dfiEquation29_frequency_power_normalization
    {R Z Q ε : ℝ} (hQ : 0 < Q) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (R * (Z / ((n : ℝ) * Q ^ 2))) ^ k *
        ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) =
      (R * (Z / Q ^ 2)) ^ k *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hQR : Q ≠ 0 := ne_of_gt hQ
  rw [show Z / ((n : ℝ) * Q ^ 2) =
      (Z / Q ^ 2) * (n : ℝ)⁻¹ by field_simp]
  rw [show R * (Z / Q ^ 2 * (n : ℝ)⁻¹) =
      (R * (Z / Q ^ 2)) * (n : ℝ)⁻¹ by ring]
  rw [mul_pow]
  have hinv : ((n : ℝ)⁻¹) ^ k = (n : ℝ) ^ (-(k : ℝ)) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hnR.le]
  rw [hinv]
  rw [← Real.rpow_add hnR]
  rw [show (R * (Z / Q ^ 2)) ^ k * (n : ℝ) ^ (-(k : ℝ)) *
      (n : ℝ) ^ (ε + -(1 / 4 : ℝ)) =
      (R * (Z / Q ^ 2)) ^ k *
        ((n : ℝ) ^ (-(k : ℝ)) *
          (n : ℝ) ^ (ε + -(1 / 4 : ℝ))) by ring]
  rw [← Real.rpow_add hnR]
  congr 1
  ring

/-- If the same nonnegative amplitude has an `m`-recurrence bound and an
`n`-recurrence bound, their geometric mean shares half of the recurrence
gain between the two frequencies.  This is the analytic device used for
the corner in which both frequencies lie beyond the DFI (29) cutoffs. -/
theorem two_frequency_geometric_mean
    {x A B m n e k : ℝ}
    (hx0 : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : 0 < m) (hn : 0 < n)
    (hx : x ≤ A * m ^ (e - k) * n ^ e)
    (hy : x ≤ B * m ^ e * n ^ (e - k)) :
    x ≤ Real.sqrt (A * B) *
      m ^ (e - k / 2) * n ^ (e - k / 2) := by
  let R₁ : ℝ := A * m ^ (e - k) * n ^ e
  let R₂ : ℝ := B * m ^ e * n ^ (e - k)
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hsq : x ^ 2 ≤ R₁ * R₂ := by
    rw [pow_two]
    exact mul_le_mul hx hy hx0 hR₁
  have hsqrt : x ≤ Real.sqrt (R₁ * R₂) :=
    (Real.le_sqrt hx0 (mul_nonneg hR₁ hR₂)).2 hsq
  calc
    x ≤ Real.sqrt (R₁ * R₂) := hsqrt
    _ = Real.sqrt (A * B) *
        m ^ (e - k / 2) * n ^ (e - k / 2) := by
      rw [Real.sqrt_eq_rpow]
      dsimp [R₁, R₂]
      rw [show (A * m ^ (e - k) * n ^ e) *
          (B * m ^ e * n ^ (e - k)) =
          (A * B) * (m ^ (e - k) * m ^ e) *
            (n ^ e * n ^ (e - k)) by ring]
      rw [Real.mul_rpow
          (mul_nonneg (mul_nonneg hA hB)
            (mul_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hm.le _)))
          (mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hn.le _))]
      rw [Real.mul_rpow (mul_nonneg hA hB)
          (mul_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hm.le _))]
      rw [← Real.rpow_add hm, ← Real.rpow_add hn]
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hm.le, ← Real.rpow_mul hn.le]
      congr 1 <;> ring

/-- Source-specialized first-variable arbitrary-power tail from DFI (29).
The displayed bound still shows both exact recurrence factors; the next
algebraic corollary combines them into the cutoff ratio `aX/(nQ²)`. -/
theorem exists_dfiEquation29_xSlice_recurrence_tail_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (X / a) *
                      (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    exists_dfiEquation28_xSlice_derivative_profile_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q r ha hb hqInst hrInst hqQ h y branch n hn
  letI : NeZero q := hqInst
  letI : NeZero r := hrInst
  have hq : 0 < q := NeZero.pos q
  let g : ℝ → ℂ := fun x => dfiEquation23Weight w
    (dfiLocalizedWeight f φ h) a b h q x y
  have hg : DFIVoronoiTestFunction g := by
    simpa [g] using dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y
  have hQ : 0 < Q := w.Q_pos
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleX : U ≤ X := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    have hminX : min X Y ≤ X := min_le_left _ _
    exact hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans hminX)
  have hqQle : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  have hS : 0 < X / (a : ℝ) := div_pos hX haR
  have hB : 0 ≤ 2 * ((a : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (X / (a : ℝ)) *
      (2 * ((a : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQ
    rw [show (X / (a : ℝ)) *
        (2 * ((a : ℝ) / ((q : ℝ) * Q))) =
      2 * X / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  have hSupport : Function.support g ⊆
      Set.Icc (X / (a : ℝ)) (2 * (X / (a : ℝ))) := by
    intro x hx
    have hp : (x, y) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
      simpa only [g, Function.mem_support,
        Function.uncurry_apply_pair] using hx
    have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
    constructor
    · exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.1)
    · calc
        x ≤ (2 * X) / (a : ℝ) :=
          (le_div_iff₀ haR).2 (by simpa [mul_comm] using hmem.1.2)
        _ = 2 * (X / (a : ℝ)) := by ring
  have hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤
        (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr x
    have hraw := hprofile a b q ha hb hq hqQ h y r hr x
    have hratio : 0 ≤ (a : ℝ) / ((q : ℝ) * Q) := by positivity
    dsimp [g]
    calc
      ‖iteratedDeriv r
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) x‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := hraw
      _ ≤ (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r := by
        have hratio_le : (a : ℝ) / ((q : ℝ) * Q) ≤
            2 * ((a : ℝ) / ((q : ℝ) * Q)) := by linarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) (by positivity)
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := C * ((q : ℝ) * Q)⁻¹)
    (B := 2 * ((a : ℝ) / ((q : ℝ) * Q)))
    (S := X / (a : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    (show 0 ≤ C * ((q : ℝ) * Q)⁻¹ by positivity) hB hS hSB hSupport
    r branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  simpa [g] using hout

/-- Fixed-instance compatibility form of the source-specialized
first-variable recurrence tail.  Uniform applications use the preceding
profile-explicit theorem so its constant is fixed before the physical
parameters vary. -/
theorem exists_dfiEquation29_xSlice_recurrence_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (X / a) *
                      (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_xSlice_recurrence_tail_bound_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hUQ k

/-- Source-specialized second-variable arbitrary-power tail from DFI (29),
with the exact `b/(qQ)` derivative scale. -/
theorem exists_dfiEquation29_ySlice_recurrence_tail_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) n‖ ≤
          (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (Y / b) *
                      (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    exists_dfiEquation28_ySlice_derivative_profile_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q r ha hb hqInst hrInst hqQ h x branch n hn
  letI : NeZero q := hqInst
  letI : NeZero r := hrInst
  have hq : 0 < q := NeZero.pos q
  let g : ℝ → ℂ := dfiEquation23Weight w
    (dfiLocalizedWeight f φ h) a b h q x
  have hg : DFIVoronoiTestFunction g := by
    simpa [g] using dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x
  have hQ : 0 < Q := w.Q_pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleY : U ≤ Y := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    have hminY : min X Y ≤ Y := min_le_right _ _
    exact hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans hminY)
  have hqQle : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  have hS : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hB : 0 ≤ 2 * ((b : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (Y / (b : ℝ)) *
      (2 * ((b : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQ
    rw [show (Y / (b : ℝ)) *
        (2 * ((b : ℝ) / ((q : ℝ) * Q))) =
      2 * Y / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  have hSupport : Function.support g ⊆
      Set.Icc (Y / (b : ℝ)) (2 * (Y / (b : ℝ))) := by
    intro y hy
    have hp : (x, y) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
      simpa only [g, Function.mem_support,
        Function.uncurry_apply_pair] using hy
    have hmem := dfiEquation23Weight_support_subset w hbox a b h q hp
    constructor
    · exact (div_le_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.1)
    · calc
        y ≤ (2 * Y) / (b : ℝ) :=
          (le_div_iff₀ hbR).2 (by simpa [mul_comm] using hmem.2.2)
        _ = 2 * (Y / (b : ℝ)) := by ring
  have hDeriv : ∀ r ≤ 2 * k, ∀ y : ℝ,
      ‖iteratedDeriv r g y‖ ≤
        (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr y
    have hraw := hprofile a b q ha hb hq hqQ h x r hr y
    have hratio : 0 ≤ (b : ℝ) / ((q : ℝ) * Q) := by positivity
    dsimp [g]
    calc
      ‖iteratedDeriv r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := hraw
      _ ≤ (C * ((q : ℝ) * Q)⁻¹) *
          (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r := by
        have hratio_le : (b : ℝ) / ((q : ℝ) * Q) ≤
            2 * ((b : ℝ) / ((q : ℝ) * Q)) := by linarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) (by positivity)
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := C * ((q : ℝ) * Q)⁻¹)
    (B := 2 * ((b : ℝ) / ((q : ℝ) * Q)))
    (S := Y / (b : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    (show 0 ≤ C * ((q : ℝ) * Q)⁻¹ by positivity) hB hS hSB hSupport
    r branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  simpa [g] using hout

/-- Fixed-instance compatibility form of the source-specialized
second-variable recurrence tail. -/
theorem exists_dfiEquation29_ySlice_recurrence_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) n‖ ≤
          (((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) *
                  (C * ((q : ℝ) * Q)⁻¹ *
                    (((2 * k + 3 : ℕ) : ℝ) * (Y / b) *
                      (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_ySlice_recurrence_tail_bound_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hUQ k

/-- First-variable form of DFI (29) with the two recurrence factors
combined into the published frequency ratio `aX/(nQ²)`. -/
theorem exists_dfiEquation29_xSlice_source_ratio_tail_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation29_xSlice_recurrence_tail_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ k
  refine ⟨C, hC, ?_⟩
  intro a b q r ha hb hqInst hrInst hrq hqQ h y branch n hn
  letI : NeZero q := hqInst
  letI : NeZero r := hrInst
  have hq : 0 < q := NeZero.pos q
  have hr : 0 < r := NeZero.pos r
  have hraw := hbound a b q r ha hb hqInst hrInst hqQ h y branch n hn
  have hQ : 0 < Q := w.Q_pos
  have hX : 0 ≤ X := zero_le_one.trans hf.one_le_X
  calc
    ‖dfiEquation29InitialTransform r branch
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) n‖ ≤ _ := hraw
    _ = (((((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((((2 * k + 3 : ℕ) : ℝ) * (X / a) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k)) *
          ((14 * Real.pi + 8) / Real.sqrt r *
            (((X / a) ^ (-(1 / 4 : ℝ)) *
              ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by ring
    _ ≤ _ := by
      gcongr
      exact dfiEquation29_recurrence_ratio_le hQ hX ha hq hr hn hrq
        (by positivity) k

/-- Fixed-instance compatibility form of the first-variable source-ratio
tail. -/
theorem exists_dfiEquation29_xSlice_source_ratio_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_xSlice_source_ratio_tail_bound_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hUQ k

/-- Second-variable form of DFI (29) with the published frequency ratio
`bY/(nQ²)`. -/
theorem exists_dfiEquation29_ySlice_source_ratio_tail_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation29_ySlice_recurrence_tail_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ k
  refine ⟨C, hC, ?_⟩
  intro a b q r ha hb hqInst hrInst hrq hqQ h x branch n hn
  letI : NeZero q := hqInst
  letI : NeZero r := hrInst
  have hq : 0 < q := NeZero.pos q
  have hr : 0 < r := NeZero.pos r
  have hraw := hbound a b q r ha hb hqInst hrInst hqQ h x branch n hn
  have hQ : 0 < Q := w.Q_pos
  have hY : 0 ≤ Y := zero_le_one.trans hf.one_le_Y
  calc
    ‖dfiEquation29InitialTransform r branch
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) n‖ ≤ _ := hraw
    _ = (((((r : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((((2 * k + 3 : ℕ) : ℝ) * (Y / b) *
            (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k)) *
          ((14 * Real.pi + 8) / Real.sqrt r *
            (((Y / b) ^ (-(1 / 4 : ℝ)) *
              ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by ring
    _ ≤ _ := by
      gcongr
      exact dfiEquation29_recurrence_ratio_le hQ hY hb hq hr hn hrq
        (by positivity) k

/-- Fixed-instance compatibility form of the second-variable source-ratio
tail. -/
theorem exists_dfiEquation29_ySlice_source_ratio_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt r *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_ySlice_source_ratio_tail_bound_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hUQ k

/-- DFI (29) for an actual first-variable Voronoi summand, including the
native divisor coefficient.  The cutoff ratio and the divisor loss remain
separate so that the subsequent tail summation can choose its shift order. -/
theorem exists_dfiEquation29_xSlice_source_ratio_dualTerm_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x y) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt r *
                (((X / a) ^ (-(1 / 4 : ℝ)) *
                  ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_xSlice_source_ratio_tail_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q r ha hb hq hr hrq hqQ h y branch n hn
  letI : NeZero q := hq
  letI : NeZero r := hr
  have hT := hTransform a b q r ha hb hq hr hrq hqQ h y branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ *
        ‖dfiEquation29InitialTransform r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x y) n‖ ≤
      (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt r *
            (((X / a) ^ (-(1 / 4 : ℝ)) *
              ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = _ := by ring

/-- Fixed-instance compatibility form of the first-variable source-ratio
dual-term bound. -/
theorem exists_dfiEquation29_xSlice_source_ratio_dualTerm_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm r branch
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x y) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt r *
                (((X / a) ^ (-(1 / 4 : ℝ)) *
                  ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cψ, hψC⟩ := hψ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_xSlice_source_ratio_dualTerm_bound_of_profiles
    hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k

/-- Second-variable counterpart of the preceding source-ratio estimate. -/
theorem exists_dfiEquation29_ySlice_source_ratio_dualTerm_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt r *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_ySlice_source_ratio_tail_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q r ha hb hq hr hrq hqQ h x branch n hn
  letI : NeZero q := hq
  letI : NeZero r := hr
  have hT := hTransform a b q r ha hb hq hr hrq hqQ h x branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ *
        ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x) n‖ ≤
      (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt r *
            (((Y / b) ^ (-(1 / 4 : ℝ)) *
              ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = _ := by ring

/-- Fixed-instance compatibility form of the second-variable source-ratio
dual-term bound. -/
theorem exists_dfiEquation29_ySlice_source_ratio_dualTerm_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q r : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hr : NeZero r) → (r : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm r branch
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt r *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cψ, hψC⟩ := hψ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_ySlice_source_ratio_dualTerm_bound_of_profiles
    hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k

/-- Uniform derivative profile for the actual mixed `x`-dual/`y`-main
test function.  The logarithmic main operator contributes only its literal
interval norm; the differentiating variable keeps the source scale
`a/(qQ)` from equation (28). -/
theorem exists_dfiEquation29_xMainSlice_derivative_profile_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (r : ℕ), r ≤ J → ∀ x : ℝ,
        ‖iteratedDeriv r (fun x' ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x')) x‖ ≤
          (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (Y / b) * (C * ((q : ℝ) * Q)⁻¹) *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_dfiEquation28_xSlice_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ J
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h r hr x
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  rw [show (fun x' ↦ dfiVoronoiMainTerm qy
      (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
        a b h q x')) = (fun x' ↦ dfiVoronoiMainTerm qy (E x')) by rfl]
  rw [iteratedDeriv_dfiVoronoiMainTerm_second hE hYC hSupport qy r x]
  have hMain := norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    hYC hYCD qy hqy
    (support_dfiMixedDeriv_first_slice_subset hSupport r x)
    (fun y _hy ↦ by
      simpa only [E, dfiMixedDeriv, iteratedDeriv_zero] using
        hProfile a b q ha hb hq hqQ h y r hr x)
  calc
    ‖dfiVoronoiMainTerm qy (fun y ↦ dfiMixedDeriv r 0 E x y)‖ ≤
        (qy : ℝ)⁻¹ * ((2 * Y / b) - (Y / b)) *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r) := hMain
    _ = _ := by ring

/-- Symmetric derivative profile for the actual `x`-main/`y`-dual test
function.  The main operator contributes its literal `x`-interval norm,
while every differentiated source factor retains the scale `b/(qQ)`. -/
theorem exists_dfiEquation29_yMainSlice_derivative_profile_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (r : ℕ), r ≤ J → ∀ y : ℝ,
        ‖iteratedDeriv r
          (fun y' ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y')) y‖ ≤
          (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (X / a) * (C * ((q : ℝ) * Q)⁻¹) *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_dfiEquation28_ySlice_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ J
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h r hr y
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  rw [show (fun y' ↦ dfiVoronoiMainTerm qx (fun x ↦
      dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
        a b h q x y')) =
      (fun y' ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y')) by rfl]
  rw [iteratedDeriv_dfiVoronoiMainTerm_first hE hXA hSupport qx r y]
  have hMain := norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    hXA hXAB qx hqx
    (support_dfiMixedDeriv_second_slice_subset hSupport r y)
    (fun x _hx ↦ by
      simpa only [E, dfiMixedDeriv, iteratedDeriv_zero] using
        hProfile a b q ha hb hq hqQ h x r hr y)
  calc
    ‖dfiVoronoiMainTerm qx (fun x ↦ dfiMixedDeriv 0 r E x y)‖ ≤
        (qx : ℝ)⁻¹ * ((2 * X / a) - (X / a)) *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r) := hMain
    _ = _ := by ring

/-- The first recurrence estimate for the actual mixed `x`-dual/`y`-main
term in DFI (24).  In contrast with a generic shifted-contour estimate, this
keeps the derivative scale `a/(qQ)` visible.  Consequently the Bessel
recurrence cancels the reduced Voronoi modulus against that scale and leaves
the source frequency ratio `aX/(nQ²)` from DFI (29). -/
theorem exists_dfiEquation29_xMain_source_l1_transform_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qx : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt qx *
              ((X / a) ^ (-(1 / 4 : ℝ)) *
                (C * (qy : ℝ)⁻¹ *
                  (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                  ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_integral_Icc_norm_iteratedDeriv_dfiEquation23_yMain_le
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q qx qy ha hb hqInst hqxInst hqyInst hqxq hqQ h branch n hn
  letI : NeZero q := hqInst
  letI : NeZero qx := hqxInst
  letI : NeZero qy := hqyInst
  have hq : 0 < q := NeZero.pos q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let g : ℝ → ℂ := fun x ↦ dfiVoronoiMainTerm qy (E x)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) := div_pos hY hbR
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hg : DFIVoronoiTestFunction g := by
    simpa only [g, Eswap] using dfiVoronoiMainTermFamilyTestFunction
      hEswap hYC hXA hXAB hSupportSwap qy
  have hgSupport : Function.support g ⊆
      Set.Icc (X / a) (2 * (X / a)) := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      have hm := hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)
      exact hnot ⟨hm.1.1, by
        calc
          x ≤ (2 * X) / (a : ℝ) := hm.1.2
          _ = 2 * (X / (a : ℝ)) := by ring⟩
    change dfiVoronoiMainTerm qy (E x) ≠ 0 at hx
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hx
    exact hx rfl
  have hQpos : 0 < Q := by linarith
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleX : U ≤ X := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min hX.le hY.le
    exact hscale.trans
      ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_left X Y))
  have hqQle : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  let Bscale : ℝ := 2 * ((a : ℝ) / ((q : ℝ) * Q))
  have hBscale : 0 ≤ Bscale := by dsimp [Bscale]; positivity
  have hSB : 1 ≤ (X / (a : ℝ)) * Bscale := by
    have hqQpos : 0 < (q : ℝ) * Q := by positivity
    dsimp [Bscale]
    rw [show (X / (a : ℝ)) *
        (2 * ((a : ℝ) / ((q : ℝ) * Q))) =
      2 * X / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  let A : ℝ := C * (qy : ℝ)⁻¹ *
    (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
    ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  have hA : 0 ≤ A := by
    dsimp [A]
    have hmin : 0 ≤ min X Y := le_min hX.le hY.le
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hL1 : ∀ r ≤ 2 * k,
      (∫ x in Set.Icc (X / a) (2 * (X / a)),
        ‖iteratedDeriv r g x‖) ≤ A * Bscale ^ r := by
    intro r hr
    have hraw := hProfile a b ha hb q hq hqQ qy hqy h r hr
    have hratio : 0 ≤ (a : ℝ) / ((q : ℝ) * Q) := by positivity
    have hratio_le : (a : ℝ) / ((q : ℝ) * Q) ≤ Bscale := by
      dsimp [Bscale]
      linarith
    calc
      (∫ x in Set.Icc (X / a) (2 * (X / a)),
          ‖iteratedDeriv r g x‖) =
          ∫ x in Set.Icc (X / a) (2 * X / a),
            ‖iteratedDeriv r g x‖ := by
              congr 2
              ext x
              ring_nf
      _ ≤ A * (((a : ℝ) / ((q : ℝ) * Q)) ^ r) := by
        simpa only [g, E, A, mul_assoc] using hraw
      _ ≤ A * Bscale ^ r :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) hA
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_l1_profile
    (A := A) (B := Bscale) (S := X / (a : ℝ))
    (D := ((2 * k + 3 : ℕ) : ℝ)) hA hBscale hXA hSB hgSupport
    qx branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hL1
  calc
    ‖dfiEquation29InitialTransform qx branch g n‖ ≤ _ := hout
    _ = ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (((2 * k + 3 : ℕ) : ℝ) * (X / a) * Bscale ^ 2) ^ k) *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          ((X / a) ^ (-(1 / 4 : ℝ)) * A *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by ring
    _ ≤ _ := by
      let L : ℝ :=
        (((qx : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (((2 * k + 3 : ℕ) : ℝ) * (X / a) * Bscale ^ 2) ^ k
      let R : ℝ := ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k
      let G : ℝ := (14 * Real.pi + 8) / Real.sqrt qx *
        ((X / a) ^ (-(1 / 4 : ℝ)) * A *
          (n : ℝ) ^ (-(1 / 4 : ℝ)))
      have hratio : L ≤ R := by
        dsimp only [L, R]
        simpa only [Bscale] using dfiEquation29_recurrence_ratio_le
          hQpos hX.le ha hq hqx hn hqxq
            (D := ((2 * k + 3 : ℕ) : ℝ)) (by positivity) k
      have hG : 0 ≤ G := by dsimp only [G]; positivity
      calc
        _ = L * G := by dsimp only [L, G]
        _ ≤ R * G := mul_le_mul_of_nonneg_right hratio hG
        _ = _ := by dsimp only [R, G, A]

/-- Frequency-independent coefficient of the source-sharp
`x`-dual/`y`-main tail. -/
noncomputable def dfiEquation29XSingleMainTailL1Coefficient
    (C D : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b qx qy : ℕ) : ℝ :=
  (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
      (((a : ℝ) * X) / Q ^ 2)) ^ k) *
    (D * ((14 * Real.pi + 8) / Real.sqrt qx *
      ((X / a) ^ (-(1 / 4 : ℝ)) *
        (C * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q))))

theorem dfiEquation29XSingleMainTailL1Coefficient_nonneg
    {C D Q X Y : ℝ} {k a b qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : 2 ≤ Q)
    (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29XSingleMainTailL1Coefficient
      C D k Q X Y a b qx qy := by
  unfold dfiEquation29XSingleMainTailL1Coefficient
  have hmin : 0 ≤ min X Y := le_min hX.le hY.le
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  positivity

/-- Divisor-weighted, power-normalized source-sharp summand estimate for
the actual `x`-dual/`y`-main branch of equation (24). -/
theorem exists_dfiEquation29_xMain_source_l1_power_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qx : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
          dfiEquation29XSingleMainTailL1Coefficient
              C D k Q X Y a b qx qy *
            (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_xMain_source_l1_transform_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqxq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hT := hTransform a b q qx qy ha hb hq hqx hqy hqxq hqQ
    h branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  have hnorm := dfiEquation29_frequency_power_normalization
    (R := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2)
    (Z := (a : ℝ) * X) (Q := Q) (ε := ε)
    (by linarith : 0 < Q) hn k
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ *
        ‖dfiEquation29InitialTransform qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
      (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qx *
            ((X / a) ^ (-(1 / 4 : ℝ)) *
              (C * (qy : ℝ)⁻¹ *
                (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = dfiEquation29XSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      unfold dfiEquation29XSingleMainTailL1Coefficient
      let B : ℝ := (14 * Real.pi + 8) / Real.sqrt qx *
        ((X / a) ^ (-(1 / 4 : ℝ)) *
          (C * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q))
      calc
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
              ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
                dsimp only [B]
                ring
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((a : ℝ) * X) / Q ^ 2)) ^ k *
              (n : ℝ) ^ (ε - 1 / 4 - k)) := by rw [hnorm]
        _ = _ := by dsimp only [B]; ring

theorem exists_dfiEquation29_xMain_source_ratio_transform_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qx : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt qx *
              (((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) *
                  ((qy : ℝ)⁻¹ *
                    (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                    (Y / b) * (C * ((q : ℝ) * Q)⁻¹)))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_dfiEquation29_xMainSlice_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q qx qy ha hb hqInst hqxInst hqyInst hqxq hqQ h branch n hn
  letI : NeZero q := hqInst
  letI : NeZero qx := hqxInst
  letI : NeZero qy := hqyInst
  have hq : 0 < q := NeZero.pos q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let g : ℝ → ℂ := fun x ↦ dfiVoronoiMainTerm qy (E x)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) := div_pos hY hbR
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hg : DFIVoronoiTestFunction g := by
    simpa only [g, Eswap] using dfiVoronoiMainTermFamilyTestFunction
      hEswap hYC hXA hXAB hSupportSwap qy
  have hgSupport : Function.support g ⊆
      Set.Icc (X / a) (2 * (X / a)) := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot ⟨
        (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1.1,
        (by
          calc
            x ≤ (2 * X) / (a : ℝ) :=
              (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
                simpa only [Function.mem_support,
                  Function.uncurry_apply_pair] using hne)).1.2
            _ = 2 * (X / (a : ℝ)) := by ring)⟩
    change dfiVoronoiMainTerm qy (E x) ≠ 0 at hx
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hx
    exact hx rfl
  have hQ : 0 < Q := w.Q_pos
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleX : U ≤ X := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min hX.le hY.le
    exact hscale.trans
      ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_left X Y))
  have hqQle : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  have hB : 0 ≤ 2 * ((a : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (X / (a : ℝ)) *
      (2 * ((a : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := by positivity
    rw [show (X / (a : ℝ)) *
        (2 * ((a : ℝ) / ((q : ℝ) * Q))) =
      2 * X / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  let A : ℝ :=
    (qy : ℝ)⁻¹ *
      (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
      (Y / b) * (C * ((q : ℝ) * Q)⁻¹)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDeriv : ∀ r ≤ 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤
        A * (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr x
    have hraw := hProfile a b q qy ha hb hq hqy hqQ h r hr x
    have hratio : 0 ≤ (a : ℝ) / ((q : ℝ) * Q) := by positivity
    have hratio_le : (a : ℝ) / ((q : ℝ) * Q) ≤
        2 * ((a : ℝ) / ((q : ℝ) * Q)) := by linarith
    dsimp only [g, E]
    calc
      _ ≤ A * ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
        simpa only [A, mul_assoc] using hraw
      _ ≤ A * (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ r :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) hA
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := A) (B := 2 * ((a : ℝ) / ((q : ℝ) * Q)))
    (S := X / (a : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    hA hB hXA hSB hgSupport qx branch hn k
      (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  calc
    ‖dfiEquation29InitialTransform qx branch g n‖ ≤ _ := hout
    _ = (((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((((2 * k + 3 : ℕ) : ℝ) * (X / a) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k)) *
          ((14 * Real.pi + 8) / Real.sqrt qx *
            (((X / a) ^ (-(1 / 4 : ℝ)) * ((X / a) * A)) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by ring
    _ ≤ _ := by
      gcongr
      exact dfiEquation29_recurrence_ratio_le hQ hX.le ha hq hqx hn hqxq
        (by positivity) k

/-- Divisor-weighted form of the preceding recurrence estimate.  This is
the literal summand in the `x`-dual/`y`-main branch of equation (24), not a
separately supplied model transform. -/
theorem exists_dfiEquation29_xMain_source_ratio_dualTerm_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qx : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qx *
                (((X / a) ^ (-(1 / 4 : ℝ)) *
                  ((X / a) *
                    ((qy : ℝ)⁻¹ *
                      (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                      (Y / b) * (C * ((q : ℝ) * Q)⁻¹)))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_xMain_source_ratio_transform_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqxq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hT := hTransform a b q qx qy ha hb hq hqx hqy hqxq hqQ
    h branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ *
        ‖dfiEquation29InitialTransform qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
      (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qx *
            (((X / a) ^ (-(1 / 4 : ℝ)) *
              ((X / a) *
                ((qy : ℝ)⁻¹ *
                  (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                  (Y / b) * (C * ((q : ℝ) * Q)⁻¹)))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = _ := by ring

/-- Frequency-independent coefficient of the actual `x`-dual/`y`-main
tail after the equation-(29) recurrence. -/
noncomputable def dfiEquation29XSingleMainTailCoefficient
    (C D : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b q qx qy : ℕ) : ℝ :=
  (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
      (((a : ℝ) * X) / Q ^ 2)) ^ k) *
    (D * ((14 * Real.pi + 8) / Real.sqrt qx *
      ((X / a) ^ (-(1 / 4 : ℝ)) *
        ((X / a) *
          ((qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (Y / b) * (C * ((q : ℝ) * Q)⁻¹))))))

theorem dfiEquation29XSingleMainTailCoefficient_nonneg
    {C D Q X Y : ℝ} {k a b q qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : 0 < Q)
    (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hq : 0 < q) (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29XSingleMainTailCoefficient
      C D k Q X Y a b q qx qy := by
  unfold dfiEquation29XSingleMainTailCoefficient
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqxR : (0 : ℝ) < qx := by exact_mod_cast hqx
  have hqyR : (0 : ℝ) < qy := by exact_mod_cast hqy
  positivity

/-- Power-normalized summand estimate for the actual one-sided branch.
All dependence on the source frequency is now the summable power
`n^(ε - 1/4 - k)`. -/
theorem exists_dfiEquation29_xMain_source_power_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qx : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy
            (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x)) n‖ ≤
          dfiEquation29XSingleMainTailCoefficient
              C D k Q X Y a b q qx qy *
            (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_xMain_source_ratio_dualTerm_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqxq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hraw := hPoint a b q qx qy ha hb hq hqx hqy hqxq hqQ
    h branch n hn
  have hnorm := dfiEquation29_frequency_power_normalization
    (R := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2)
    (Z := (a : ℝ) * X) (Q := Q) (ε := ε) w.Q_pos hn k
  calc
    ‖dfiVoronoiDualTerm qx branch
        (fun x ↦ dfiVoronoiMainTerm qy
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x)) n‖ ≤ _ := hraw
    _ = dfiEquation29XSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      unfold dfiEquation29XSingleMainTailCoefficient
      let B : ℝ := (14 * Real.pi + 8) / Real.sqrt qx *
        ((X / a) ^ (-(1 / 4 : ℝ)) *
          ((X / a) *
            ((qy : ℝ)⁻¹ *
              (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
              (Y / b) * (C * ((q : ℝ) * Q)⁻¹))))
      calc
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k *
              ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
              dsimp only [B]
              ring
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((a : ℝ) * X) / Q ^ 2)) ^ k *
              (n : ℝ) ^ (ε - 1 / 4 - k)) := by rw [hnorm]
        _ = _ := by dsimp only [B]; ring

/-- Source-sharp symmetric equation-(29) recurrence for the actual
`x`-main/`y`-dual branch.  The `L¹` derivative profile retains
`(ab)⁻¹ min(X,Y)` and therefore removes the spurious full support-length
factor from the older pointwise route. -/
theorem exists_dfiEquation29_yMain_source_l1_transform_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qy : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt qy *
              ((Y / b) ^ (-(1 / 4 : ℝ)) *
                (C * (qx : ℝ)⁻¹ *
                  (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                  ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_integral_Icc_norm_iteratedDeriv_dfiEquation23_xMain_le
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q qx qy ha hb hqInst hqxInst hqyInst hqyq hqQ h branch n hn
  letI : NeZero q := hqInst
  letI : NeZero qx := hqxInst
  letI : NeZero qy := hqyInst
  have hq : 0 < q := NeZero.pos q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let g : ℝ → ℂ := fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hYC : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hg : DFIVoronoiTestFunction g := by
    simpa only [g, E] using dfiVoronoiMainTermFamilyTestFunction
      hE hXA hYC hYCD hSupport qx
  have hgSupport : Function.support g ⊆
      Set.Icc (Y / b) (2 * (Y / b)) := by
    intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      have hm := hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)
      exact hnot ⟨hm.2.1, by
        calc
          y ≤ (2 * Y) / (b : ℝ) := hm.2.2
          _ = 2 * (Y / (b : ℝ)) := by ring⟩
    change dfiVoronoiMainTerm qx (fun x ↦ E x y) ≠ 0 at hy
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hy
    exact hy rfl
  have hQpos : 0 < Q := by linarith
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleY : U ≤ Y := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min hX.le hY.le
    exact hscale.trans
      ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_right X Y))
  have hqQle : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  let Bscale : ℝ := 2 * ((b : ℝ) / ((q : ℝ) * Q))
  have hBscale : 0 ≤ Bscale := by dsimp [Bscale]; positivity
  have hSB : 1 ≤ (Y / (b : ℝ)) * Bscale := by
    have hqQpos : 0 < (q : ℝ) * Q := by positivity
    dsimp [Bscale]
    rw [show (Y / (b : ℝ)) *
        (2 * ((b : ℝ) / ((q : ℝ) * Q))) =
      2 * Y / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  let A : ℝ := C * (qx : ℝ)⁻¹ *
    (|Real.log (X / a)| + |Real.log (2 * X / a)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
    ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  have hA : 0 ≤ A := by
    dsimp [A]
    have hmin : 0 ≤ min X Y := le_min hX.le hY.le
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hL1 : ∀ r ≤ 2 * k,
      (∫ y in Set.Icc (Y / b) (2 * (Y / b)),
        ‖iteratedDeriv r g y‖) ≤ A * Bscale ^ r := by
    intro r hr
    have hraw := hProfile a b ha hb q hq hqQ qx hqx h r hr
    have hratio : 0 ≤ (b : ℝ) / ((q : ℝ) * Q) := by positivity
    have hratio_le : (b : ℝ) / ((q : ℝ) * Q) ≤ Bscale := by
      dsimp [Bscale]
      linarith
    calc
      (∫ y in Set.Icc (Y / b) (2 * (Y / b)),
          ‖iteratedDeriv r g y‖) =
          ∫ y in Set.Icc (Y / b) (2 * Y / b),
            ‖iteratedDeriv r g y‖ := by
              congr 2
              ext y
              ring_nf
      _ ≤ A * (((b : ℝ) / ((q : ℝ) * Q)) ^ r) := by
        simpa only [g, E, A, mul_assoc] using hraw
      _ ≤ A * Bscale ^ r :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) hA
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_l1_profile
    (A := A) (B := Bscale) (S := Y / (b : ℝ))
    (D := ((2 * k + 3 : ℕ) : ℝ)) hA hBscale hYC hSB hgSupport
    qy branch hn k (by exact_mod_cast (le_refl (2 * k + 3))) hL1
  calc
    ‖dfiEquation29InitialTransform qy branch g n‖ ≤ _ := hout
    _ = ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (((2 * k + 3 : ℕ) : ℝ) * (Y / b) * Bscale ^ 2) ^ k) *
        ((14 * Real.pi + 8) / Real.sqrt qy *
          ((Y / b) ^ (-(1 / 4 : ℝ)) * A *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by ring
    _ ≤ _ := by
      let L : ℝ :=
        (((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          (((2 * k + 3 : ℕ) : ℝ) * (Y / b) * Bscale ^ 2) ^ k
      let R : ℝ := ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k
      let G : ℝ := (14 * Real.pi + 8) / Real.sqrt qy *
        ((Y / b) ^ (-(1 / 4 : ℝ)) * A *
          (n : ℝ) ^ (-(1 / 4 : ℝ)))
      have hratio : L ≤ R := by
        dsimp only [L, R]
        simpa only [Bscale] using dfiEquation29_recurrence_ratio_le
          hQpos hY.le hb hq hqy hn hqyq
            (D := ((2 * k + 3 : ℕ) : ℝ)) (by positivity) k
      have hG : 0 ≤ G := by dsimp only [G]; positivity
      calc
        _ = L * G := by dsimp only [L, G]
        _ ≤ R * G := mul_le_mul_of_nonneg_right hratio hG
        _ = _ := by dsimp only [R, G, A]

/-- Frequency-independent coefficient of the source-sharp symmetric
one-sided tail. -/
noncomputable def dfiEquation29YSingleMainTailL1Coefficient
    (C D : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b qx qy : ℕ) : ℝ :=
  (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
      (((b : ℝ) * Y) / Q ^ 2)) ^ k) *
    (D * ((14 * Real.pi + 8) / Real.sqrt qy *
      ((Y / b) ^ (-(1 / 4 : ℝ)) *
        (C * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q))))

theorem dfiEquation29YSingleMainTailL1Coefficient_nonneg
    {C D Q X Y : ℝ} {k a b qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : 2 ≤ Q)
    (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29YSingleMainTailL1Coefficient
      C D k Q X Y a b qx qy := by
  unfold dfiEquation29YSingleMainTailL1Coefficient
  have hmin : 0 ≤ min X Y := le_min hX.le hY.le
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  positivity

/-- Divisor-weighted, power-normalized source-sharp summand estimate for
the actual `x`-main/`y`-dual branch of equation (24). -/
theorem exists_dfiEquation29_yMain_source_l1_power_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qy : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
          dfiEquation29YSingleMainTailL1Coefficient
              C D k Q X Y a b qx qy *
            (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_yMain_source_l1_transform_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqyq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hT := hTransform a b q qx qy ha hb hq hqx hqy hqyq hqQ
    h branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  have hnorm := dfiEquation29_frequency_power_normalization
    (R := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2)
    (Z := (b : ℝ) * Y) (Q := Q) (ε := ε)
    (by linarith : 0 < Q) hn k
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ *
        ‖dfiEquation29InitialTransform qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
      (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qy *
            ((Y / b) ^ (-(1 / 4 : ℝ)) *
              (C * (qx : ℝ)⁻¹ *
                (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = dfiEquation29YSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      unfold dfiEquation29YSingleMainTailL1Coefficient
      let B : ℝ := (14 * Real.pi + 8) / Real.sqrt qy *
        ((Y / b) ^ (-(1 / 4 : ℝ)) *
          (C * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q))
      calc
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
              ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
                dsimp only [B]
                ring
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((b : ℝ) * Y) / Q ^ 2)) ^ k *
              (n : ℝ) ^ (ε - 1 / 4 - k)) := by rw [hnorm]
        _ = _ := by dsimp only [B]; ring

/-- Symmetric equation-(29) recurrence for the actual
`x`-main/`y`-dual branch. -/
theorem exists_dfiEquation29_yMain_source_ratio_transform_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qy : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt qy *
              (((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) *
                  ((qx : ℝ)⁻¹ *
                    (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                    (X / a) * (C * ((q : ℝ) * Q)⁻¹)))) *
                (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_dfiEquation29_yMainSlice_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ (2 * k)
  refine ⟨C, hC, ?_⟩
  intro a b q qx qy ha hb hqInst hqxInst hqyInst hqyq hqQ h branch n hn
  letI : NeZero q := hqInst
  letI : NeZero qx := hqxInst
  letI : NeZero qy := hqyInst
  have hq : 0 < q := NeZero.pos q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let g : ℝ → ℂ := fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hXA : 0 < X / (a : ℝ) := div_pos hX haR
  have hYC : 0 < Y / (b : ℝ) := div_pos hY hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hg : DFIVoronoiTestFunction g := by
    simpa only [g, E] using dfiVoronoiMainTermFamilyTestFunction
      hE hXA hYC hYCD hSupport qx
  have hgSupport : Function.support g ⊆
      Set.Icc (Y / b) (2 * (Y / b)) := by
    intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      have hm := hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)
      exact hnot ⟨hm.2.1, by
        calc
          y ≤ (2 * Y) / (b : ℝ) := hm.2.2
          _ = 2 * (Y / (b : ℝ)) := by ring⟩
    change dfiVoronoiMainTerm qx (fun x ↦ E x y) ≠ 0 at hy
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hy
    exact hy rfl
  have hQ : 0 < Q := w.Q_pos
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hUleY : U ≤ Y := by
    have hPinv : P⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hP]
      exact hf.one_le_P
    have hmin0 : 0 ≤ min X Y := le_min hX.le hY.le
    exact hscale.trans
      ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_right X Y))
  have hqQle : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  have hB : 0 ≤ 2 * ((b : ℝ) / ((q : ℝ) * Q)) := by positivity
  have hSB : 1 ≤ (Y / (b : ℝ)) *
      (2 * ((b : ℝ) / ((q : ℝ) * Q))) := by
    have hqQpos : 0 < (q : ℝ) * Q := by positivity
    rw [show (Y / (b : ℝ)) *
        (2 * ((b : ℝ) / ((q : ℝ) * Q))) =
      2 * Y / ((q : ℝ) * Q) by field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQle)
  let A : ℝ :=
    (qx : ℝ)⁻¹ *
      (|Real.log (X / a)| + |Real.log (2 * X / a)| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
      (X / a) * (C * ((q : ℝ) * Q)⁻¹)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hDeriv : ∀ r ≤ 2 * k, ∀ y : ℝ,
      ‖iteratedDeriv r g y‖ ≤
        A * (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r := by
    intro r hr y
    have hraw := hProfile a b q qx ha hb hq hqx hqQ h r hr y
    have hratio : 0 ≤ (b : ℝ) / ((q : ℝ) * Q) := by positivity
    have hratio_le : (b : ℝ) / ((q : ℝ) * Q) ≤
        2 * ((b : ℝ) / ((q : ℝ) * Q)) := by linarith
    dsimp only [g, E]
    calc
      _ ≤ A * ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
        simpa only [A, mul_assoc] using hraw
      _ ≤ A * (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ r :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio hratio_le r) hA
  have hout := hg.norm_dfiEquation29InitialTransform_le_recurrence_profile
    (A := A) (B := 2 * ((b : ℝ) / ((q : ℝ) * Q)))
    (S := Y / (b : ℝ)) (D := ((2 * k + 3 : ℕ) : ℝ))
    hA hB hYC hSB hgSupport qy branch hn k
      (by exact_mod_cast (le_refl (2 * k + 3))) hDeriv
  calc
    ‖dfiEquation29InitialTransform qy branch g n‖ ≤ _ := hout
    _ = (((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((((2 * k + 3 : ℕ) : ℝ) * (Y / b) *
            (2 * ((b : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k)) *
          ((14 * Real.pi + 8) / Real.sqrt qy *
            (((Y / b) ^ (-(1 / 4 : ℝ)) * ((Y / b) * A)) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by ring
    _ ≤ _ := by
      gcongr
      exact dfiEquation29_recurrence_ratio_le hQ hY.le hb hq hqy hn hqyq
        (by positivity) k

/-- Divisor-weighted symmetric one-sided recurrence estimate. -/
theorem exists_dfiEquation29_yMain_source_ratio_dualTerm_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qy : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) *
                    ((qx : ℝ)⁻¹ *
                      (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                      (X / a) * (C * ((q : ℝ) * Q)⁻¹)))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨C, hC, hTransform⟩ :=
    exists_dfiEquation29_yMain_source_ratio_transform_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ k
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, D, hC, hD.le, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqyq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hT := hTransform a b q qx qy ha hb hq hqx hqy hqyq hqQ
    h branch n hn
  have hDiv : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    _ ≤ (D * (n : ℝ) ^ ε) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qy *
            (((Y / b) ^ (-(1 / 4 : ℝ)) *
              ((Y / b) *
                ((qx : ℝ)⁻¹ *
                  (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                  (X / a) * (C * ((q : ℝ) * Q)⁻¹)))) *
              (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        exact mul_le_mul hDiv hT (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) ε))
    _ = _ := by ring

/-- Frequency-independent coefficient of the symmetric one-sided tail. -/
noncomputable def dfiEquation29YSingleMainTailCoefficient
    (C D : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b q qx qy : ℕ) : ℝ :=
  (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
      (((b : ℝ) * Y) / Q ^ 2)) ^ k) *
    (D * ((14 * Real.pi + 8) / Real.sqrt qy *
      ((Y / b) ^ (-(1 / 4 : ℝ)) *
        ((Y / b) *
          ((qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (X / a) * (C * ((q : ℝ) * Q)⁻¹))))))

theorem dfiEquation29YSingleMainTailCoefficient_nonneg
    {C D Q X Y : ℝ} {k a b q qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : 0 < Q)
    (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hq : 0 < q) (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29YSingleMainTailCoefficient
      C D k Q X Y a b q qx qy := by
  unfold dfiEquation29YSingleMainTailCoefficient
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqxR : (0 : ℝ) < qx := by exact_mod_cast hqx
  have hqyR : (0 : ℝ) < qy := by exact_mod_cast hqy
  positivity

/-- Power-normalized summand estimate for the symmetric one-sided branch. -/
theorem exists_dfiEquation29_yMain_source_power_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q qx qy : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (_hqx : NeZero qx) → (_hqy : NeZero qy) → (qy : ℝ) ≤ q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦
            dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
              a b h q x y)) n‖ ≤
          dfiEquation29YSingleMainTailCoefficient
              C D k Q X Y a b q qx qy *
            (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_yMain_source_ratio_dualTerm_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q qx qy ha hb hq hqx hqy hqyq hqQ h branch n hn
  letI : NeZero q := hq
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  have hraw := hPoint a b q qx qy ha hb hq hqx hqy hqyq hqQ
    h branch n hn
  have hnorm := dfiEquation29_frequency_power_normalization
    (R := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2)
    (Z := (b : ℝ) * Y) (Q := Q) (ε := ε) w.Q_pos hn k
  calc
    _ ≤ _ := hraw
    _ = dfiEquation29YSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      unfold dfiEquation29YSingleMainTailCoefficient
      let B : ℝ := (14 * Real.pi + 8) / Real.sqrt qy *
        ((Y / b) ^ (-(1 / 4 : ℝ)) *
          ((Y / b) *
            ((qx : ℝ)⁻¹ *
              (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
              (X / a) * (C * ((q : ℝ) * Q)⁻¹))))
      calc
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
              ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
              dsimp only [B]
              ring
        _ = (D * B) *
            (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
                (((b : ℝ) * Y) / Q ^ 2)) ^ k *
              (n : ℝ) ^ (ε - 1 / 4 - k)) := by rw [hnorm]
        _ = _ := by dsimp only [B]; ring

/-- The physical Bessel norm of a mixed Voronoi branch is controlled by
the literal two-variable `L¹` mass of the source weight.  This is the
source-faithful bridge from DFI (29) to the mass estimate in DFI (30). -/
theorem dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) :
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiMainTerm q (E x)) ≤
      A ^ (-(1 / 4 : ℝ)) * (q : ℝ)⁻¹ *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) := by
  let W : ℝ := |Real.log C| + |Real.log D| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hFamily : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm q (E x)) := by
    simpa only [Eswap] using dfiVoronoiMainTermFamilyTestFunction
      hEswap hC hA hAB hSupportSwap q
  have hFamilySupport : Function.support
      (fun x ↦ dfiVoronoiMainTerm q (E x)) ⊆ Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiMainTerm q (E x) ≠ 0 at hx
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hx
    exact hx rfl
  have hSliceSupport (x : ℝ) :
      Function.support (E x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
  have hSlice (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := hSliceSupport x }
  have hInnerContinuous : Continuous (fun x : ℝ ↦
      ∫ y in Set.Icc C D, ‖E x y‖) := by
    exact continuous_parametric_integral_of_continuous
      hE.continuous.norm isCompact_Icc
  have hLeft : IntegrableOn (fun x : ℝ ↦
      ‖dfiVoronoiMainTerm q (E x)‖) (Set.Icc A B) :=
    hFamily.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun x : ℝ ↦
      (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖E x y‖))
      (Set.Icc A B) :=
    (hInnerContinuous.const_mul ((q : ℝ)⁻¹ * W)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) :
      ‖dfiVoronoiMainTerm q (E x)‖ ≤
        (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖E x y‖) := by
    simpa only [W] using norm_dfiVoronoiMainTerm_le_integral_norm
      hC q hq (hSlice x) (hSliceSupport x)
  have hIntegral :
      (∫ x in Set.Icc A B, ‖dfiVoronoiMainTerm q (E x)‖) ≤
        ∫ x in Set.Icc A B,
          (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖E x y‖) := by
    apply integral_mono_ae hLeft hRight
    filter_upwards with x
    exact hPoint x
  calc
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiMainTerm q (E x)) ≤
        A ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A B, ‖dfiVoronoiMainTerm q (E x)‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hA hFamily hFamilySupport
    _ ≤ A ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B,
          (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖E x y‖)) := by
      exact mul_le_mul_of_nonneg_left hIntegral (Real.rpow_nonneg hA.le _)
    _ = A ^ (-(1 / 4 : ℝ)) * (q : ℝ)⁻¹ * W *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) := by
      have hInner :
          (∫ x in Set.Icc A B,
              (q : ℝ)⁻¹ * W * (∫ y in Set.Icc C D, ‖E x y‖)) =
            ((q : ℝ)⁻¹ * W) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) := by
        rw [integral_const_mul]
      rw [hInner]
      ring

/-- Positive-quadrant version of the mixed physical Bessel estimate.  For
a rectangularly supported DFI weight the compact-rectangle mass is exactly
the positive-quadrant mass used in equations (27) and (30). -/
theorem dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le_Ioi
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) :
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiMainTerm q (E x)) ≤
      A ^ (-(1 / 4 : ℝ)) * (q : ℝ)⁻¹ *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) := by
  have hySubset : Set.Icc C D ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact hC.trans_le hy.1
  have hInnerEq (x : ℝ) :
      (∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        ∫ y in Set.Icc C D, ‖E x y‖ := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hySubset
    intro y hy
    have hzero : E x y = 0 := by
      by_contra hne
      exact hy.2 (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    simp [hzero]
  have hxSubset : Set.Icc A B ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hA.trans_le hx.1
  have hOuterEq :
      (∫ x in Set.Ioi (0 : ℝ),
          ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        ∫ x in Set.Icc A B,
          ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hxSubset
    intro x hx
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hx.2 (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    simp [hzero]
  have hMass :
      (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) =
        ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ := by
    rw [hOuterEq]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact (hInnerEq x).symm
  simpa only [hMass] using
    dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le
      hE hA hAB hC hCD hSupport q hq

/-- Exact restoration of the two positive divisor-variable Jacobians in
the absolute mass of the concrete equation-(23) weight. -/
theorem integral_norm_dfiEquation23Weight_Ioi_eq_scaled_physical_Ioi
    {Q : ℝ} (w : DFIDeltaWeight Q) (q a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (F : ℝ → ℝ → ℂ) (h : ℤ) :
    (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation23Weight w F a b h q x y‖) =
      ((a : ℝ) * b)⁻¹ *
        (∫ X in Set.Ioi (0 : ℝ), ∫ Y in Set.Ioi (0 : ℝ),
          ‖F X Y‖ * |dfiDeltaKernel w q (X - Y - h)|) := by
  let H : ℝ → ℝ → ℝ := fun X Y ↦
    ‖F X Y‖ * |dfiDeltaKernel w q (X - Y - h)|
  let K : ℝ → ℝ := fun X ↦ ∫ Y in Set.Ioi (0 : ℝ), H X Y
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hPoint (x y : ℝ) :
      ‖dfiEquation23Weight w F a b h q x y‖ =
        H (x * (a : ℝ)) (y * (b : ℝ)) := by
    simp only [dfiEquation23Weight, H, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    congr 2 <;> ring
  have hInner (x : ℝ) :
      (∫ y in Set.Ioi (0 : ℝ),
          ‖dfiEquation23Weight w F a b h q x y‖) =
        (b : ℝ)⁻¹ * K (x * (a : ℝ)) := by
    rw [show (fun y ↦ ‖dfiEquation23Weight w F a b h q x y‖) =
        fun y ↦ H (x * (a : ℝ)) (y * (b : ℝ)) by
      funext y
      exact hPoint x y]
    rw [integral_comp_mul_right_Ioi
      (fun Y ↦ H (x * (a : ℝ)) Y) 0 hbR]
    simp only [zero_mul, smul_eq_mul, K]
  rw [show (fun x ↦ ∫ y in Set.Ioi (0 : ℝ),
      ‖dfiEquation23Weight w F a b h q x y‖) =
      fun x ↦ (b : ℝ)⁻¹ * K (x * (a : ℝ)) by
        funext x
        exact hInner x]
  rw [integral_const_mul, integral_comp_mul_right_Ioi K 0 haR]
  simp only [zero_mul, smul_eq_mul]
  dsimp only [K, H]
  ring

/-- A positive-quadrant supported physical weight has the same absolute
mass whether it is integrated over all reals squared or over the source quadrant. -/
theorem dfiEquation30PhysicalAbsoluteIntegral_eq_Ioi
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (F : ℝ → ℝ → ℂ) (h : ℝ)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :
    dfiEquation30PhysicalAbsoluteIntegral w q F h =
      ∫ X in Set.Ioi (0 : ℝ), ∫ Y in Set.Ioi (0 : ℝ),
        ‖F X Y‖ * |dfiDeltaKernel w q (X - Y - h)| := by
  unfold dfiEquation30PhysicalAbsoluteIntegral
  have hInner (X : ℝ) :
      (∫ Y : ℝ, ‖F X Y‖ *
          |dfiDeltaKernel w q (X - Y - h)|) =
        ∫ Y in Set.Ioi (0 : ℝ), ‖F X Y‖ *
          |dfiDeltaKernel w q (X - Y - h)| := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioi (0 : ℝ)) (fun Y hY ↦ ?_)).symm
    have hzero : F X Y = 0 := by
      by_contra hne
      exact hY (hSupport (show
        (X, Y) ∈ Function.support (Function.uncurry F) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    simp [hzero]
  rw [show (fun X ↦ ∫ Y : ℝ,
      ‖F X Y‖ * |dfiDeltaKernel w q (X - Y - h)|) =
      fun X ↦ ∫ Y in Set.Ioi (0 : ℝ),
        ‖F X Y‖ * |dfiDeltaKernel w q (X - Y - h)| by
      funext X
      exact hInner X]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioi (0 : ℝ)) (fun X hX ↦ ?_)).symm
  have hzero : F X = fun _ ↦ 0 := by
    funext Y
    by_contra hne
    exact hX (hSupport (show
      (X, Y) ∈ Function.support (Function.uncurry F) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hne)).1
  simp [hzero]

/-- Exact equation-(30) mass identity for the source equation-(23) weight. -/
theorem integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
    {Q : ℝ} (w : DFIDeltaWeight Q) (q a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (F : ℝ → ℝ → ℂ) (h : ℤ)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :
    (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation23Weight w F a b h q x y‖) =
      dfiEquation30DivisorAbsoluteIntegral w q a b F h := by
  rw [integral_norm_dfiEquation23Weight_Ioi_eq_scaled_physical_Ioi
    w q a b ha hb F h]
  unfold dfiEquation30DivisorAbsoluteIntegral
  rw [dfiEquation30PhysicalAbsoluteIntegral_eq_Ioi
    w q F (h : ℝ) hSupport]

/-- Fubini symmetry for the positive-quadrant mass of a smooth rectangular
DFI weight. -/
theorem integral_integral_norm_swap_Ioi
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    (∫ y in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (0 : ℝ), ‖E x y‖) =
      ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ := by
  let H : ℝ → ℝ → ℝ := fun x y ↦ ‖E x y‖
  have hHcont : Continuous H.uncurry := by
    simpa only [H, Function.uncurry_apply_pair] using hE.continuous.norm
  have hHsupport : Function.support H.uncurry ⊆
      Set.Icc A B ×ˢ Set.Icc C D := by
    intro p hp
    apply hSupport
    intro hz
    change E p.1 p.2 = 0 at hz
    apply hp
    change ‖E p.1 p.2‖ = 0
    rw [hz, norm_zero]
  have hHcompact : HasCompactSupport H.uncurry :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hswap := MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := H)
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    hHcont hHcompact
  simpa only [H] using hswap.symm

set_option maxHeartbeats 2000000 in
/-- Source-uniform physical Bessel norm for the x-dual/y-main mixed
branch.  The right side is precisely the equation-(30) divisor mass times
the quarter-power and logarithmic factors from equation (29). -/
theorem exists_dfiEquation24_xMixedPhysicalBesselBase_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (h : ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        dfiBesselQuarterBaseNorm
            (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)) ≤
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) := by
  obtain ⟨K, hK, hPhysical⟩ :=
    dfiEquation30_physical_log_bound
      w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro a b q qy ha hb hq hqy
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    simpa only [E] using
      integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
        w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hDivisor :
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    unfold dfiEquation30DivisorAbsoluteIntegral
    have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
    calc
      ((a : ℝ) * b)⁻¹ *
          dfiEquation30PhysicalAbsoluteIntegral w q
            (dfiLocalizedWeight f φ h) h ≤
        ((a : ℝ) * b)⁻¹ * (K * min X Y * Real.log Q) :=
          mul_le_mul_of_nonneg_left (hPhysical h q hq) hab
      _ = K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by ring
  have hBessel :=
    dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le_Ioi
      hE hXA hXAB hYC hYCD hSupport qy hqy
  let R : ℝ := (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
    (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  calc
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiMainTerm qy
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x)) ≤
      R * (∫ x in Set.Ioi (0 : ℝ),
        ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) := by
        simpa only [E, R, mul_assoc] using hBessel
    _ = R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h := by rw [hMassEq]
    _ ≤ R * (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) :=
      mul_le_mul_of_nonneg_left hDivisor hR
    _ = (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) := by
      rfl

set_option maxHeartbeats 2000000 in
/-- Symmetric source-uniform physical Bessel norm for the x-main/y-dual
mixed branch. -/
theorem exists_dfiEquation24_yMixedPhysicalBesselBase_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (h : ℤ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        dfiBesselQuarterBaseNorm
            (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)) ≤
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) := by
  obtain ⟨K, hK, hPhysical⟩ :=
    dfiEquation30_physical_log_bound
      w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro a b q qx ha hb hq hqx
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYAB : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    simpa only [E] using
      integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
        w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hSwap :
      (∫ y in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (0 : ℝ), ‖E x y‖) =
        ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
    integral_integral_norm_swap_Ioi hE hSupport
  have hDivisor :
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    unfold dfiEquation30DivisorAbsoluteIntegral
    have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
    calc
      ((a : ℝ) * b)⁻¹ *
          dfiEquation30PhysicalAbsoluteIntegral w q
            (dfiLocalizedWeight f φ h) h ≤
        ((a : ℝ) * b)⁻¹ * (K * min X Y * Real.log Q) :=
          mul_le_mul_of_nonneg_left (hPhysical h q hq) hab
      _ = K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by ring
  have hBessel :=
    dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le_Ioi
      hEswap hYA hYAB hXA hXAB hSupportSwap qx hqx
  let R : ℝ := (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
    (|Real.log (X / a)| + |Real.log (2 * X / a)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  calc
    dfiBesselQuarterBaseNorm
        (fun y ↦ dfiVoronoiMainTerm qx
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y)) ≤
      R * (∫ y in Set.Ioi (0 : ℝ),
        ∫ x in Set.Ioi (0 : ℝ), ‖E x y‖) := by
        simpa only [E, Eswap, R, mul_assoc] using hBessel
    _ = R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h := by rw [hSwap, hMassEq]
    _ ≤ R * (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) :=
      mul_le_mul_of_nonneg_left hDivisor hR
    _ = (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) := by
      rfl

/-- The physical equation-(29)/(30) majorant for one mixed branch. -/
noncomputable def dfiEquation29MixedPhysicalMajorant
    (K Q S R : ℝ) (a b qMain : ℕ) : ℝ :=
  (S / a) ^ (-(1 / 4 : ℝ)) * (qMain : ℝ)⁻¹ *
    (|Real.log (R / b)| + |Real.log (2 * R / b)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qMain|) *
    (K * ((a : ℝ) * b)⁻¹ * min S R * Real.log Q)

/-- Weighted form of `norm_dfiVoronoiMainTerm_le_Icc_of_norm_le`.  A
parameter-uniform Mellin decay estimate passes through the logarithmic main
operator with exactly the same vertical weight. -/
theorem mul_norm_dfiVoronoiMainTerm_le_Icc_of_mul_norm_le
    {A B K R : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hR : 0 < R)
    (q : ℕ) (hq : 0 < q) {g : ℝ → ℂ}
    (hSupport : Function.support g ⊆ Set.Icc A B)
    (hBound : ∀ x ∈ Set.Icc A B, R * ‖g x‖ ≤ K) :
    R * ‖dfiVoronoiMainTerm q g‖ ≤
      (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  have hPoint : ∀ x ∈ Set.Icc A B, ‖g x‖ ≤ K / R := by
    intro x hx
    exact (le_div_iff₀ hR).2 (by simpa [mul_comm] using hBound x hx)
  have hMain := norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    hA hAB q hq hSupport hPoint
  have hRnonneg : 0 ≤ R := hR.le
  calc
    R * ‖dfiVoronoiMainTerm q g‖ ≤
        R * ((q : ℝ)⁻¹ * (B - A) *
          (|Real.log A| + |Real.log B| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
          (K / R)) := mul_le_mul_of_nonneg_left hMain hRnonneg
    _ = (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
      field_simp [hR.ne']

/-- Quantitative mixed-branch Fubini estimate.  Mellin transformation in
the first variable is commuted through the logarithmic main operator in the
second variable, and a uniform vertical-line estimate for the literal
source slices is preserved. -/
theorem mul_norm_mellin_dfiVoronoiMainTerm_family_le
    {E : ℝ → ℝ → ℂ} {A B C D K R : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) (z : ℂ) (hR : 0 < R)
    (hBound : ∀ y ∈ Set.Icc C D,
      R * ‖mellin (fun x ↦ E x y) z‖ ≤ K) :
    R * ‖mellin
        (fun x ↦ dfiVoronoiMainTerm q (E x)) z‖ ≤
      (q : ℝ)⁻¹ * (D - C) *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hmem := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hmem.2, hmem.1⟩
  have hMellinSupport : Function.support
      (fun y ↦ mellin (fun x ↦ E x y) z) ⊆ Set.Icc C D := by
    intro y hy
    by_contra hyOutside
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hyOutside (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    change mellin (fun x ↦ E x y) z ≠ 0 at hy
    rw [hzero] at hy
    exact hy (by simp [mellin])
  rw [show (fun x ↦ dfiVoronoiMainTerm q (E x)) =
      fun x ↦ dfiVoronoiMainTerm q (fun y ↦ Eswap y x) by rfl]
  rw [mellin_dfiVoronoiMainTerm_comm_of_rectangular_support
    hEswap hC hA hSupportSwap q z]
  exact mul_norm_dfiVoronoiMainTerm_le_Icc_of_mul_norm_le
    hC hCD hR q hq hMellinSupport hBound

/-- Applying the logarithmic main operator in the second variable preserves
the DFI test-function class in the first variable. -/
noncomputable def dfiVoronoiMainTermSecondFamilyTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm q (E x)) := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  simpa only [Eswap] using dfiVoronoiMainTermFamilyTestFunction
    hEswap hC hA hAB hSupportSwap q

/-- The elementary partial-sum estimate needed for DFI's retained dual
frequencies. -/
theorem sum_Icc_natCast_rpow_neg_quarter_le (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  cases L with
  | zero => simp
  | succ K =>
      let f : ℝ → ℝ := fun x ↦ x ^ (-(1 / 4 : ℝ))
      have hanti : AntitoneOn f (Set.Icc 1 (1 + K)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
          (fun x hx ↦ lt_of_lt_of_le zero_lt_one hx.1)
      have htail :
          ∑ j ∈ Finset.range K, f (1 + (j + 1 : ℕ)) ≤
            ∫ x in (1 : ℝ)..1 + K, f x := hanti.sum_le_integral
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + K]] := by
        rw [Set.uIcc_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg K) : (1 : ℝ) ≤ 1 + K)]
        intro hx
        linarith [hx.1]
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)] at htail
      have hfinset : Finset.Icc 1 (K + 1) =
          insert 1 ((Finset.range K).image
            (fun j ↦ (1 + (j + 1) : ℕ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro hn
          by_cases h1 : n = 1
          · exact Or.inl h1
          · right
            refine ⟨n - 2, by omega, by omega⟩
        · intro hn
          rcases hn with h1 | ⟨j, hj, rfl⟩
          · omega
          · omega
      have honeNot : 1 ∉ (Finset.range K).image
          (fun j ↦ (1 + (j + 1) : ℕ)) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, _, hj⟩
        omega
      have hinj : Function.Injective (fun j : ℕ ↦ (1 + (j + 1) : ℕ)) := by
        intro x y hxy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      rw [hfinset, Finset.sum_insert honeNot, Finset.sum_image] 
      · dsimp [f] at htail ⊢
        norm_num at htail ⊢
        calc
          _ ≤ 1 + (((1 + (K : ℝ)) ^ (3 / 4 : ℝ) - 1) /
                (3 / 4 : ℝ)) := by linarith
          _ ≤ (4 / 3 : ℝ) * (1 + (K : ℝ)) ^ (3 / 4 : ℝ) := by
            ring_nf
            norm_num
          _ = (4 / 3 : ℝ) * ((K : ℝ) + 1) ^ (3 / 4 : ℝ) := by
            congr 2
            ring
      · intro x _ y _ hxy
        exact hinj hxy

/-- Source-strength partial sum for DFI (29).  The exponent `ε - 1/4`
integrates to `L^(3/4+ε)` with the exact elementary constant. -/
theorem sum_Icc_natCast_rpow_sub_quarter_le
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 4) (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (ε - 1 / 4) ≤
      (3 / 4 + ε)⁻¹ * (L : ℝ) ^ (3 / 4 + ε) := by
  cases L with
  | zero =>
      have hαpos : 0 < 3 / 4 + ε := by linarith
      simp [Real.zero_rpow hαpos.ne']
  | succ K =>
      let p : ℝ := ε - 1 / 4
      let α : ℝ := 3 / 4 + ε
      have hp : p ≤ 0 := by dsimp [p]; linarith
      have hαpos : 0 < α := by dsimp [α]; linarith
      have hαle : α ≤ 1 := by dsimp [α]; linarith
      have hpα : p + 1 = α := by dsimp [p, α]; ring
      let f : ℝ → ℝ := fun x ↦ x ^ p
      have hanti : AntitoneOn f (Set.Icc 1 (1 + K)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hp).mono
          (fun x hx ↦ lt_of_lt_of_le zero_lt_one hx.1)
      have htail :
          ∑ j ∈ Finset.range K, f (1 + (j + 1 : ℕ)) ≤
            ∫ x in (1 : ℝ)..1 + K, f x := hanti.sum_le_integral
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + K]] := by
        rw [Set.uIcc_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg K) : (1 : ℝ) ≤ 1 + K)]
        intro hx
        linarith [hx.1]
      have hpGt : -1 < p := by dsimp [p]; linarith
      rw [integral_rpow (Or.inl hpGt)] at htail
      have hfinset : Finset.Icc 1 (K + 1) =
          insert 1 ((Finset.range K).image
            (fun j ↦ (1 + (j + 1) : ℕ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro hn
          by_cases h1 : n = 1
          · exact Or.inl h1
          · right
            refine ⟨n - 2, by omega, by omega⟩
        · intro hn
          rcases hn with h1 | ⟨j, hj, rfl⟩
          · omega
          · omega
      have honeNot : 1 ∉ (Finset.range K).image
          (fun j ↦ (1 + (j + 1) : ℕ)) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, _, hj⟩
        omega
      have hinj : Function.Injective (fun j : ℕ ↦ (1 + (j + 1) : ℕ)) := by
        intro x y hxy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      rw [hfinset, Finset.sum_insert honeNot, Finset.sum_image]
      · dsimp [f] at htail ⊢
        norm_num at htail ⊢
        rw [hpα] at htail
        calc
          _ ≤ 1 + (((1 + (K : ℝ)) ^ α - 1) / α) := by
            nlinarith
          _ ≤ α⁻¹ * (1 + (K : ℝ)) ^ α := by
            rw [div_eq_mul_inv]
            field_simp [hαpos.ne']
            nlinarith
          _ = (3 / 4 + ε)⁻¹ * ((K : ℝ) + 1) ^ (3 / 4 + ε) := by
            dsimp [α]
            congr 2
            ring
      · intro x _ y _ hxy
        exact hinj hxy

/-- A complete Kloosterman coefficient may be pulled uniformly through one
absolutely convergent dual Voronoi series. -/
theorem norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    (q r : ℕ) [NeZero q] [NeZero r] (A : ZMod q)
    (frequency : ℕ → ZMod q) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      (Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDual := summable_norm_dfiVoronoiDualTerm r branch g
  have hScaled : Summable (fun n : ℕ =>
      B * ‖dfiVoronoiDualTerm r branch g n‖) := hDual.mul_left B
  have hPoint (n : ℕ) :
      ‖kloostermanSumZMod q A (frequency n) *
          dfiVoronoiDualTerm r branch g n‖ ≤
        B * ‖dfiVoronoiDualTerm r branch g n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q A (frequency n))
      (norm_nonneg _)
  have hSeries : Summable (fun n : ℕ =>
      kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n) := by
    apply Summable.of_norm_bounded hScaled
    exact hPoint
  calc
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      ∑' n : ℕ, ‖kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ :=
      norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' n : ℕ, B * ‖dfiVoronoiDualTerm r branch g n‖ :=
      hSeries.norm.tsum_le_tsum hPoint hScaled
    _ = B * ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
      rw [tsum_mul_left]

/-- A complete Kloosterman coefficient may be pulled uniformly through an
absolutely convergent source-ordered double-frequency series. -/
theorem norm_dfiEquation24DualDualKloosterman_le
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ)
    (hRight : ∀ m, Summable (fun n ↦ ‖amplitude m n‖))
    (hOuter : Summable (fun m ↦ ∑' n, ‖amplitude m n‖)) :
    ‖dfiEquation24DualDualKloosterman
        q a b h xSign ySign amplitude‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hPoint (m n : ℕ) :
      ‖kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n‖ ≤ B * ‖amplitude m n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q (-h : ZMod q) _)
      (norm_nonneg _)
  have hInner (m : ℕ) : Summable (fun n : ℕ ↦
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded ((hRight m).mul_left B)
    exact hPoint m
  have hInnerNorm (m : ℕ) :
      ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ ≤
        B * ∑' n : ℕ, ‖amplitude m n‖ := by
    calc
      _ ≤ ∑' n : ℕ,
          ‖kloostermanSumZMod q (-h : ZMod q)
              (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
                dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
            amplitude m n‖ := norm_tsum_le_tsum_norm (hInner m).norm
      _ ≤ ∑' n : ℕ, B * ‖amplitude m n‖ :=
        (hInner m).norm.tsum_le_tsum (hPoint m) ((hRight m).mul_left B)
      _ = B * ∑' n : ℕ, ‖amplitude m n‖ := by
        rw [tsum_mul_left]
  have hSeries : Summable (fun m : ℕ ↦ ∑' n : ℕ,
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded (hOuter.mul_left B)
    exact hInnerNorm
  unfold dfiEquation24DualDualKloosterman
  calc
    _ ≤ ∑' m : ℕ, ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ := norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' m : ℕ, B * ∑' n : ℕ, ‖amplitude m n‖ :=
      hSeries.norm.tsum_le_tsum hInnerNorm (hOuter.mul_left B)
    _ = B * ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
      rw [tsum_mul_left]

/-- The single transformed `x` branch has exactly the Weil factor times the
absolute dual Voronoi mass. -/
theorem norm_dfiEquation24XDualContribution_le
    (q a : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24XDualContribution q a h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n‖ := by
  rw [dfiEquation24XDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus a q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.xSign
      (dfiLiftedInverseFrequency a q n)) branch g

/-- The symmetric single transformed `y` branch, including the reversed
source character, has the same Weil majorant. -/
theorem norm_dfiEquation24YDualContribution_le
    (q b : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24YDualContribution q b h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n‖ := by
  rw [dfiEquation24YDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus b q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.ySign
      (dfiLiftedInverseFrequency b q n)) branch g

/-- The literal double-dual branch of equation (24) is bounded by the full
Weil factor times the absolutely convergent Mellin-amplitude mass. -/
theorem norm_dfiEquation24ActualDualDualContribution_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ‖dfiEquation24ActualDualDualContribution
        q a b h xBranch yBranch E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            (dfiReducedModulus a q).denominator xBranch
            (dfiReducedModulus b q).denominator yBranch E m n‖ := by
  rw [dfiEquation24ActualDualDualContribution_eq_kloosterman
    hE hA hAB hC hCD hSupport q a b h xBranch yBranch]
  exact norm_dfiEquation24DualDualKloosterman_le
    q a b h xBranch.xSign yBranch.ySign
      (dfiEquation24DoubleDualMellinAmplitude
        (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch E)
    (fun m ↦
      summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
        (E := E) (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch m)
    (summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      (E := E) (dfiReducedModulus a q).denominator xBranch
      (dfiReducedModulus b q).denominator yBranch)

/-- The literal eight non-main terms in DFI equation (24) are bounded by
the two one-sided transformed families and the four double-transformed
families.  This is the source-facing bridge from the exact branch expansion
to the analytic estimates in equations (29) and (30). -/
theorem norm_dfiEquation24ReducedError_le_single_add_double
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24XDualContribution q a h branch
          (fun x ↦ dfiVoronoiMainTerm
            (dfiReducedModulus b q).denominator (E x))‖) +
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24YDualContribution q b h branch
          (fun y ↦ dfiVoronoiMainTerm
            (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
      ∑ yBranch : DFIVoronoiDualBranch,
        ∑ xBranch : DFIVoronoiDualBranch,
          ‖dfiEquation24ActualDualDualContribution
            q a b h xBranch yBranch E‖ := by
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
          if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
            ‖dfiEquation24ReducedBranchContribution
              q a b h xBranch yBranch E‖ :=
      norm_dfiEquation24ReducedError_le q a b h E
    _ = _ := by
      have hBranches : (Finset.univ : Finset DFIVoronoiBranch) =
          {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
            DFIVoronoiBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      have hDualBranches : (Finset.univ : Finset DFIVoronoiDualBranch) =
          {DFIVoronoiDualBranch.minusTerm,
            DFIVoronoiDualBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      rw [hBranches, hDualBranches]
      simp only [Finset.sum_insert, Finset.sum_singleton,
        Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
        or_false, not_false_eq_true, true_and, false_and, ite_true,
        ite_false]
      have hxMinus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.minusTerm E
      have hxPlus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.plusTerm E
      have hyMinus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.minusTerm E hE hA hC hCD hSupport
      have hyPlus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.plusTerm E hE hA hC hCD hSupport
      have hmm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hpm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hmp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.plusTerm E
      have hpp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.plusTerm E
      simp only [DFIVoronoiDualBranch.toBranch] at hxMinus hxPlus hyMinus hyPlus hmm hpm hmp hpp
      rw [hxMinus, hxPlus, hyMinus, hyPlus, hmm, hpm, hmp, hpp]
      ring

/-- Absolute mass of the two `x`-dual/`y`-main terms in DFI (24). -/
noncomputable def dfiEquation24XSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
        (fun x ↦ dfiVoronoiMainTerm
          (dfiReducedModulus b q).denominator (E x)) n‖

/-- Absolute mass of the two `x`-main/`y`-dual terms in DFI (24). -/
noncomputable def dfiEquation24YSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
        (fun y ↦ dfiVoronoiMainTerm
          (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖

/-- Absolute two-variable Mellin mass of the four double-dual terms in
DFI (24). -/
noncomputable def dfiEquation24DoubleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ yBranch : DFIVoronoiDualBranch,
    ∑ xBranch : DFIVoronoiDualBranch,
      ∑' m : ℕ, ∑' n : ℕ,
        ‖dfiEquation24DoubleDualMellinAmplitude
          (dfiReducedModulus a q).denominator xBranch
          (dfiReducedModulus b q).denominator yBranch E m n‖

/-- The complete equation-(24) error is the Weil--Estermann factor times
the sum of the two single-dual masses and the four double-dual masses. -/
theorem norm_dfiEquation24ReducedError_le_weil_mul_masses
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  let K : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hSingle := norm_dfiEquation24ReducedError_le_single_add_double
    hE hA hC hCD hSupport q a b h
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24XDualContribution q a h branch
            (fun x ↦ dfiVoronoiMainTerm
              (dfiReducedModulus b q).denominator (E x))‖) +
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24YDualContribution q b h branch
            (fun y ↦ dfiVoronoiMainTerm
              (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            ‖dfiEquation24ActualDualDualContribution
              q a b h xBranch yBranch E‖ := hSingle
    _ ≤
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x)) n‖) +
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            K * ∑' m : ℕ, ∑' n : ℕ,
              ‖dfiEquation24DoubleDualMellinAmplitude
                (dfiReducedModulus a q).denominator xBranch
                (dfiReducedModulus b q).denominator yBranch E m n‖ := by
      apply add_le_add
      · apply add_le_add
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24XDualContribution_le q a h branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x))
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24YDualContribution_le q b h branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y))
      · apply Finset.sum_le_sum
        intro yBranch _hyBranch
        apply Finset.sum_le_sum
        intro xBranch _hxBranch
        simpa only [K] using
          norm_dfiEquation24ActualDualDualContribution_le
            hE hA hAB hC hCD hSupport q a b h xBranch yBranch
    _ = _ := by
      unfold dfiEquation24XSingleDualMass
        dfiEquation24YSingleDualMass dfiEquation24DoubleDualMass
      dsimp only [K]
      simp_rw [← Finset.mul_sum]
      ring

/-- Source specialization of the complete equation-(24) error bound.  All
smoothness, support, and positive-scale hypotheses are discharged from the
literal equation-(2)/(21)/(23) weight. -/
theorem norm_dfiEquation24_source_error_le_weil_mul_masses
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    let E := dfiEquation23Weight w
      (dfiLocalizedWeight f φ h) a b h q
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  dsimp only
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact norm_dfiEquation24ReducedError_le_weil_mul_masses
    hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport q a b h

/-- A slice obtained after differentiating the second source variable is
still an admissible Voronoi test function in the first variable.  The
support proof uses the full rectangular support, so no projection or
pointwise-support shortcut is hidden in this construction. -/
noncomputable def dfiMixedDerivativeFirstSliceTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) :
    DFIVoronoiTestFunction (fun x ↦ iteratedDeriv j (E x) y) where
  lower := A
  upper := B
  lower_pos := hA
  lower_le_upper := hAB
  smooth := contDiff_iteratedDeriv_slice_right hE j y
  support_subset := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y'
      by_contra hne
      exact hnot (hSupport (show
        (x, y') ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change iteratedDeriv j (E x) y ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp)

@[simp] theorem iteratedDeriv_mixedDerivativeFirstSlice
    {E : ℝ → ℝ → ℂ}
    (i j : ℕ) (x y : ℝ) :
    iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x =
      dfiMixedDeriv i j E x y := by
  rfl

/-- Differentiation in the retained second variable commutes with the
compactly supported Mellin transform in the first variable.  This is the
source-order identity that makes DFI's mixed derivative estimate (28)
apply literally. -/
theorem iteratedDeriv_mellin_transpose
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) (z : ℂ) :
    iteratedDeriv j (fun y' ↦ mellin (fun x ↦ E x y') z) y =
      mellin (fun x ↦ iteratedDeriv j (E x) y) z := by
  let F : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    exact hE.comp (contDiff_snd.prodMk contDiff_fst)
  have hFSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hne : E p.2 p.1 ≠ 0 := by
      simpa [F, Function.mem_support, Function.uncurry_apply_pair] using hp
    have hs : (p.2, p.1) ∈ Function.support (Function.uncurry E) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
    exact ⟨(hSupport hs).2, (hSupport hs).1⟩
  have h := iteratedDeriv_mellin_slice hF hA hFSupport j y z
  simpa only [F, dfiMixedDeriv, Function.uncurry_apply_pair] using h

/-- The explicit one-dimensional Mellin majorant obtained by integrating
by parts `p` times in logarithmic coordinates. -/
noncomputable def dfiMellinProfileMajorant
    (lower upper σ : ℝ) (p : ℕ) (A B : ℝ) : ℝ :=
  let D := max 1 (max upper lower⁻¹)
  (1 + 2 * Real.pi) ^ p *
    ((2 : ℝ) ^ p * ((-Real.log lower) - (-Real.log upper)) *
      (D ^ |σ| * A + D ^ |σ| *
        (A * (|σ| + (p : ℝ) + D * B) ^ p)))

/-- The sign-sensitive physical Mellin majorant on a nonpositive line.
It retains the lower support endpoint to the real power `σ`, which is the
decaying source-scale factor in DFI equation (29). -/
noncomputable def dfiMellinNonposProfileMajorant
    (lower upper σ : ℝ) (p : ℕ) (A B : ℝ) : ℝ :=
  (1 + 2 * Real.pi) ^ p *
    ((2 : ℝ) ^ p * ((-Real.log lower) - (-Real.log upper)) *
      (lower ^ σ * A + lower ^ σ *
        (A * (|σ| + (p : ℝ) + upper * B) ^ p)))

theorem dfiMellinNonposProfileMajorant_mul_amplitude
    (lower upper σ : ℝ) (p j : ℕ) (A B : ℝ) :
    dfiMellinNonposProfileMajorant lower upper σ p (A * B ^ j) B =
      dfiMellinNonposProfileMajorant lower upper σ p A B * B ^ j := by
  simp only [dfiMellinNonposProfileMajorant]
  ring

theorem dfiMellinNonposProfileMajorant_scale_amplitude
    (lower upper σ : ℝ) (p : ℕ) (A B r : ℝ) :
    dfiMellinNonposProfileMajorant lower upper σ p (A * r) B =
      dfiMellinNonposProfileMajorant lower upper σ p A B * r := by
  simp only [dfiMellinNonposProfileMajorant]
  ring

/-- The exact normalized form of the physical Mellin majorant on a dyadic
block `[S,2S]`. -/
noncomputable def dfiMellinDyadicMajorant
    (S σ : ℝ) (p : ℕ) (A B : ℝ) : ℝ :=
  (1 + 2 * Real.pi) ^ p *
    ((2 : ℝ) ^ p * Real.log 2 *
      ((2 * S) ^ |σ| * A + (2 * S) ^ |σ| *
        (A * (|σ| + (p : ℝ) + (2 * S) * B) ^ p)))

/-- The part of the dyadic Mellin majorant independent of the source
amplitude.  Isolating it makes the two successive integrations by parts
in DFI equation (28) multiplicative rather than nested. -/
noncomputable def dfiMellinDyadicFactor
    (S σ : ℝ) (p : ℕ) (B : ℝ) : ℝ :=
  (1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p * Real.log 2 *
    (2 * S) ^ |σ| *
      (1 + (|σ| + (p : ℝ) + (2 * S) * B) ^ p)

theorem dfiMellinDyadicMajorant_eq_factor_mul
    (S σ : ℝ) (p : ℕ) (A B : ℝ) :
    dfiMellinDyadicMajorant S σ p A B =
      dfiMellinDyadicFactor S σ p B * A := by
  simp only [dfiMellinDyadicMajorant, dfiMellinDyadicFactor]
  ring

theorem dfiMellinDyadicMajorant_scale_amplitude
    (S σ : ℝ) (p : ℕ) (A B r : ℝ) :
    dfiMellinDyadicMajorant S σ p (A * r) B =
      dfiMellinDyadicMajorant S σ p A B * r := by
  simp only [dfiMellinDyadicMajorant_eq_factor_mul]
  ring

theorem abs_neg_half_sub_natCast (k : ℕ) :
    |-(1 / 2 : ℝ) - k| = 1 / 2 + k := by
  rw [abs_of_nonpos]
  · ring
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The dyadic Mellin majorant on the left line used in DFI equation
(29), with the absolute value in its exponent evaluated exactly. -/
theorem dfiMellinDyadicMajorant_neg_half_sub_nat
    (S A B : ℝ) (p k : ℕ) :
    dfiMellinDyadicMajorant S (-(1 / 2 : ℝ) - k) p A B =
      (1 + 2 * Real.pi) ^ p *
        ((2 : ℝ) ^ p * Real.log 2 *
          ((2 * S) ^ (1 / 2 + (k : ℝ)) * A +
            (2 * S) ^ (1 / 2 + (k : ℝ)) *
              (A * (1 / 2 + (k : ℝ) + (p : ℝ) +
                (2 * S) * B) ^ p))) := by
  simp only [dfiMellinDyadicMajorant, abs_neg_half_sub_natCast]

/-- On a dyadic source block `[S,2S]` with `S ≥ 1`, the scale hidden in
the physical Mellin profile is exactly `2S`, and its logarithmic width is
exactly `log 2`. -/
theorem dfiMellinProfileMajorant_dyadic_of_one_le
    (S σ A B : ℝ) (p : ℕ) (hS : 1 ≤ S) :
    dfiMellinProfileMajorant S (2 * S) σ p A B =
      (1 + 2 * Real.pi) ^ p *
        ((2 : ℝ) ^ p * Real.log 2 *
          ((2 * S) ^ |σ| * A + (2 * S) ^ |σ| *
            (A * (|σ| + (p : ℝ) + (2 * S) * B) ^ p))) := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hInv : S⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS
  have hOneTwo : (1 : ℝ) ≤ 2 * S := by nlinarith
  have hInvTwo : S⁻¹ ≤ 2 * S := hInv.trans hOneTwo
  have hD : max 1 (max (2 * S) S⁻¹) = 2 * S := by
    rw [max_eq_left hInvTwo, max_eq_right hOneTwo]
  have hLog : (-Real.log S) - (-Real.log (2 * S)) = Real.log 2 := by
    rw [Real.log_mul (by norm_num) hSpos.ne']
    ring
  simp only [dfiMellinProfileMajorant, hD, hLog]

theorem dfiMellinProfileMajorant_eq_dyadicMajorant_of_one_le
    (S σ A B : ℝ) (p : ℕ) (hS : 1 ≤ S) :
    dfiMellinProfileMajorant S (2 * S) σ p A B =
      dfiMellinDyadicMajorant S σ p A B := by
  simpa only [dfiMellinDyadicMajorant] using
    dfiMellinProfileMajorant_dyadic_of_one_le S σ A B p hS

theorem DFIVoronoiTestFunction.mellin_le_profileMajorant
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (σ : ℝ) (p : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDeriv : ∀ j ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv j g x‖ ≤ A * B ^ j) (u : ℝ) :
    (1 + |u|) ^ p *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      dfiMellinProfileMajorant hg.lower hg.upper σ p A B := by
  exact hg.mellin_line_bound_of_physical_profile_order
    σ p hA hB hDeriv u

theorem DFIVoronoiTestFunction.mellin_le_nonposProfileMajorant
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (σ : ℝ) (p : ℕ) (hσ : σ ≤ 0) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDeriv : ∀ j ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv j g x‖ ≤ A * B ^ j) (u : ℝ) :
    (1 + |u|) ^ p *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      dfiMellinNonposProfileMajorant hg.lower hg.upper σ p A B := by
  exact hg.mellin_line_bound_of_physical_profile_order_of_nonpos
    σ p hσ hA hB hDeriv u

theorem dfiMellinProfileMajorant_mul_amplitude
    (lower upper σ : ℝ) (p j : ℕ) (A B : ℝ) :
    dfiMellinProfileMajorant lower upper σ p (A * B ^ j) B =
      dfiMellinProfileMajorant lower upper σ p A B * B ^ j := by
  simp only [dfiMellinProfileMajorant]
  ring

theorem dfiMellinProfileMajorant_scale_amplitude
    (lower upper σ : ℝ) (p : ℕ) (A B r : ℝ) :
    dfiMellinProfileMajorant lower upper σ p (A * r) B =
      dfiMellinProfileMajorant lower upper σ p A B * r := by
  simp only [dfiMellinProfileMajorant]
  ring

/-- Quantitative two-variable Mellin decay obtained by applying the
one-dimensional physical-profile estimate twice after the exact compact
support interchange.  Both frequency weights and every mixed derivative
used in DFI (28) are explicit. -/
theorem dfiBiMellin_line_bound_of_mixed_profile
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (σ τ : ℝ) (p : ℕ) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j))
    (u v : ℝ) :
    (1 + |u|) ^ p * (1 + |v|) ^ p *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((τ : ℂ) + (v : ℂ) * I)‖ ≤
      dfiMellinProfileMajorant C D τ p
        (dfiMellinProfileMajorant A B σ p M R) R := by
  let X : ℝ := dfiMellinProfileMajorant A B σ p M R
  let wu : ℝ := (1 + |u|) ^ p
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hInner (j : ℕ) (hj : j ≤ p) (y : ℝ) :
      wu * ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ X * R ^ j := by
    have hProfile : ∀ i ≤ p, ∀ x : ℝ,
        ‖iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x‖ ≤
          (M * R ^ j) * R ^ i := by
      intro i hi x
      rw [iteratedDeriv_mixedDerivativeFirstSlice]
      calc
        ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) :=
          hDeriv i hi j hj x y
        _ = (M * R ^ j) * R ^ i := by rw [pow_add]; ring
    have hBound :=
      (dfiMixedDerivativeFirstSliceTestFunction hE hA hAB hSupport j y)
        |>.mellin_le_profileMajorant σ p
          (mul_nonneg hM (pow_nonneg hR j)) hR hProfile u
    simpa only [X, wu,
      dfiMellinProfileMajorant_mul_amplitude] using hBound
  have hX : 0 ≤ X := by
    have h0 := hInner 0 (Nat.zero_le p) 0
    have hleft : 0 ≤ wu *
        ‖mellin (fun x ↦ iteratedDeriv 0 (E x) 0)
          ((σ : ℂ) + (u : ℂ) * I)‖ := by positivity
    exact hleft.trans (by simpa using h0)
  let G : ℝ → ℂ := fun y ↦
    mellin (fun x ↦ E x y) ((σ : ℂ) + (u : ℂ) * I)
  have hGDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j G y‖ ≤ (X * wu⁻¹) * R ^ j := by
    intro j hj y
    rw [show iteratedDeriv j G y =
        mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I) by
      exact iteratedDeriv_mellin_transpose hE hA hSupport j y _]
    calc
      ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (X * R ^ j) / wu := by
        apply (le_div_iff₀ hwu).2
        simpa [mul_comm] using hInner j hj y
      _ = (X * wu⁻¹) * R ^ j := by
        rw [div_eq_mul_inv]
        ring
  have hOuter :=
    (dfiMellinTransposeTestFunction hE hA hC hCD hSupport
      ((σ : ℂ) + (u : ℂ) * I))
      |>.mellin_le_profileMajorant τ p
        (mul_nonneg hX (inv_nonneg.mpr hwu.le)) hR hGDeriv v
  change (1 + |v|) ^ p *
      ‖mellin G ((τ : ℂ) + (v : ℂ) * I)‖ ≤
        dfiMellinProfileMajorant C D τ p (X * wu⁻¹) R at hOuter
  have hComm := mellin_mellin_comm_of_rectangular_support
    hE hA hC hSupport
      ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I)
  rw [show dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I) =
        mellin G ((τ : ℂ) + (v : ℂ) * I) by
    exact hComm]
  have hScaled := mul_le_mul_of_nonneg_left hOuter hwu.le
  rw [dfiMellinProfileMajorant_scale_amplitude] at hScaled
  have hCancel : wu *
      (dfiMellinProfileMajorant C D τ p X R * wu⁻¹) =
        dfiMellinProfileMajorant C D τ p X R := by
    field_simp [ne_of_gt hwu]
  rw [hCancel] at hScaled
  simpa only [wu, X, mul_assoc] using hScaled

/-- Two-variable version of the sign-sensitive Mellin estimate on
nonpositive lines.  Both lower support endpoints survive the two Fubini
steps, exactly as required for DFI's simultaneous left shift in (29). -/
theorem dfiBiMellin_line_bound_of_anisotropic_mixed_profile_of_nonpos
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (σ τ : ℝ) (hσ : σ ≤ 0) (hτ : τ ≤ 0) (p : ℕ) {M Rx Ry : ℝ}
    (hM : 0 ≤ M) (hRx : 0 ≤ Rx) (hRy : 0 ≤ Ry)
    (hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * Rx ^ i * Ry ^ j)
    (u v : ℝ) :
    (1 + |u|) ^ p * (1 + |v|) ^ p *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((τ : ℂ) + (v : ℂ) * I)‖ ≤
      dfiMellinNonposProfileMajorant C D τ p
        (dfiMellinNonposProfileMajorant A B σ p M Rx) Ry := by
  let X : ℝ := dfiMellinNonposProfileMajorant A B σ p M Rx
  let wu : ℝ := (1 + |u|) ^ p
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hInner (j : ℕ) (hj : j ≤ p) (y : ℝ) :
      wu * ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ X * Ry ^ j := by
    have hProfile : ∀ i ≤ p, ∀ x : ℝ,
        ‖iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x‖ ≤
          (M * Ry ^ j) * Rx ^ i := by
      intro i hi x
      rw [iteratedDeriv_mixedDerivativeFirstSlice]
      calc
        ‖dfiMixedDeriv i j E x y‖ ≤ M * Rx ^ i * Ry ^ j :=
          hDeriv i hi j hj x y
        _ = (M * Ry ^ j) * Rx ^ i := by ring
    have hBound :=
      (dfiMixedDerivativeFirstSliceTestFunction hE hA hAB hSupport j y)
        |>.mellin_le_nonposProfileMajorant σ p hσ
          (mul_nonneg hM (pow_nonneg hRy j)) hRx hProfile u
    simpa only [X, wu,
      dfiMellinNonposProfileMajorant_scale_amplitude] using hBound
  have hX : 0 ≤ X := by
    have h0 := hInner 0 (Nat.zero_le p) 0
    have hleft : 0 ≤ wu *
        ‖mellin (fun x ↦ iteratedDeriv 0 (E x) 0)
          ((σ : ℂ) + (u : ℂ) * I)‖ := by positivity
    exact hleft.trans (by simpa using h0)
  let G : ℝ → ℂ := fun y ↦
    mellin (fun x ↦ E x y) ((σ : ℂ) + (u : ℂ) * I)
  have hGDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j G y‖ ≤ (X * wu⁻¹) * Ry ^ j := by
    intro j hj y
    rw [show iteratedDeriv j G y =
        mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I) by
      exact iteratedDeriv_mellin_transpose hE hA hSupport j y _]
    calc
      ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (X * Ry ^ j) / wu := by
        apply (le_div_iff₀ hwu).2
        simpa [mul_comm] using hInner j hj y
      _ = (X * wu⁻¹) * Ry ^ j := by
        rw [div_eq_mul_inv]
        ring
  have hOuter :=
    (dfiMellinTransposeTestFunction hE hA hC hCD hSupport
      ((σ : ℂ) + (u : ℂ) * I))
      |>.mellin_le_nonposProfileMajorant τ p hτ
        (mul_nonneg hX (inv_nonneg.mpr hwu.le)) hRy hGDeriv v
  change (1 + |v|) ^ p *
      ‖mellin G ((τ : ℂ) + (v : ℂ) * I)‖ ≤
        dfiMellinNonposProfileMajorant C D τ p (X * wu⁻¹) Ry at hOuter
  have hComm := mellin_mellin_comm_of_rectangular_support
    hE hA hC hSupport
      ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I)
  rw [show dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I) =
        mellin G ((τ : ℂ) + (v : ℂ) * I) by
    exact hComm]
  have hScaled := mul_le_mul_of_nonneg_left hOuter hwu.le
  rw [dfiMellinNonposProfileMajorant_scale_amplitude] at hScaled
  have hCancel : wu *
      (dfiMellinNonposProfileMajorant C D τ p X Ry * wu⁻¹) =
        dfiMellinNonposProfileMajorant C D τ p X Ry := by
    field_simp [ne_of_gt hwu]
  rw [hCancel] at hScaled
  simpa only [wu, X, mul_assoc] using hScaled

/-- Isotropic specialization retained for existing consumers. -/
theorem dfiBiMellin_line_bound_of_mixed_profile_of_nonpos
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (σ τ : ℝ) (hσ : σ ≤ 0) (hτ : τ ≤ 0) (p : ℕ) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j))
    (u v : ℝ) :
    (1 + |u|) ^ p * (1 + |v|) ^ p *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((τ : ℂ) + (v : ℂ) * I)‖ ≤
      dfiMellinNonposProfileMajorant C D τ p
        (dfiMellinNonposProfileMajorant A B σ p M R) R := by
  apply dfiBiMellin_line_bound_of_anisotropic_mixed_profile_of_nonpos
    hE hA hAB hC hCD hSupport σ τ hσ hτ p hM hR hR
  intro i hi j hj x y
  calc
    ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) :=
      hDeriv i hi j hj x y
    _ = M * R ^ i * R ^ j := by rw [pow_add]; ring

/-- Source-uniform two-variable Mellin estimate for the literal
equation-(23) weight.  The constants are selected before the arithmetic
parameters and every mixed derivative is supplied by DFI equation (28). -/
theorem exists_dfiEquation28_biMellin_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ τ : ℝ) (p : ℕ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u v : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j
        let qQ := (q : ℝ) * Q
        let M := Csum * qQ⁻¹
        let R := ((a : ℝ) * (b : ℝ)) / qQ
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (1 + |u|) ^ p * (1 + |v|) ^ p *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((τ : ℂ) + (v : ℂ) * I)‖ ≤
          dfiMellinProfileMajorant (Y / b) (2 * Y / b) τ p
            (dfiMellinProfileMajorant (X / a) (2 * X / a)
              σ p M R) R := by
  choose K hK hBound using fun i j ↦
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i j
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h u v
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ : ℝ := (q : ℝ) * Q
  let M : ℝ := Csum * qQ⁻¹
  let R : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    have hinner : ∀ i ∈ Finset.range (p + 1),
        0 < ∑ j ∈ Finset.range (p + 1), K i j := by
      intro i _hi
      exact Finset.sum_pos (fun j _hj ↦ hK i j) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) := by
    intro i hi j hj x y
    have hiMem : i ∈ Finset.range (p + 1) := by simp [hi]
    have hjMem : j ∈ Finset.range (p + 1) := by simp [hj]
    have hKle : K i j ≤ Csum := by
      dsimp [Csum]
      exact (Finset.single_le_sum (fun t _ ↦ (hK i t).le) hjMem).trans
        (Finset.single_le_sum
          (fun t _ ↦ Finset.sum_nonneg (fun s _ ↦ (hK t s).le)) hiMem)
    calc
      ‖dfiMixedDeriv i j E x y‖ ≤
          K i j * qQ⁻¹ * R ^ (i + j) := by
        simpa only [E, qQ, R] using
          hBound i j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * R ^ (i + j) := by gcongr
      _ = M * R ^ (i + j) := rfl
  simpa only [E, M, R, Csum, qQ] using
    dfiBiMellin_line_bound_of_mixed_profile hE hXA hXAB hYC hYCD
      hSupport σ τ p hM hR hDeriv u v

/-- Equation (28) with the source-scale decay retained on two nonpositive
vertical lines.  This is the quantitative input for the discarded modes in
DFI equation (29). -/
theorem exists_dfiEquation28_biMellin_nonpos_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ τ : ℝ) (hσ : σ ≤ 0) (hτ : τ ≤ 0) (p : ℕ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u v : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j
        let qQ := (q : ℝ) * Q
        let M := Csum * qQ⁻¹
        let R := ((a : ℝ) * (b : ℝ)) / qQ
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (1 + |u|) ^ p * (1 + |v|) ^ p *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((τ : ℂ) + (v : ℂ) * I)‖ ≤
          dfiMellinNonposProfileMajorant (Y / b) (2 * Y / b) τ p
            (dfiMellinNonposProfileMajorant (X / a) (2 * X / a)
              σ p M R) R := by
  choose K hK hBound using fun i j ↦
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i j
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h u v
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ : ℝ := (q : ℝ) * Q
  let M : ℝ := Csum * qQ⁻¹
  let R : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    have hinner : ∀ i ∈ Finset.range (p + 1),
        0 < ∑ j ∈ Finset.range (p + 1), K i j := by
      intro i _hi
      exact Finset.sum_pos (fun j _hj ↦ hK i j) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) := by
    intro i hi j hj x y
    have hiMem : i ∈ Finset.range (p + 1) := by simp [hi]
    have hjMem : j ∈ Finset.range (p + 1) := by simp [hj]
    have hKle : K i j ≤ Csum := by
      dsimp [Csum]
      exact (Finset.single_le_sum (fun t _ ↦ (hK i t).le) hjMem).trans
        (Finset.single_le_sum
          (fun t _ ↦ Finset.sum_nonneg (fun s _ ↦ (hK t s).le)) hiMem)
    calc
      ‖dfiMixedDeriv i j E x y‖ ≤
          K i j * qQ⁻¹ * R ^ (i + j) := by
        simpa only [E, qQ, R] using
          hBound i j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * R ^ (i + j) := by gcongr
      _ = M * R ^ (i + j) := rfl
  simpa only [E, M, R, Csum, qQ] using
    dfiBiMellin_line_bound_of_mixed_profile_of_nonpos
      hE hXA hXAB hYC hYCD hSupport σ τ hσ hτ p hM hR hDeriv u v

/-- Equation (28) on two nonpositive lines with its two physical derivative
scales retained separately.  This is the quantitative form needed for the
two-frequency complement in equation (29). -/
theorem exists_dfiEquation28_biMellin_nonpos_separated_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ τ : ℝ) (hσ : σ ≤ 0) (hτ : τ ≤ 0) (p : ℕ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u v : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j
        let qQ := (q : ℝ) * Q
        let M := Csum * qQ⁻¹
        let Rx := (a : ℝ) / qQ
        let Ry := (b : ℝ) / qQ
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (1 + |u|) ^ p * (1 + |v|) ^ p *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((τ : ℂ) + (v : ℂ) * I)‖ ≤
          dfiMellinNonposProfileMajorant (Y / b) (2 * Y / b) τ p
            (dfiMellinNonposProfileMajorant (X / a) (2 * X / a)
              σ p M Rx) Ry := by
  choose K hK hBound using fun i j ↦
    dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ i j
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h u v
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ : ℝ := (q : ℝ) * Q
  let M : ℝ := Csum * qQ⁻¹
  let Rx : ℝ := (a : ℝ) / qQ
  let Ry : ℝ := (b : ℝ) / qQ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    have hinner : ∀ i ∈ Finset.range (p + 1),
        0 < ∑ j ∈ Finset.range (p + 1), K i j := by
      intro i _hi
      exact Finset.sum_pos (fun j _hj ↦ hK i j) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hRx : 0 ≤ Rx := by dsimp [Rx]; positivity
  have hRy : 0 ≤ Ry := by dsimp [Ry]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * Rx ^ i * Ry ^ j := by
    intro i hi j hj x y
    have hiMem : i ∈ Finset.range (p + 1) := by simp [hi]
    have hjMem : j ∈ Finset.range (p + 1) := by simp [hj]
    have hKle : K i j ≤ Csum := by
      dsimp [Csum]
      exact (Finset.single_le_sum (fun t _ ↦ (hK i t).le) hjMem).trans
        (Finset.single_le_sum
          (fun t _ ↦ Finset.sum_nonneg (fun s _ ↦ (hK t s).le)) hiMem)
    calc
      ‖dfiMixedDeriv i j E x y‖ ≤
          K i j * qQ⁻¹ * Rx ^ i * Ry ^ j := by
        simpa only [E, qQ, Rx, Ry] using
          hBound i j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * Rx ^ i * Ry ^ j := by gcongr
      _ = M * Rx ^ i * Ry ^ j := rfl
  simpa only [E, M, Rx, Ry, Csum, qQ] using
    dfiBiMellin_line_bound_of_anisotropic_mixed_profile_of_nonpos
      hE hXA hXAB hYC hYCD hSupport σ τ hσ hτ p hM hRx hRy hDeriv u v

/-- Profile-explicit two-line equation-(28) estimate. -/
theorem exists_dfiEquation28_biMellin_nonpos_separated_line_bound_order_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (σ τ : ℝ) (hσ : σ ≤ 0) (hτ : τ ≤ 0) (p : ℕ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u v : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j
        let qQ := (q : ℝ) * Q
        let M := Csum * qQ⁻¹
        let Rx := (a : ℝ) / qQ
        let Ry := (b : ℝ) / qQ
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (1 + |u|) ^ p * (1 + |v|) ^ p *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((τ : ℂ) + (v : ℂ) * I)‖ ≤
          dfiMellinNonposProfileMajorant (Y / b) (2 * Y / b) τ p
            (dfiMellinNonposProfileMajorant (X / a) (2 * X / a)
              σ p M Rx) Ry := by
  choose K hK hBound using fun i j ↦
    dfiEquation28_separated_uniform_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ i j
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h u v
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ : ℝ := (q : ℝ) * Q
  let M : ℝ := Csum * qQ⁻¹
  let Rx : ℝ := (a : ℝ) / qQ
  let Ry : ℝ := (b : ℝ) / qQ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    have hinner : ∀ i ∈ Finset.range (p + 1),
        0 < ∑ j ∈ Finset.range (p + 1), K i j := by
      intro i _hi
      exact Finset.sum_pos (fun j _hj ↦ hK i j) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hRx : 0 ≤ Rx := by dsimp [Rx]; positivity
  have hRy : 0 ≤ Ry := by dsimp [Ry]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * Rx ^ i * Ry ^ j := by
    intro i hi j hj x y
    have hiMem : i ∈ Finset.range (p + 1) := by simp [hi]
    have hjMem : j ∈ Finset.range (p + 1) := by simp [hj]
    have hKle : K i j ≤ Csum := by
      dsimp [Csum]
      exact (Finset.single_le_sum (fun t _ ↦ (hK i t).le) hjMem).trans
        (Finset.single_le_sum
          (fun t _ ↦ Finset.sum_nonneg (fun s _ ↦ (hK t s).le)) hiMem)
    calc
      ‖dfiMixedDeriv i j E x y‖ ≤
          K i j * qQ⁻¹ * Rx ^ i * Ry ^ j := by
        simpa only [E, qQ, Rx, Ry] using
          hBound i j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * Rx ^ i * Ry ^ j := by gcongr
      _ = M * Rx ^ i * Ry ^ j := rfl
  simpa only [E, M, Rx, Ry, Csum, qQ] using
    dfiBiMellin_line_bound_of_anisotropic_mixed_profile_of_nonpos
      hE hXA hXAB hYC hYCD hSupport σ τ hσ hτ p hM hRx hRy hDeriv u v

/-- Two quadratically growing vertical multipliers consume four of six
powers of Mellin decay in each frequency, leaving an integrable Cauchy
kernel in both variables. -/
theorem two_frequency_quadratic_decay
    {a b c Cx Cy M u v : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hA : a ≤ Cx * (1 + |u|) ^ 2)
    (hB : b ≤ Cy * (1 + |v|) ^ 2)
    (hC : (1 + |u|) ^ 6 * (1 + |v|) ^ 6 * c ≤ M) :
    a * b * c ≤
      Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
  let wu : ℝ := 1 + |u|
  let wv : ℝ := 1 + |v|
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hwv : 0 < wv := by dsimp [wv]; positivity
  have hc' : c ≤ M / (wu ^ 6 * wv ^ 6) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hwu 6) (pow_pos hwv 6))).2
    simpa only [wu, wv, mul_comm, mul_left_comm, mul_assoc] using hC
  have huDen : 0 < 1 + u ^ 2 := by positivity
  have hvDen : 0 < 1 + v ^ 2 := by positivity
  have huPow : 1 + u ^ 2 ≤ wu ^ 4 := by
    dsimp [wu]
    nlinarith [abs_nonneg u, sq_abs u]
  have hvPow : 1 + v ^ 2 ≤ wv ^ 4 := by
    dsimp [wv]
    nlinarith [abs_nonneg v, sq_abs v]
  have huInv : (wu ^ 4)⁻¹ ≤ (1 + u ^ 2)⁻¹ :=
    inv_anti₀ huDen huPow
  have hvInv : (wv ^ 4)⁻¹ ≤ (1 + v ^ 2)⁻¹ :=
    inv_anti₀ hvDen hvPow
  calc
    a * b * c ≤
        (Cx * wu ^ 2) * (Cy * wv ^ 2) *
          (M / (wu ^ 6 * wv ^ 6)) := by gcongr
    _ = Cx * Cy * M * (wu ^ 4)⁻¹ * (wv ^ 4)⁻¹ := by
      field_simp [ne_of_gt hwu, ne_of_gt hwv]
    _ ≤ Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
      gcongr

/-- The fixed two-dimensional Cauchy mass left after the two DFI
archimedean multipliers are absorbed. -/
noncomputable def dfiCauchyPlaneMass : ℝ :=
  ∫ p : ℝ × ℝ, (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹

theorem integrable_dfiCauchyPlaneKernel :
    Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) := by
  exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

theorem dfiCauchyPlaneMass_nonneg : 0 ≤ dfiCauchyPlaneMass := by
  exact integral_nonneg fun _ ↦ mul_nonneg (inv_nonneg.mpr (by positivity))
    (inv_nonneg.mpr (by positivity))

/-- The common archimedean integral of a literal double-dual branch is
bounded by the equation-(28) bivariate Mellin majorant. -/
theorem integral_norm_dfiDualBranchMultipliers_mul_biMellin_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (M : ℝ) (hM : 0 ≤ M)
    (hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    (∫ p : ℝ × ℝ,
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖) ≤
      (32 * qx * dfiArchimedeanScale qx ^ 2) *
        (32 * qy * dfiArchimedeanScale qy ^ 2) * M *
          dfiCauchyPlaneMass := by
  let Cx : ℝ := 32 * qx * dfiArchimedeanScale qx ^ 2
  let Cy : ℝ := 32 * qy * dfiArchimedeanScale qy ^ 2
  have hCx : 0 ≤ Cx := by dsimp [Cx]; positivity
  have hCy : 0 ≤ Cy := by dsimp [Cy]; positivity
  have hMajor : Integrable (fun p : ℝ × ℝ ↦
      Cx * Cy * M * ((1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹)) := by
    exact integrable_dfiCauchyPlaneKernel.const_mul (Cx * Cy * M)
  have hInt : Integrable (fun p : ℝ × ℝ ↦
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖) := by
    exact (integrable_dfiDualBranchMultipliers_mul_biMellin
      hE hA hAB hC hCD hSupport qx qy xBranch yBranch).norm
  calc
    _ ≤ ∫ p : ℝ × ℝ,
        Cx * Cy * M * ((1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) := by
      apply integral_mono hInt hMajor
      intro p
      simpa only [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), Cx, Cy, mul_assoc] using
        two_frequency_quadratic_decay
          (norm_nonneg (dfiDualBranchMultiplier qy yBranch
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))
          (norm_nonneg (dfiBiMellin E
            (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))
          hCx hCy hM
          (norm_dfiDualBranchMultiplier_le qx xBranch p.1)
          (norm_dfiDualBranchMultiplier_le qy yBranch p.2)
          (hBi p.1 p.2)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem summable_norm_divisorWeight_LSeriesTerm_threeHalf :
    Summable (fun n : ℕ ↦
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖) := by
  have h := periodicDivisorCoeff_LSeriesSummable
    1 (fun _ : ZMod 1 ↦ (1 : ℂ)) (s := (3 / 2 : ℂ)) (by norm_num)
  have hEq : periodicDivisorCoeff 1 (fun _ : ZMod 1 ↦ (1 : ℂ)) =
      divisorWeight := by
    funext n
    simp [periodicDivisorCoeff, divisorWeight]
  rw [hEq] at h
  exact summable_norm_iff.mpr h

/-- The absolute Dirichlet mass of the ordinary divisor coefficients on
the DFI line `Re s = 3/2`. -/
noncomputable def dfiDivisorThreeHalfMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖

theorem dfiDivisorThreeHalfMass_nonneg : 0 ≤ dfiDivisorThreeHalfMass :=
  tsum_nonneg fun _ ↦ norm_nonneg _

/-- Exact coefficient/archimedean factorization for the
residue-independent double-dual amplitude integrand. -/
theorem integral_norm_dfiEquation24DoubleDualAmplitudeIntegrand_eq
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (m n : ℕ) :
    (∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p‖) =
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  have hx : periodicDivisorCoeff qx (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have hy : periodicDivisorCoeff qy (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have h := integral_norm_dfiEquation24DoubleMellinTerm
    (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m n
  rw [hx, hy] at h
  simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand] using h

/-- The complete absolute `(m,n)` mass of one double-dual branch factors
through the fixed divisor mass and its common archimedean integral. -/
theorem tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch) :
    (∑' m : ℕ, ∑' n : ℕ,
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) ≤
      ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
        dfiDivisorThreeHalfMass ^ 2 *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  let K : ℝ := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖
  let J : ℝ := ∫ p : ℝ × ℝ,
    ‖dfiDualBranchMultiplier qx xBranch
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
      dfiDualBranchMultiplier qy yBranch
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
      dfiBiMellin E
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖
  have hAmpOuter :=
    summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      (E := E) qx xBranch qy yBranch
  have hCoeff := summable_norm_divisorWeight_LSeriesTerm_threeHalf
  have hCoeffScaled (m : ℕ) : Summable (fun n : ℕ ↦
      K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J)) := by
    exact ((hCoeff.mul_left
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖).mul_right J).mul_left K
  have hInner (m : ℕ) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
        K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    calc
      _ ≤ ∑' n : ℕ,
          K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
            ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J) :=
        hAmp.tsum_le_tsum (fun n ↦ by
          calc
            ‖dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m n‖ ≤
                K * ∫ p : ℝ × ℝ,
                  ‖dfiEquation24DoubleDualAmplitudeIntegrand
                    qx xBranch qy yBranch E m n p‖ := by
              exact norm_dfiEquation24DoubleDualMellinAmplitude_le
                qx xBranch qy yBranch E m n
            _ = K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
                ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J) := by
              rw [integral_norm_dfiEquation24DoubleDualAmplitudeIntegrand_eq])
          (hCoeffScaled m)
      _ = K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) := by
        rw [show (fun n : ℕ ↦
            K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
              ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J)) =
            fun n : ℕ ↦
              (K * ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ * J) *
                ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ by
          funext n; ring,
          tsum_mul_left]
        dsimp [dfiDivisorThreeHalfMass]
        ring
  have hOuterMajor : Summable (fun m : ℕ ↦
      K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        dfiDivisorThreeHalfMass * J)) := by
    convert ((hCoeff.mul_right (dfiDivisorThreeHalfMass * J)).mul_left K) using 1
    funext m
    ring
  calc
    _ ≤ ∑' m : ℕ,
        K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) :=
      hAmpOuter.tsum_le_tsum hInner hOuterMajor
    _ = K * dfiDivisorThreeHalfMass ^ 2 * J := by
      rw [show (fun m : ℕ ↦
          K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
            dfiDivisorThreeHalfMass * J)) =
          fun m : ℕ ↦
            K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
              (dfiDivisorThreeHalfMass * J)) by
        funext m; ring,
        tsum_mul_left, tsum_mul_right]
      dsimp [K, J, dfiDivisorThreeHalfMass]
      ring
    _ = _ := rfl

/-- One complete double-dual Voronoi branch is bounded by the fixed divisor
mass, the two archimedean scales, and the bivariate Mellin majorant.  This is
the absolute-convergence step needed before the four signs are recombined in
DFI equation (24). -/
theorem tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (M : ℝ) (hM : 0 ≤ M)
    (hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    (∑' m : ℕ, ∑' n : ℕ,
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) ≤
      ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
        dfiDivisorThreeHalfMass ^ 2 *
        ((32 * qx * dfiArchimedeanScale qx ^ 2) *
          (32 * qy * dfiArchimedeanScale qy ^ 2) * M *
          dfiCauchyPlaneMass) := by
  refine (tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le
    qx xBranch qy yBranch).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact integral_norm_dfiDualBranchMultipliers_mul_biMellin_le
      hE hA hAB hC hCD hSupport qx qy xBranch yBranch M hM hBi
  · positivity

/-- The dual Voronoi series has no zero-frequency term; DFI's transformed
sums begin at frequency one. -/
@[simp] theorem dfiVoronoiDualTerm_zero
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    dfiVoronoiDualTerm q branch g 0 = 0 := by
  cases branch <;>
    simp [dfiVoronoiDualTerm, divisorWeight]

/-- Every fixed dual frequency vanishes on the zero test function. -/
@[simp] theorem dfiVoronoiDualTerm_zero_function
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (n : ℕ) :
    dfiVoronoiDualTerm q branch (fun _ ↦ 0) n = 0 := by
  cases branch <;>
    simp [dfiVoronoiDualTerm, dfiVoronoiMinusTransform,
      dfiVoronoiPlusTransform, VerticalIntegral', VerticalIntegral, mellin]

/-- For a smooth compactly supported two-variable weight, each fixed
nonzero Voronoi frequency in the second variable remains a smooth compactly
supported test function of the first variable.  This regularity permits the
second physical Bessel transform to be applied without passing through the
already summed dual branch. -/
noncomputable def dfiVoronoiDualTerm_family_testFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (n : ℕ) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) := by
  by_cases hn : n = 0
  · subst n
    refine {
      lower := A
      upper := B
      lower_pos := hA
      lower_le_upper := hAB
      smooth := ?_
      support_subset := ?_ }
    · simpa only [dfiVoronoiDualTerm_zero] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : ℂ)))
    · intro x hx
      exfalso
      change dfiVoronoiDualTerm q branch (E x) 0 ≠ 0 at hx
      rw [dfiVoronoiDualTerm_zero] at hx
      exact hx rfl
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let P : ℝ → ℂ := fun u ↦
    (n : ℂ) ^ (-(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))))
  let W : ℝ → ℂ := fun u ↦ divisorWeight n * P u *
    dfiDualBranchMultiplier q branch
      (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
  let Cw : ℝ := ‖divisorWeight n‖ *
    (32 * q * dfiArchimedeanScale q ^ 2)
  have hPcont : Continuous P := by
    have hExponent : Continuous (fun u : ℝ ↦
        -(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)))) := by
      fun_prop
    exact hExponent.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hPnorm (u : ℝ) : ‖P u‖ ≤ 1 := by
    dsimp [P]
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    · norm_num
  have hWcont : Continuous W := by
    apply (continuous_const.mul hPcont).mul
    simpa only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using
      (continuous_dfiDualBranchMultiplier_leftLine q branch)
  have hCw : 0 ≤ Cw := by
    dsimp [Cw]
    positivity
  have hWbound (u : ℝ) : ‖W u‖ ≤ Cw * (1 + |u|) ^ 2 := by
    dsimp [W, Cw]
    rw [norm_mul, norm_mul]
    calc
      ‖divisorWeight n‖ * ‖P u‖ *
          ‖dfiDualBranchMultiplier q branch
            (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))‖ ≤
          ‖divisorWeight n‖ * 1 *
            (32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2) := by
        gcongr
        · exact hPnorm u
        · simpa only [Complex.ofReal_neg, Complex.ofReal_div,
            Complex.ofReal_one] using
            (norm_dfiDualBranchMultiplier_le q branch u)
      _ = (‖divisorWeight n‖ *
          (32 * q * dfiArchimedeanScale q ^ 2)) * (1 + |u|) ^ 2 := by
        ring
  have hVerticalSmooth : ContDiff ℝ ∞
      (dfiParametricVerticalIntegralDeriv 0 W (-(1 / 2 : ℝ)) E) :=
    contDiff_dfiParametricVerticalIntegral hE hC hCD hSupport
      hWcont hCw hWbound _
  have hEq :
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) =
        fun x ↦ (1 / (2 * Real.pi * I) : ℂ) *
          (I * dfiParametricVerticalIntegralDeriv 0 W
            (-(1 / 2 : ℝ)) E x) := by
    funext x
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    unfold dfiEquation29TransformAt VerticalIntegral' VerticalIntegral
      dfiEquation29Integrand dfiEquation29Multiplier
      dfiParametricVerticalIntegralDeriv W P
    simp only [smul_eq_mul, iteratedDeriv_zero]
    cases branch <;>
      simp only [dfiDualBranchMultiplier,
        Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] <;>
      simp_rw [← MeasureTheory.integral_const_mul] <;>
      apply MeasureTheory.integral_congr_ae <;>
      filter_upwards with u <;>
      ring
  refine {
    lower := A
    upper := B
    lower_pos := hA
    lower_le_upper := hAB
    smooth := ?_
    support_subset := ?_ }
  · rw [hEq]
    exact contDiff_const.mul (contDiff_const.mul hVerticalSmooth)
  · intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm q branch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl

set_option maxHeartbeats 1000000 in
/-- Differentiation in the untransformed parameter commutes exactly with a
fixed-frequency dual Voronoi transform in the second variable.  This is the
physical two-stage bridge needed to apply the equation-(29) Bessel recurrence
twice while retaining a mixed `L¹` derivative profile. -/
theorem iteratedDeriv_dfiVoronoiDualTerm_family
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (n i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun x' ↦ dfiVoronoiDualTerm q branch (E x') n) x =
      dfiVoronoiDualTerm q branch (fun y ↦ dfiMixedDeriv i 0 E x y) n := by
  by_cases hn : n = 0
  · subst n
    simp only [dfiVoronoiDualTerm_zero]
    simp
  let P : ℝ → ℂ := fun u ↦
    (n : ℂ) ^ (-(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))))
  let W : ℝ → ℂ := fun u ↦ divisorWeight n * P u *
    dfiDualBranchMultiplier q branch
      (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
  let Cw : ℝ := ‖divisorWeight n‖ *
    (32 * q * dfiArchimedeanScale q ^ 2)
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hPcont : Continuous P := by
    have hExponent : Continuous (fun u : ℝ ↦
        -(1 - (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)))) := by
      fun_prop
    exact hExponent.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hPnorm (u : ℝ) : ‖P u‖ ≤ 1 := by
    dsimp [P]
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    · norm_num
  have hWcont : Continuous W := by
    apply (continuous_const.mul hPcont).mul
    simpa only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using
      (continuous_dfiDualBranchMultiplier_leftLine q branch)
  have hCw : 0 ≤ Cw := by
    dsimp [Cw]
    positivity
  have hWbound (u : ℝ) : ‖W u‖ ≤ Cw * (1 + |u|) ^ 2 := by
    dsimp [W, Cw]
    rw [norm_mul, norm_mul]
    calc
      ‖divisorWeight n‖ * ‖P u‖ *
          ‖dfiDualBranchMultiplier q branch
            (((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))‖ ≤
          ‖divisorWeight n‖ * 1 *
            (32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2) := by
        gcongr
        · exact hPnorm u
        · simpa only [Complex.ofReal_neg, Complex.ofReal_div,
            Complex.ofReal_one] using
            (norm_dfiDualBranchMultiplier_le q branch u)
      _ = (‖divisorWeight n‖ *
          (32 * q * dfiArchimedeanScale q ^ 2)) * (1 + |u|) ^ 2 := by
        ring
  let V : ℕ → ℝ → ℂ := fun r ↦
    dfiParametricVerticalIntegralDeriv r W (-(1 / 2 : ℝ)) E
  have hVsmooth : ContDiff ℝ ∞ (V 0) := by
    simpa only [V] using contDiff_dfiParametricVerticalIntegral
      hE hC hCD hSupport hWcont hCw hWbound (-(1 / 2 : ℝ))
  have hViter : iteratedDeriv i (V 0) = V i := by
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [iteratedDeriv_succ, ih]
        funext x'
        simpa only [V, Nat.succ_eq_add_one] using
          (hasDerivAt_dfiParametricVerticalIntegralDeriv
            hE hC hCD hSupport hWcont hCw hWbound
              i (-(1 / 2 : ℝ)) x').deriv
  have hFamilyEq :
      (fun x' ↦ dfiVoronoiDualTerm q branch (E x') n) =
        fun x' ↦ (1 / (2 * Real.pi * I) : ℂ) * (I * V 0 x') := by
    funext x'
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    dsimp only [V]
    unfold dfiEquation29TransformAt VerticalIntegral' VerticalIntegral
      dfiEquation29Integrand dfiEquation29Multiplier
      dfiParametricVerticalIntegralDeriv W P
    simp only [smul_eq_mul, iteratedDeriv_zero]
    cases branch <;>
      simp only [dfiDualBranchMultiplier,
        Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] <;>
      simp_rw [← MeasureTheory.integral_const_mul] <;>
      apply MeasureTheory.integral_congr_ae <;>
      filter_upwards with u <;>
      ring
  have hMixedEq :
      dfiVoronoiDualTerm q branch
          (fun y ↦ dfiMixedDeriv i 0 E x y) n =
        (1 / (2 * Real.pi * I) : ℂ) * (I * V i x) := by
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    dsimp only [V]
    unfold dfiEquation29TransformAt VerticalIntegral' VerticalIntegral
      dfiEquation29Integrand dfiEquation29Multiplier
      dfiParametricVerticalIntegralDeriv W P
    simp only [smul_eq_mul]
    simp_rw [iteratedDeriv_mellin_slice hE hC hSupport i x]
    cases branch <;>
      simp only [dfiDualBranchMultiplier,
        Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] <;>
      simp_rw [← MeasureTheory.integral_const_mul] <;>
      apply MeasureTheory.integral_congr_ae <;>
      filter_upwards with u <;>
      ring
  rw [hFamilyEq]
  have hInnerSmooth : ContDiff ℝ ∞ (fun x' ↦ I * V 0 x') :=
    contDiff_const.mul hVsmooth
  rw [iteratedDeriv_const_mul (1 / (2 * Real.pi * I) : ℂ)
    (hInnerSmooth.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [iteratedDeriv_const_mul I
    (hVsmooth.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [hViter]
  exact hMixedEq.symm

/-- One `x`- and one `y`-directional derivative commute for a smooth
two-variable function.  The proof invokes the symmetry of the full second
Fréchet derivative rather than treating mixed partial commutation as a
definitional simplification. -/
theorem dfiPartialY_one_dfiPartialX_one_comm
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    dfiPartialY 1 (dfiPartialX 1 g) p =
      dfiPartialX 1 (dfiPartialY 1 g) p := by
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  have hTwoInf : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr le_top
  have hfg : DifferentiableAt ℝ (fderiv ℝ g) p :=
    ((hg.fderiv_right (m := 1) (by simpa using hTwoInf)).differentiable
      one_ne_zero) p
  have hex : DifferentiableAt ℝ (fun _ : ℝ × ℝ ↦ ex) p :=
    differentiableAt_const ex
  have hey : DifferentiableAt ℝ (fun _ : ℝ × ℝ ↦ ey) p :=
    differentiableAt_const ey
  change fderiv ℝ (fun z ↦ fderiv ℝ g z ex) p ey =
    fderiv ℝ (fun z ↦ fderiv ℝ g z ey) p ex
  rw [fderiv_clm_apply hfg hex, fderiv_clm_apply hfg hey]
  simpa using
    (hg.contDiffAt.isSymmSndFDerivAt (by simpa using hTwoInf)).eq ey ex

/-- Any number of `y` derivatives commutes past one `x` derivative. -/
theorem dfiPartialY_dfiPartialX_one_comm
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    dfiPartialY j (dfiPartialX 1 g) =
      dfiPartialX 1 (dfiPartialY j g) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show dfiPartialY (j + 1) (dfiPartialX 1 g) =
          dfiPartialY 1 (dfiPartialY j (dfiPartialX 1 g)) by rfl]
      rw [ih]
      funext p
      exact dfiPartialY_one_dfiPartialX_one_comm
        (contDiff_dfiPartialY j hg) p

/-- Arbitrary smooth coordinate derivatives commute. -/
theorem dfiPartialY_dfiPartialX_comm
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (i j : ℕ) :
    dfiPartialY j (dfiPartialX i g) =
      dfiPartialX i (dfiPartialY j g) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show dfiPartialX (i + 1) g =
          dfiPartialX 1 (dfiPartialX i g) by rfl]
      rw [dfiPartialY_dfiPartialX_one_comm (contDiff_dfiPartialX i hg) j]
      rw [ih]
      rfl

/-- The derivative order naturally produced by differentiating a family of
Voronoi transforms agrees with the project's equation-(2) mixed derivative
convention. -/
theorem iteratedDeriv_dfiMixedDeriv_zero_second
    {E : ℝ → ℝ → ℂ} (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (i j : ℕ) (x y : ℝ) :
    iteratedDeriv j (fun y' ↦ dfiMixedDeriv i 0 E x y') y =
      dfiMixedDeriv i j E x y := by
  have hleft :
      iteratedDeriv j (fun y' ↦ dfiMixedDeriv i 0 E x y') y =
        dfiPartialY j (dfiPartialX i (Function.uncurry E)) (x, y) := by
    rw [dfiPartialY_apply j (contDiff_dfiPartialX i hE)]
    congr 2
    funext y'
    rw [dfiMixedDeriv_eq_partialXY hE i 0]
    rfl
  rw [hleft, dfiPartialY_dfiPartialX_comm hE i j]
  exact (dfiMixedDeriv_eq_partialXY hE i j x y).symm

/-- Integrating the normalized derivative envelope of a source slice
recovers the mixed two-variable `L¹` profile.  Each derivative order costs
exactly one copy of the same normalized mass, so the only loss is the
finite count `2k+1`. -/
theorem integral_Icc_dfiDerivativeL1Envelope_mixed_le
    {E : ℝ → ℝ → ℂ} (hE : ContDiff ℝ ∞ (Function.uncurry E))
    {Sx Sy Bx By M : ℝ} (hBy : 0 < By) (i k : ℕ)
    (hMass : ∀ j ≤ 2 * k,
      (∫ x in Set.Icc Sx (2 * Sx),
        ∫ y in Set.Icc Sy (2 * Sy), ‖dfiMixedDeriv i j E x y‖) ≤
          M * Bx ^ i * By ^ j) :
    (∫ x in Set.Icc Sx (2 * Sx),
      dfiDerivativeL1Envelope
        (fun y ↦ dfiMixedDeriv i 0 E x y) Sy By k) ≤
      (2 * k + 1 : ℝ) * (M * Bx ^ i) := by
  have hCont (j : ℕ) : Continuous (fun x : ℝ ↦
      (∫ y in Set.Icc Sy (2 * Sy), ‖dfiMixedDeriv i j E x y‖) /
        By ^ j) := by
    have hMixedSmooth : ContDiff ℝ ∞
        (Function.uncurry (dfiMixedDeriv i j E)) :=
      contDiff_uncurry_dfiMixedDeriv hE i j
    exact (continuous_parametric_integral_of_continuous
      hMixedSmooth.continuous.norm isCompact_Icc).div_const _
  have hInt (j : ℕ) : IntegrableOn (fun x : ℝ ↦
      (∫ y in Set.Icc Sy (2 * Sy), ‖dfiMixedDeriv i j E x y‖) /
        By ^ j) (Set.Icc Sx (2 * Sx)) :=
    (hCont j).continuousOn.integrableOn_compact isCompact_Icc
  have hEach (j : ℕ) (hj : j ∈ Finset.range (2 * k + 1)) :
      (∫ x in Set.Icc Sx (2 * Sx),
        (∫ y in Set.Icc Sy (2 * Sy), ‖dfiMixedDeriv i j E x y‖) /
          By ^ j) ≤ M * Bx ^ i := by
    have hjk : j ≤ 2 * k := by simpa using hj
    rw [MeasureTheory.integral_div]
    have hraw := div_le_div_of_nonneg_right (hMass j hjk)
      (pow_nonneg hBy.le j)
    have hpow : By ^ j ≠ 0 := ne_of_gt (pow_pos hBy j)
    calc
      (∫ x in Set.Icc Sx (2 * Sx),
          ∫ y in Set.Icc Sy (2 * Sy), ‖dfiMixedDeriv i j E x y‖) /
            By ^ j ≤ (M * Bx ^ i * By ^ j) / By ^ j := hraw
      _ = M * Bx ^ i := by field_simp
  simp only [dfiDerivativeL1Envelope]
  rw [MeasureTheory.integral_finsetSum (Finset.range (2 * k + 1)) (by
    intro r hr
    simpa only [iteratedDeriv_dfiMixedDeriv_zero_second hE] using hInt r)]
  calc
    (∑ r ∈ Finset.range (2 * k + 1),
        ∫ x in Set.Icc Sx (2 * Sx),
          (∫ y in Set.Icc Sy (2 * Sy),
            ‖iteratedDeriv r (fun y ↦ dfiMixedDeriv i 0 E x y) y‖) /
              By ^ r) ≤
        ∑ _r ∈ Finset.range (2 * k + 1), M * Bx ^ i := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [iteratedDeriv_dfiMixedDeriv_zero_second hE] using hEach r hr
    _ = (2 * k + 1 : ℝ) * (M * Bx ^ i) := by simp

/-- Restricting a smooth compactly supported mixed derivative to its
source rectangle can only decrease its nonnegative two-variable `L¹`
mass. -/
theorem integral_Icc_integral_Icc_norm_dfiMixedDeriv_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i j : ℕ) :
    (∫ x in Set.Icc A B, ∫ y in Set.Icc C D,
      ‖dfiMixedDeriv i j E x y‖) ≤
      ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i j E x y‖ := by
  let Er : ℝ → ℝ → ℂ := dfiMixedDeriv i j E
  have hEr : ContDiff ℝ ∞ (Function.uncurry Er) := by
    exact contDiff_uncurry_dfiMixedDeriv hE i j
  have hErSupport : Function.support (Function.uncurry Er) ⊆
      Set.Icc A B ×ˢ Set.Icc C D :=
    (support_dfiMixedDeriv_subset_tsupport hE i j).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  have hErNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) (volume.prod volume) :=
    hEr.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) (by
          intro p hp
          change ‖Er p.1 p.2‖ ≠ 0 at hp
          exact hErSupport (by
            simpa only [Function.mem_support,
              Function.uncurry_apply_pair] using (norm_ne_zero_iff.mp hp))))
  have hprod :
      (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖Er x y‖) =
        ∫ p in Set.Icc A B ×ˢ Set.Icc C D,
          ‖Er p.1 p.2‖ ∂(volume.prod volume) := by
    exact (MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) hErNorm.integrableOn).symm
  rw [hprod]
  calc
    (∫ p in Set.Icc A B ×ˢ Set.Icc C D,
        ‖Er p.1 p.2‖ ∂(volume.prod volume)) ≤
        ∫ p : ℝ × ℝ, ‖Er p.1 p.2‖ ∂(volume.prod volume) :=
      MeasureTheory.integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun p ↦ norm_nonneg (Er p.1 p.2)) hErNorm
    _ = ∫ x : ℝ, ∫ y : ℝ, ‖Er x y‖ :=
      MeasureTheory.integral_prod
        (fun p : ℝ × ℝ ↦ ‖Er p.1 p.2‖) hErNorm

set_option maxHeartbeats 1000000 in
/-- The residue-independent double Mellin amplitude in DFI equation (24)
is exactly the result of applying the two fixed-frequency Voronoi terms in
source order.  This is the frequency-by-frequency bridge from the Mellin
formula to the physical Bessel transforms used in equation (29). -/
theorem dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n =
      dfiVoronoiDualTerm qx xBranch
        (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n) m := by
  by_cases hm : m = 0
  · subst m
    rw [dfiVoronoiDualTerm_zero]
    simp [dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand,
      divisorWeight]
  by_cases hn : n = 0
  · subst n
    have hzero : (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) 0) =
        (fun _ ↦ 0) := by
      funext x
      exact dfiVoronoiDualTerm_zero qy yBranch (E x)
    rw [hzero]
    simp [dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand,
      dfiVoronoiDualTerm_zero_function, divisorWeight]
  have hMellin (z : ℂ) :
      mellin (fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n) z =
        dfiVoronoiDualTerm qy yBranch
          (fun y ↦ mellin (fun x ↦ E x y) z) n := by
    simpa using mellin_dfiVoronoiDualTerm_family
      hE hA hC hCD hSupport qy yBranch n z
  have hAmpInt : Integrable (dfiEquation24DoubleDualAmplitudeIntegrand
      qx xBranch qy yBranch E m n) := by
    rw [← show (fun p ↦ dfiEquation24DoubleMellinTerm
        qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch E m n p) =
        dfiEquation24DoubleDualAmplitudeIntegrand
          qx xBranch qy yBranch E m n by
      funext p
      exact dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand
        qx xBranch qy yBranch E m n p]
    exact integrable_dfiEquation24DoubleMellinTerm
      hE hA hAB hC hCD hSupport
      qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m n
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
  rw [← dfiEquation29TransformAt_initial]
  unfold dfiEquation29TransformAt VerticalIntegral'
  simp only [smul_eq_mul]
  unfold dfiEquation29Integrand
  simp_rw [hMellin]
  simp_rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
  simp_rw [← dfiEquation29TransformAt_initial]
  unfold dfiEquation29TransformAt VerticalIntegral'
  simp only [smul_eq_mul]
  unfold dfiEquation29Integrand VerticalIntegral
  simp only [smul_eq_mul]
  have hBi (z w : ℂ) :
      mellin (fun y ↦ mellin (fun x ↦ E x y) z) w =
        dfiBiMellin E z w := by
    simpa [dfiBiMellin] using
      (mellin_mellin_comm_of_rectangular_support
        hE hA hC hSupport z w).symm
  simp_rw [hBi]
  unfold dfiEquation24DoubleDualMellinAmplitude
  rw [Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.integral_prod _ hAmpInt]
  unfold dfiEquation24DoubleDualAmplitudeIntegrand
    dfiEquation29Multiplier dfiDualBranchMultiplier
  cases xBranch <;> cases yBranch
  all_goals
    simp only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one]
    norm_num only
    simp_rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    have hu : (-(1 / 2 : ℂ) + (u : ℂ) * I) =
        (-(1 / (((2 : ℝ) : ℂ))) + (u : ℂ) * I) := by norm_num
    have hv : (-(1 / 2 : ℂ) + (v : ℂ) * I) =
        (-(1 / (((2 : ℝ) : ℂ))) + (v : ℂ) * I) := by norm_num
    rw [hu, hv]
    ring

set_option maxHeartbeats 1000000 in
/-- Applying the equation-(29) Bessel recurrence in both physical variables
while retaining the mixed two-variable `L¹` mass.  This is the literal
two-stage estimate required in the double-tail corner: unlike a pointwise
slice estimate, it introduces no factor equal to either support length. -/
theorem norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_recurrence
    {E : ℝ → ℝ → ℂ} {A C Bx By M D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hBx : 0 < Bx) (hBy : 0 < By)
    (hABx : 1 ≤ A * Bx) (hCBy : 1 ≤ C * By)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C))
    (k : ℕ) (hD : (2 * k + 3 : ℕ) ≤ D)
    (hMass : ∀ i ≤ 2 * k, ∀ j ≤ 2 * k,
      (∫ x in Set.Icc A (2 * A),
        ∫ y in Set.Icc C (2 * C), ‖dfiMixedDeriv i j E x y‖) ≤
          M * Bx ^ i * By ^ j)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    let Ty : ℝ :=
      ‖divisorWeight n‖ *
      ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt qy *
          (C ^ (-(1 / 4 : ℝ)) *
            ((2 * (k : ℝ) + 1) * M *
              (D * C * By ^ 2) ^ k) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))))
    ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖ ≤
      ‖divisorWeight m‖ *
      ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          (A ^ (-(1 / 4 : ℝ)) *
            (Ty * (D * A * Bx ^ 2) ^ k) *
            (m : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  dsimp only
  let G : ℝ → ℂ := fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n
  have hAA : A ≤ 2 * A := by linarith
  have hCC : C ≤ 2 * C := by linarith
  have hG : DFIVoronoiTestFunction G :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAA hC hCC hSupport qy yBranch n
  have hGSupport : Function.support G ⊆ Set.Icc A (2 * A) := by
    intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm qy yBranch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl
  let Fy : ℝ :=
    ‖divisorWeight n‖ *
    ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
      ((14 * Real.pi + 8) / Real.sqrt qy *
        (C ^ (-(1 / 4 : ℝ)) * (D * C * By ^ 2) ^ k *
          (n : ℝ) ^ (-(1 / 4 : ℝ)))))
  have hFy : 0 ≤ Fy := by
    dsimp [Fy]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hD0 : 0 ≤ D := by
      exact (show (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) by positivity).trans hD
    positivity
  have hEnvelope (i : ℕ) (hi : i ≤ 2 * k) :
      (∫ x in Set.Icc A (2 * A),
        dfiDerivativeL1Envelope
          (fun y ↦ dfiMixedDeriv i 0 E x y) C By k) ≤
        (2 * (k : ℝ) + 1) * (M * Bx ^ i) :=
    integral_Icc_dfiDerivativeL1Envelope_mixed_le hE hBy i k
      (fun j hj ↦ hMass i hi j hj)
  have hDerivMass (i : ℕ) (hi : i ≤ 2 * k) :
      (∫ x in Set.Icc A (2 * A), ‖iteratedDeriv i G x‖) ≤
        Fy * ((2 * (k : ℝ) + 1) * (M * Bx ^ i)) := by
    have hLeft : IntegrableOn (fun x ↦ ‖iteratedDeriv i G x‖)
        (Set.Icc A (2 * A)) :=
      (ContDiff.continuous_iteratedDeriv i hG.smooth
        (by exact WithTop.coe_le_coe.mpr le_top)).norm.continuousOn
        |>.integrableOn_compact isCompact_Icc
    have hEnvCont : Continuous (fun x ↦
        dfiDerivativeL1Envelope
          (fun y ↦ dfiMixedDeriv i 0 E x y) C By k) := by
      simp only [dfiDerivativeL1Envelope]
      apply continuous_finsetSum
      intro j _hj
      apply Continuous.div_const
      simpa only [iteratedDeriv_dfiMixedDeriv_zero_second hE] using
        continuous_parametric_integral_of_continuous
          (contDiff_uncurry_dfiMixedDeriv hE i j).continuous.norm
            isCompact_Icc
    have hRight : IntegrableOn (fun x ↦ Fy *
        dfiDerivativeL1Envelope
          (fun y ↦ dfiMixedDeriv i 0 E x y) C By k)
        (Set.Icc A (2 * A)) :=
      (hEnvCont.const_mul Fy).continuousOn.integrableOn_compact isCompact_Icc
    have hPoint (x : ℝ) : ‖iteratedDeriv i G x‖ ≤ Fy *
        dfiDerivativeL1Envelope
          (fun y ↦ dfiMixedDeriv i 0 E x y) C By k := by
      let gi : ℝ → ℂ := fun y ↦ dfiMixedDeriv i 0 E x y
      have hgi : DFIVoronoiTestFunction gi := {
        lower := C
        upper := 2 * C
        lower_pos := hC
        lower_le_upper := hCC
        smooth := by
          simpa only [gi, Function.uncurry_apply_pair] using
            (contDiff_uncurry_dfiMixedDeriv hE i 0).comp
              (contDiff_prodMk_right x)
        support_subset := support_dfiMixedDeriv_first_slice_subset
          hSupport i x }
      have hrec :=
        hgi.norm_dfiEquation29InitialTransform_le_recurrence_l1_envelope
          hBy hC hCBy
            (support_dfiMixedDeriv_first_slice_subset hSupport i x)
              qy yBranch hn k hD
      rw [iteratedDeriv_dfiVoronoiDualTerm_family
        hE hC hCC hSupport qy yBranch n i x]
      rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial,
        norm_mul]
      calc
        ‖divisorWeight n‖ *
            ‖dfiEquation29InitialTransform qy yBranch gi n‖ ≤
          ‖divisorWeight n‖ *
            ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (C ^ (-(1 / 4 : ℝ)) *
                  (dfiDerivativeL1Envelope gi C By k *
                    (D * C * By ^ 2) ^ k) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by gcongr
        _ = Fy * dfiDerivativeL1Envelope gi C By k := by
          dsimp only [Fy]
          ring
    calc
      (∫ x in Set.Icc A (2 * A), ‖iteratedDeriv i G x‖) ≤
          ∫ x in Set.Icc A (2 * A), Fy *
            dfiDerivativeL1Envelope
              (fun y ↦ dfiMixedDeriv i 0 E x y) C By k := by
        apply integral_mono_ae hLeft hRight
        filter_upwards with x
        exact hPoint x
      _ = Fy * (∫ x in Set.Icc A (2 * A),
          dfiDerivativeL1Envelope
            (fun y ↦ dfiMixedDeriv i 0 E x y) C By k) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ Fy * ((2 * (k : ℝ) + 1) * (M * Bx ^ i)) := by
        exact mul_le_mul_of_nonneg_left (hEnvelope i hi) hFy
  have hOuter :=
    hG.norm_dfiEquation29InitialTransform_le_recurrence_l1_profile
      (A := Fy * ((2 * (k : ℝ) + 1) * M))
      (B := Bx) (S := A) (D := D)
      (mul_nonneg hFy (mul_nonneg (by positivity) (by
        have h0 := hMass 0 (by omega) 0 (by omega)
        have hnonneg : 0 ≤ (∫ x in Set.Icc A (2 * A),
            ∫ y in Set.Icc C (2 * C), ‖dfiMixedDeriv 0 0 E x y‖) :=
          integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _
        simpa using hnonneg.trans h0)))
      hBx.le hA hABx hGSupport qx xBranch hm k hD
      (fun i hi ↦ by
        calc
          (∫ x in Set.Icc A (2 * A), ‖iteratedDeriv i G x‖) ≤
              Fy * ((2 * (k : ℝ) + 1) * (M * Bx ^ i)) :=
            hDerivMass i hi
          _ = (Fy * ((2 * (k : ℝ) + 1) * M)) * Bx ^ i := by ring)
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAA hC hCC hSupport qx qy xBranch yBranch m n]
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight m‖ * ‖dfiEquation29InitialTransform qx xBranch G m‖ ≤
        ‖divisorWeight m‖ *
          ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)) ^ k *
            ((14 * Real.pi + 8) / Real.sqrt qx *
              (A ^ (-(1 / 4 : ℝ)) *
                ((Fy * ((2 * (k : ℝ) + 1) * M)) *
                  (D * A * Bx ^ 2) ^ k) *
                (m : ℝ) ^ (-(1 / 4 : ℝ))))) := by gcongr
    _ = _ := by dsimp only [Fy]; ring

set_option maxHeartbeats 1000000 in
/-- Asymmetric form of the mixed-`L¹` recurrence: the second Voronoi
frequency is integrated by parts `k` times, while the first is retained on
the physical quarter line.  Unlike the older uniform-slice estimate, this
keeps the two-dimensional mass `M`, and hence preserves DFI equation
(30)'s factor `(X+Y)⁻¹ XY log Q`. -/
theorem norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_y_recurrence
    {E : ℝ → ℝ → ℂ} {A C By M D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hBy : 0 < By)
    (hCBy : 1 ≤ C * By)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C))
    (k : ℕ) (hD : (2 * k + 3 : ℕ) ≤ D)
    (hMass : ∀ j ≤ 2 * k,
      (∫ x in Set.Icc A (2 * A),
        ∫ y in Set.Icc C (2 * C), ‖dfiMixedDeriv 0 j E x y‖) ≤
          M * By ^ j)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    let Ty : ℝ :=
      ‖divisorWeight n‖ *
      ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt qy *
          (C ^ (-(1 / 4 : ℝ)) *
            ((2 * (k : ℝ) + 1) * M * (D * C * By ^ 2) ^ k) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))))
    ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖ ≤
      ‖divisorWeight m‖ *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          (A ^ (-(1 / 4 : ℝ)) * Ty *
            (m : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  dsimp only
  let G : ℝ → ℂ := fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n
  have hAA : A ≤ 2 * A := by linarith
  have hCC : C ≤ 2 * C := by linarith
  have hG : DFIVoronoiTestFunction G :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAA hC hCC hSupport qy yBranch n
  have hGSupport : Function.support G ⊆ Set.Icc A (2 * A) := by
    intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm qy yBranch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl
  let Fy : ℝ :=
    ‖divisorWeight n‖ *
    ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
      ((14 * Real.pi + 8) / Real.sqrt qy *
        (C ^ (-(1 / 4 : ℝ)) * (D * C * By ^ 2) ^ k *
          (n : ℝ) ^ (-(1 / 4 : ℝ)))))
  have hFy : 0 ≤ Fy := by
    dsimp [Fy]
    have hD0 : 0 ≤ D := by
      exact (show (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ) by positivity).trans hD
    positivity
  have hEnvelope :
      (∫ x in Set.Icc A (2 * A),
        dfiDerivativeL1Envelope
          (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k) ≤
        (2 * (k : ℝ) + 1) * M := by
    simpa using integral_Icc_dfiDerivativeL1Envelope_mixed_le
      (Bx := 1) hE hBy 0 k (fun j hj ↦ by simpa using hMass j hj)
  have hLeft : IntegrableOn (fun x ↦ ‖G x‖) (Set.Icc A (2 * A)) :=
    hG.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hEnvCont : Continuous (fun x ↦
      dfiDerivativeL1Envelope
        (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k) := by
    simp only [dfiDerivativeL1Envelope]
    apply continuous_finsetSum
    intro j _hj
    apply Continuous.div_const
    simpa only [iteratedDeriv_dfiMixedDeriv_zero_second hE] using
      continuous_parametric_integral_of_continuous
        (contDiff_uncurry_dfiMixedDeriv hE 0 j).continuous.norm
          isCompact_Icc
  have hRight : IntegrableOn (fun x ↦ Fy *
      dfiDerivativeL1Envelope
        (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k)
      (Set.Icc A (2 * A)) :=
    (hEnvCont.const_mul Fy).continuousOn.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) : ‖G x‖ ≤ Fy *
      dfiDerivativeL1Envelope
        (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k := by
    let g : ℝ → ℂ := fun y ↦ E x y
    have hgSupport : Function.support g ⊆ Set.Icc C (2 * C) := by
      intro y hy
      exact (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [g, Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
    have hg : DFIVoronoiTestFunction g := {
      lower := C
      upper := 2 * C
      lower_pos := hC
      lower_le_upper := hCC
      smooth := by
        simpa only [g, Function.uncurry_apply_pair] using
          hE.comp (contDiff_prodMk_right x)
      support_subset := hgSupport }
    have hrec :=
      hg.norm_dfiEquation29InitialTransform_le_recurrence_l1_envelope
        hBy hC hCBy hgSupport qy yBranch hn k hD
    rw [show G x = dfiVoronoiDualTerm qy yBranch g n by rfl,
      dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
    calc
      ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform qy yBranch g n‖ ≤
          ‖divisorWeight n‖ *
            ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (C ^ (-(1 / 4 : ℝ)) *
                  (dfiDerivativeL1Envelope g C By k *
                    (D * C * By ^ 2) ^ k) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) := by gcongr
      _ = Fy * dfiDerivativeL1Envelope g C By k := by
        dsimp only [Fy]
        ring
      _ = _ := by rfl
  have hIntegral : (∫ x in Set.Icc A (2 * A), ‖G x‖) ≤
      Fy * ((2 * (k : ℝ) + 1) * M) := by
    calc
      _ ≤ ∫ x in Set.Icc A (2 * A), Fy *
          dfiDerivativeL1Envelope
            (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k := by
        apply integral_mono_ae hLeft hRight
        filter_upwards with x
        exact hPoint x
      _ = Fy * (∫ x in Set.Icc A (2 * A),
          dfiDerivativeL1Envelope
            (fun y ↦ dfiMixedDeriv 0 0 E x y) C By k) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ Fy * ((2 * (k : ℝ) + 1) * M) :=
        mul_le_mul_of_nonneg_left hEnvelope hFy
  have hBase : dfiBesselQuarterBaseNorm G ≤
      A ^ (-(1 / 4 : ℝ)) * (Fy * ((2 * (k : ℝ) + 1) * M)) := by
    calc
      _ ≤ A ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A (2 * A), ‖G x‖) :=
        dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
          hA hG hGSupport
      _ ≤ _ := by gcongr
  have hOuter :=
    hG.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
      qx xBranch hm (hG.integrableOn_besselQuarterWeight_mul_nat m hm)
  rw [dfiBesselQuarterNorm_eq_rpow_mul_base G m hm] at hOuter
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAA hC hCC hSupport qx qy xBranch yBranch m n]
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    _ ≤ ‖divisorWeight m‖ *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          (dfiBesselQuarterBaseNorm G *
            (m : ℝ) ^ (-(1 / 4 : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [G, mul_comm] using hOuter) (norm_nonneg _)
    _ ≤ ‖divisorWeight m‖ *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          ((A ^ (-(1 / 4 : ℝ)) *
            (Fy * ((2 * (k : ℝ) + 1) * M))) *
            (m : ℝ) ^ (-(1 / 4 : ℝ)))) := by gcongr
    _ = _ := by dsimp only [Fy]; ring

/-- The reduced-modulus recurrence ratio is bounded by the literal DFI
equation-(29) transition ratio.  The harmless factor `4D` records the
doubled derivative scale used uniformly for all `q < 2Q`. -/
theorem dfiReducedRecurrenceRatio_le_sourceTransitionRatio
    {a q qx k : ℕ} {X Q D m : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hqx : (qx : ℝ) ≤ q)
    (hX : 0 < X) (hQ : 0 < Q) (hD : 0 ≤ D) (hm : 0 < m) :
    ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / m) ^ k) *
        (D * (X / (a : ℝ)) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k ≤
      (4 * D) ^ k * (((a : ℝ) * X / Q ^ 2) / m) ^ k := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hqx0 : (0 : ℝ) ≤ qx := Nat.cast_nonneg qx
  have hfrac : (qx : ℝ) / (2 * Real.pi) ≤ q := by
    calc
      (qx : ℝ) / (2 * Real.pi) ≤ (qx : ℝ) :=
        div_le_self hqx0 hpi
      _ ≤ q := hqx
  have hfrac0 : 0 ≤ (qx : ℝ) / (2 * Real.pi) := by positivity
  have hbase :
      (((qx : ℝ) / (2 * Real.pi)) ^ 2 / m) *
          (D * (X / (a : ℝ)) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ≤
        (4 * D) * (((a : ℝ) * X / Q ^ 2) / m) := by
    calc
      _ ≤ (((q : ℝ) ^ 2) / m) *
          (D * (X / (a : ℝ)) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) := by
        gcongr
      _ = (4 * D) * (((a : ℝ) * X / Q ^ 2) / m) := by
        field_simp
        ring
  calc
    ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / m) ^ k) *
          (D * (X / (a : ℝ)) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k =
        (((((qx : ℝ) / (2 * Real.pi)) ^ 2 / m) *
          (D * (X / (a : ℝ)) *
            (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2)) ^ k) := by
          exact (mul_pow _ _ k).symm
    _ ≤ (((4 * D) * (((a : ℝ) * X / Q ^ 2) / m)) ^ k) :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ = (4 * D) ^ k * (((a : ℝ) * X / Q ^ 2) / m) ^ k := by
      rw [mul_pow]

/-- Source specialization of the two-stage mixed-`L¹` recurrence to the
actual equation-(23) weight.  The derivative scales are the doubled
source scales `2a/(qQ)` and `2b/(qQ)`; the factor two is exactly what is
needed to cover every modulus `q < 2Q`. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_l1_recurrence
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
      (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
      (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
      0 < m → 0 < n →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      let A := X / (a : ℝ)
      let C := Y / (b : ℝ)
      let Bx := 2 * ((a : ℝ) / ((q : ℝ) * Q))
      let By := 2 * ((b : ℝ) / ((q : ℝ) * Q))
      let M := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
      let D : ℝ := (2 * k + 3 : ℕ)
      let Ty : ℝ :=
        ‖divisorWeight n‖ *
        ((((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qy *
            (C ^ (-(1 / 4 : ℝ)) *
              ((2 * (k : ℝ) + 1) * M *
                (D * C * By ^ 2) ^ k) *
              (n : ℝ) ^ (-(1 / 4 : ℝ)))))
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        ‖divisorWeight m‖ *
        ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)) ^ k *
          ((14 * Real.pi + 8) / Real.sqrt qx *
            (A ^ (-(1 / 4 : ℝ)) *
              (Ty * (D * A * Bx ^ 2) ^ k) *
              (m : ℝ) ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨K, hK, hMass⟩ :=
    exists_integral_integral_norm_dfiEquation23Weight_mixed_derivative_le
      hf hfC hbox hφ hφC hscale w hwC hQ hUQ (2 * k)
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let A : ℝ := X / (a : ℝ)
  let C : ℝ := Y / (b : ℝ)
  let Bx : ℝ := 2 * ((a : ℝ) / ((q : ℝ) * Q))
  let By : ℝ := 2 * ((b : ℝ) / ((q : ℝ) * Q))
  let M : ℝ := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  let D : ℝ := (2 * k + 3 : ℕ)
  have hq0 : 0 < q := NeZero.pos q
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQR : 0 < Q := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBx : 0 < Bx := by dsimp [Bx]; positivity
  have hBy : 0 < By := by dsimp [By]; positivity
  have hPinv : P⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (zero_lt_one.trans_le hf.one_le_P)]
    exact hf.one_le_P
  have hmin0 : 0 ≤ min X Y := le_min hX.le hY.le
  have hUleX : U ≤ X :=
    hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_left _ _))
  have hUleY : U ≤ Y :=
    hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_right _ _))
  have hqQleX : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  have hqQleY : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQR
  have hABx : 1 ≤ A * Bx := by
    rw [show A * Bx = 2 * X / ((q : ℝ) * Q) by
      dsimp [A, Bx]; field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQleX)
  have hCBy : 1 ≤ C * By := by
    rw [show C * By = 2 * Y / ((q : ℝ) * Q) by
      dsimp [C, By]; field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQleY)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq0
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C) := by
    simpa only [A, C, E, show 2 * (X / (a : ℝ)) = 2 * X / a by ring,
      show 2 * (Y / (b : ℝ)) = 2 * Y / b by ring] using
      dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hMixedMass : ∀ i ≤ 2 * k, ∀ j ≤ 2 * k,
      (∫ x in Set.Icc A (2 * A),
        ∫ y in Set.Icc C (2 * C), ‖dfiMixedDeriv i j E x y‖) ≤
          M * Bx ^ i * By ^ j := by
    intro i hi j hj
    have hRect := integral_Icc_integral_Icc_norm_dfiMixedDeriv_le
      hE hSupport i j
    have hRaw := hMass a b ha hb q hq0 hqQ h i j hi hj
    have hxi : ((a : ℝ) / ((q : ℝ) * Q)) ^ i ≤ Bx ^ i := by
      apply pow_le_pow_left₀ (by positivity)
      · dsimp [Bx]; linarith [div_nonneg haR.le hqQpos.le]
    have hyj : ((b : ℝ) / ((q : ℝ) * Q)) ^ j ≤ By ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      · dsimp [By]; linarith [div_nonneg hbR.le hqQpos.le]
    have hM0 : 0 ≤ M := by
      dsimp [M]
      have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
      positivity
    calc
      _ ≤ ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i j E x y‖ := hRect
      _ ≤ K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
        simpa only [E] using hRaw
      _ ≤ M * Bx ^ i * By ^ j := by
        dsimp only [M]
        gcongr
  have hRec :=
    norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_recurrence
      hE hA hC hBx hBy hABx hCBy hSupport k
        (by exact le_rfl) hMixedMass
          qx qy xBranch yBranch hm hn
  simpa only [A, C, Bx, By, M, D, E, qx, qy] using hRec

/-- Frequency-independent coefficient obtained from the complete mixed-`L¹`
recurrence after the reduced moduli have been replaced by the two literal
DFI equation-(29) transition scales. -/
noncomputable def dfiEquation29FullRecurrenceCoefficient
    (K Cdiv : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b qx qy : ℕ) : ℝ :=
  let D : ℝ := (2 * k + 3 : ℕ)
  let M := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  (Cdiv * (4 * D) ^ k * (((a : ℝ) * X / Q ^ 2) ^ k)) *
    (Cdiv * (4 * D) ^ k * (((b : ℝ) * Y / Q ^ 2) ^ k)) *
    ((14 * Real.pi + 8) / Real.sqrt qx) *
    ((14 * Real.pi + 8) / Real.sqrt qy) *
    (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
    (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) *
    ((2 * (k : ℝ) + 1) * M)

theorem dfiEquation29FullRecurrenceCoefficient_nonneg
    {K Cdiv Q X Y : ℝ} {k a b qx qy : ℕ}
    (hK : 0 ≤ K) (hCdiv : 0 ≤ Cdiv) (hQ : 1 ≤ Q)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ dfiEquation29FullRecurrenceCoefficient
      K Cdiv k Q X Y a b qx qy := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  dsimp [dfiEquation29FullRecurrenceCoefficient]
  positivity

/-- Literal two-frequency pointwise form of DFI equation (29).  Both
frequency exponents come from the same mixed derivative mass, so no
geometric-mean half-recurrence is introduced. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_full_pointwise
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ K Cdiv : ℝ, 0 < K ∧ 0 < Cdiv ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
      (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
      (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
      0 < m → 0 < n →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        dfiEquation29FullRecurrenceCoefficient
            K Cdiv k Q X Y a b qx qy *
          (m : ℝ) ^ (ε - 1 / 4 - k) *
          (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨K, hK, hRec⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_l1_recurrence
      hf hfC hbox hφ hφC hscale w hwC hQ hUQ k
  obtain ⟨Cdiv, hCdiv, hDiv⟩ :=
    exists_norm_divisorWeight_le_rpow ε hε
  refine ⟨K, Cdiv, hK, hCdiv, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let A : ℝ := X / (a : ℝ)
  let C : ℝ := Y / (b : ℝ)
  let Bx : ℝ := 2 * ((a : ℝ) / ((q : ℝ) * Q))
  let By : ℝ := 2 * ((b : ℝ) / ((q : ℝ) * Q))
  let M : ℝ := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  let D : ℝ := (2 * k + 3 : ℕ)
  let Rx : ℝ := ((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)
  let Ry : ℝ := ((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)
  let Sx : ℝ := D * A * Bx ^ 2
  let Sy : ℝ := D * C * By ^ 2
  let Zx : ℝ := (a : ℝ) * X / Q ^ 2
  let Zy : ℝ := (b : ℝ) * Y / Q ^ 2
  let Fx : ℝ := ‖divisorWeight m‖ *
    (Rx ^ k * (Sx ^ k * (m : ℝ) ^ (-(1 / 4 : ℝ))))
  let Fy : ℝ := ‖divisorWeight n‖ *
    (Ry ^ k * (Sy ^ k * (n : ℝ) ^ (-(1 / 4 : ℝ))))
  let Gx : ℝ := Cdiv * (4 * D) ^ k * Zx ^ k *
    (m : ℝ) ^ (ε - 1 / 4 - k)
  let Gy : ℝ := Cdiv * (4 * D) ^ k * Zy ^ k *
    (n : ℝ) ^ (ε - 1 / 4 - k)
  let Hx : ℝ := (14 * Real.pi + 8) / Real.sqrt qx
  let Hy : ℝ := (14 * Real.pi + 8) / Real.sqrt qy
  let Core : ℝ := (2 * (k : ℝ) + 1) * M
  have hqpos : 0 < q := NeZero.pos q
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hqxle : (qx : ℝ) ≤ q := by
    dsimp only [qx]
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hqyle : (qy : ℝ) ≤ q := by
    dsimp only [qy]
    exact_mod_cast dfiReducedModulus_denominator_le b q
  have hxRatio : Rx ^ k * Sx ^ k ≤
      (4 * D) ^ k * (Zx / (m : ℝ)) ^ k := by
    simpa only [Rx, Sx, Zx, A, Bx, qx, D] using
      dfiReducedRecurrenceRatio_le_sourceTransitionRatio
        ha hqpos hqxle hX hQpos hD (Nat.cast_pos.mpr hm)
  have hyRatio : Ry ^ k * Sy ^ k ≤
      (4 * D) ^ k * (Zy / (n : ℝ)) ^ k := by
    simpa only [Ry, Sy, Zy, C, By, qy, D] using
      dfiReducedRecurrenceRatio_le_sourceTransitionRatio
        hb hqpos hqyle hY hQpos hD (Nat.cast_pos.mpr hn)
  have hFx : Fx ≤ Gx := by
    simpa only [Fx, Gx] using
      divisor_recurrence_frequency_le hm hCdiv.le
        (by dsimp [Rx]; positivity) (by dsimp [Sx, D, A, Bx]; positivity)
        (hDiv m hm) hxRatio
  have hFy : Fy ≤ Gy := by
    simpa only [Fy, Gy] using
      divisor_recurrence_frequency_le hn hCdiv.le
        (by dsimp [Ry]; positivity) (by dsimp [Sy, D, C, By]; positivity)
        (hDiv n hn) hyRatio
  have hM : 0 ≤ M := by
    dsimp [M]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hRaw := hRec a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  have hRaw' :
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Fx * Fy * Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
          C ^ (-(1 / 4 : ℝ)) * Core := by
    calc
      _ ≤ ‖divisorWeight m‖ *
          (Rx ^ k *
            (Hx * (A ^ (-(1 / 4 : ℝ)) *
              ((‖divisorWeight n‖ *
                (Ry ^ k *
                  (Hy * (C ^ (-(1 / 4 : ℝ)) *
                    (Core * Sy ^ k) *
                    (n : ℝ) ^ (-(1 / 4 : ℝ)))))) * Sx ^ k) *
              (m : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        simpa only [qx, qy, E, A, C, Bx, By, M, D, Rx, Ry, Sx, Sy,
          Hx, Hy, Core] using hRaw
      _ = Fx * Fy * Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
          C ^ (-(1 / 4 : ℝ)) * Core := by
        dsimp only [Fx, Fy]
        ring
  have hFactors : 0 ≤ Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
      C ^ (-(1 / 4 : ℝ)) * Core := by
    dsimp [Hx, Hy, A, C, Core]
    positivity
  calc
    _ ≤ Fx * Fy * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by
      simpa only [mul_assoc] using hRaw'
    _ ≤ Gx * Gy * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by
      gcongr
    _ = dfiEquation29FullRecurrenceCoefficient
          K Cdiv k Q X Y a b qx qy *
        (m : ℝ) ^ (ε - 1 / 4 - k) *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      dsimp [dfiEquation29FullRecurrenceCoefficient, Gx, Gy, Hx, Hy,
        A, C, Core, M, D, Zx, Zy]
      ring

/-- Frequency-independent coefficient for the mixed-`L¹`, one-sided
`y` recurrence.  Its mass is the physical equation-(30) mass rather than
the older uniform-slice Jacobian. -/
noncomputable def dfiEquation29MixedYTailCoefficient
    (K Cdiv : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b qx qy : ℕ) : ℝ :=
  let D : ℝ := (2 * k + 3 : ℕ)
  let M := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  (Cdiv * (14 * Real.pi + 8) / Real.sqrt qx *
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ))) *
    (Cdiv * (4 * D) ^ k * (((b : ℝ) * Y / Q ^ 2) ^ k) *
      ((14 * Real.pi + 8) / Real.sqrt qy) *
      (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) *
      ((2 * (k : ℝ) + 1) * M))

theorem dfiEquation29MixedYTailCoefficient_nonneg
    {K Cdiv Q X Y : ℝ} {k a b qx qy : ℕ}
    (hK : 0 ≤ K) (hCdiv : 0 ≤ Cdiv) (hQ : 1 ≤ Q)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ dfiEquation29MixedYTailCoefficient
      K Cdiv k Q X Y a b qx qy := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  dsimp [dfiEquation29MixedYTailCoefficient]
  positivity

/-- Source-specialized asymmetric mixed-`L¹` recurrence in the second
frequency.  This is the literal one-sided complement estimate required by
DFI equation (29), with the equation-(30) physical mass retained. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_yTail_pointwise
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ K Cdiv : ℝ, 0 < K ∧ 0 < Cdiv ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
      (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
      (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
      0 < m → 0 < n →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        dfiEquation29MixedYTailCoefficient K Cdiv k Q X Y a b qx qy *
          (m : ℝ) ^ (ε - 1 / 4) *
          (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨K, hK, hMass⟩ :=
    exists_integral_integral_norm_dfiEquation23Weight_mixed_derivative_le
      hf hfC hbox hφ hφC hscale w hwC hQ hUQ (2 * k)
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := exists_norm_divisorWeight_le_rpow ε hε
  refine ⟨K, Cdiv, hK, hCdiv, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let A : ℝ := X / (a : ℝ)
  let C : ℝ := Y / (b : ℝ)
  let By : ℝ := 2 * ((b : ℝ) / ((q : ℝ) * Q))
  let M : ℝ := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  let D : ℝ := (2 * k + 3 : ℕ)
  let Ry : ℝ := ((qy : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)
  let Sy : ℝ := D * C * By ^ 2
  let Zy : ℝ := (b : ℝ) * Y / Q ^ 2
  let Fm : ℝ := ‖divisorWeight m‖ * (m : ℝ) ^ (-(1 / 4 : ℝ))
  let Fn : ℝ := ‖divisorWeight n‖ *
    (Ry ^ k * (Sy ^ k * (n : ℝ) ^ (-(1 / 4 : ℝ))))
  let Gm : ℝ := Cdiv * (m : ℝ) ^ (ε - 1 / 4)
  let Gn : ℝ := Cdiv * (4 * D) ^ k * Zy ^ k *
    (n : ℝ) ^ (ε - 1 / 4 - k)
  let Hx : ℝ := (14 * Real.pi + 8) / Real.sqrt qx
  let Hy : ℝ := (14 * Real.pi + 8) / Real.sqrt qy
  let Core : ℝ := (2 * (k : ℝ) + 1) * M
  have hq0 : 0 < q := NeZero.pos q
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQR : 0 < Q := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBy : 0 < By := by dsimp [By]; positivity
  have hPinv : P⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (zero_lt_one.trans_le hf.one_le_P)]
    exact hf.one_le_P
  have hmin0 : 0 ≤ min X Y := le_min hX0.le hY0.le
  have hUleY : U ≤ Y :=
    hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_right _ _))
  have hqQleY : (q : ℝ) * Q ≤ 2 * Y := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * Y := by linarith
  have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQR
  have hCBy : 1 ≤ C * By := by
    rw [show C * By = 2 * Y / ((q : ℝ) * Q) by
      dsimp [C, By]; field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQleY)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq0
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C) := by
    simpa only [A, C, E, show 2 * (X / (a : ℝ)) = 2 * X / a by ring,
      show 2 * (Y / (b : ℝ)) = 2 * Y / b by ring] using
      dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hMixedMass : ∀ j ≤ 2 * k,
      (∫ x in Set.Icc A (2 * A),
        ∫ y in Set.Icc C (2 * C), ‖dfiMixedDeriv 0 j E x y‖) ≤
          M * By ^ j := by
    intro j hj
    have hRect := integral_Icc_integral_Icc_norm_dfiMixedDeriv_le
      hE hSupport 0 j
    have hRaw := hMass a b ha hb q hq0 hqQ h 0 j (by omega) hj
    have hyj : ((b : ℝ) / ((q : ℝ) * Q)) ^ j ≤ By ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [By]
      linarith [div_nonneg hbR.le hqQpos.le]
    have hM0 : 0 ≤ M := by
      dsimp [M]
      have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
      positivity
    calc
      _ ≤ ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv 0 j E x y‖ := hRect
      _ ≤ K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ 0) *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ j) := by
        simpa only [E] using hRaw
      _ ≤ M * By ^ j := by
        dsimp only [M]
        simp only [pow_zero, mul_one]
        gcongr
  have hRec := norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_y_recurrence
    hE hA hC hBy hCBy hSupport k (by exact le_rfl) hMixedMass
      qx qy xBranch yBranch hm hn
  have hqyq : (qy : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le b q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hyRatio : Ry ^ k * Sy ^ k ≤
      (4 * D) ^ k * (Zy / (n : ℝ)) ^ k := by
    simpa only [Ry, Sy, Zy, C, By, qy, D] using
      dfiReducedRecurrenceRatio_le_sourceTransitionRatio
        hb hq0 hqyq hY0 hQR hD (Nat.cast_pos.mpr hn)
  have hFm : Fm ≤ Gm := by
    have hmPow := hDiv m hm
    dsimp only [Fm, Gm]
    calc
      ‖divisorWeight m‖ * (m : ℝ) ^ (-(1 / 4 : ℝ)) ≤
          (Cdiv * (m : ℝ) ^ ε) * (m : ℝ) ^ (-(1 / 4 : ℝ)) := by gcongr
      _ = Cdiv * ((m : ℝ) ^ ε * (m : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
      _ = Cdiv * (m : ℝ) ^ (ε - 1 / 4) := by
        rw [← Real.rpow_add (Nat.cast_pos.mpr hm)]
        congr 2
  have hFn : Fn ≤ Gn := by
    simpa only [Fn, Gn] using
      divisor_recurrence_frequency_le hn hCdiv.le
        (by dsimp [Ry]; positivity) (by dsimp [Sy, D, C, By]; positivity)
        (hDiv n hn) hyRatio
  have hCore0 : 0 ≤ Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
      C ^ (-(1 / 4 : ℝ)) * Core := by
    dsimp [Hx, Hy, A, C, Core, M]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hRec' :
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Fm * Fn * Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
          C ^ (-(1 / 4 : ℝ)) * Core := by
    dsimp only [A, C, By, M, D, Ry, Sy] at hRec
    convert hRec using 1
    all_goals dsimp [Fm, Fn, Hx, Hy, Core, M, D, A, C, Ry, Sy]; ring
  calc
    _ ≤ Fm * Fn * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by
      simpa only [mul_assoc] using hRec'
    _ ≤ Gm * Gn * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by gcongr
    _ = dfiEquation29MixedYTailCoefficient
          K Cdiv k Q X Y a b qx qy *
        (m : ℝ) ^ (ε - 1 / 4) *
        (n : ℝ) ^ (ε - 1 / 4 - k) := by
      dsimp [dfiEquation29MixedYTailCoefficient, Gm, Gn, Hx, Hy,
        A, C, Core, M, D, Zy]
      ring

set_option maxHeartbeats 1000000 in
/-- The double-dual Mellin amplitude is invariant under simultaneously
swapping the two physical variables, moduli, branches, and frequencies.
This is the exact Fubini bridge needed to apply DFI (29) first in whichever
frequency belongs to the discarded tail. -/
theorem dfiEquation24DoubleDualMellinAmplitude_swap
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n =
      dfiEquation24DoubleDualMellinAmplitude
        qy yBranch qx xBranch (fun y x ↦ E x y) n m := by
  have hBi (z w : ℂ) :
      dfiBiMellin (fun y x ↦ E x y) w z = dfiBiMellin E z w := by
    simpa only [dfiBiMellin] using
      (mellin_mellin_comm_of_rectangular_support
        hE hA hC hSupport z w).symm
  unfold dfiEquation24DoubleDualMellinAmplitude
  congr 1
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [← MeasureTheory.integral_prod_swap
    (f := dfiEquation24DoubleDualAmplitudeIntegrand
      qy yBranch qx xBranch (fun y x ↦ E x y) n m)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  rcases p with ⟨u, v⟩
  unfold dfiEquation24DoubleDualAmplitudeIntegrand
  simp only [Prod.swap, hBi]
  ring

set_option maxHeartbeats 1000000 in
/-- Coordinate-swapped asymmetric mixed-`L¹` recurrence.  The first
frequency is integrated by parts and the second remains on the physical
quarter line. -/
theorem norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_x_recurrence
    {E : ℝ → ℝ → ℂ} {A C Bx M D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hBx : 0 < Bx)
    (hABx : 1 ≤ A * Bx)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C))
    (k : ℕ) (hD : (2 * k + 3 : ℕ) ≤ D)
    (hMass : ∀ i ≤ 2 * k,
      (∫ y in Set.Icc C (2 * C),
        ∫ x in Set.Icc A (2 * A), ‖dfiMixedDeriv i 0 E x y‖) ≤
          M * Bx ^ i)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    let Tx : ℝ :=
      ‖divisorWeight m‖ *
      ((((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)) ^ k *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          (A ^ (-(1 / 4 : ℝ)) *
            ((2 * (k : ℝ) + 1) * M * (D * A * Bx ^ 2) ^ k) *
            (m : ℝ) ^ (-(1 / 4 : ℝ)))))
    ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖ ≤
      ‖divisorWeight n‖ *
        ((14 * Real.pi + 8) / Real.sqrt qy *
          (C ^ (-(1 / 4 : ℝ)) * Tx *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  dsimp only
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C (2 * C) ×ˢ Set.Icc A (2 * A) := by
    intro p hp
    have hs := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hs.2, hs.1⟩
  have hMassSwap : ∀ j ≤ 2 * k,
      (∫ y in Set.Icc C (2 * C),
        ∫ x in Set.Icc A (2 * A), ‖dfiMixedDeriv 0 j Eswap y x‖) ≤
          M * Bx ^ j := by
    intro j hj
    simpa only [Eswap, dfiMixedDeriv, iteratedDeriv_zero] using hMass j hj
  have hrec :=
    norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_y_recurrence
      hEswap hC hA hBx hABx hSupportSwap k hD hMassSwap
        qy qx yBranch xBranch hn hm
  rw [dfiEquation24DoubleDualMellinAmplitude_swap
    hE hA hC hSupport qx qy xBranch yBranch m n]
  simpa only [Eswap, mul_assoc, mul_left_comm, mul_comm] using hrec

/-- Coordinate-swapped physical one-sided recurrence coefficient. -/
noncomputable def dfiEquation29MixedXTailCoefficient
    (K Cdiv : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b qx qy : ℕ) : ℝ :=
  let D : ℝ := (2 * k + 3 : ℕ)
  let M := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  (Cdiv * (14 * Real.pi + 8) / Real.sqrt qy *
      (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ))) *
    (Cdiv * (4 * D) ^ k * (((a : ℝ) * X / Q ^ 2) ^ k) *
      ((14 * Real.pi + 8) / Real.sqrt qx) *
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
      ((2 * (k : ℝ) + 1) * M))

theorem dfiEquation29MixedXTailCoefficient_nonneg
    {K Cdiv Q X Y : ℝ} {k a b qx qy : ℕ}
    (hK : 0 ≤ K) (hCdiv : 0 ≤ Cdiv) (hQ : 1 ≤ Q)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ dfiEquation29MixedXTailCoefficient
      K Cdiv k Q X Y a b qx qy := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  dsimp [dfiEquation29MixedXTailCoefficient]
  positivity

/-- Source-specialized asymmetric mixed-`L¹` recurrence in the first
frequency, including the compact-support Fubini bridge needed to preserve
the equation-(30) physical mass. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_xTail_pointwise
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ K Cdiv : ℝ, 0 < K ∧ 0 < Cdiv ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
      (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
      (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
      0 < m → 0 < n →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        dfiEquation29MixedXTailCoefficient K Cdiv k Q X Y a b qx qy *
          (m : ℝ) ^ (ε - 1 / 4 - k) *
          (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hMass⟩ :=
    exists_integral_integral_norm_dfiEquation23Weight_mixed_derivative_le
      hf hfC hbox hφ hφC hscale w hwC hQ hUQ (2 * k)
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := exists_norm_divisorWeight_le_rpow ε hε
  refine ⟨K, Cdiv, hK, hCdiv, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let A : ℝ := X / (a : ℝ)
  let C : ℝ := Y / (b : ℝ)
  let Bx : ℝ := 2 * ((a : ℝ) / ((q : ℝ) * Q))
  let M : ℝ := K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q
  let D : ℝ := (2 * k + 3 : ℕ)
  let Rx : ℝ := ((qx : ℝ) / (2 * Real.pi)) ^ 2 / (m : ℝ)
  let Sx : ℝ := D * A * Bx ^ 2
  let Zx : ℝ := (a : ℝ) * X / Q ^ 2
  let Fm : ℝ := ‖divisorWeight m‖ *
    (Rx ^ k * (Sx ^ k * (m : ℝ) ^ (-(1 / 4 : ℝ))))
  let Fn : ℝ := ‖divisorWeight n‖ * (n : ℝ) ^ (-(1 / 4 : ℝ))
  let Gm : ℝ := Cdiv * (4 * D) ^ k * Zx ^ k *
    (m : ℝ) ^ (ε - 1 / 4 - k)
  let Gn : ℝ := Cdiv * (n : ℝ) ^ (ε - 1 / 4)
  let Hx : ℝ := (14 * Real.pi + 8) / Real.sqrt qx
  let Hy : ℝ := (14 * Real.pi + 8) / Real.sqrt qy
  let Core : ℝ := (2 * (k : ℝ) + 1) * M
  have hq0 : 0 < q := NeZero.pos q
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQR : 0 < Q := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBx : 0 < Bx := by dsimp [Bx]; positivity
  have hPinv : P⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (zero_lt_one.trans_le hf.one_le_P)]
    exact hf.one_le_P
  have hmin0 : 0 ≤ min X Y := le_min hX0.le hY0.le
  have hUleX : U ≤ X :=
    hscale.trans ((mul_le_of_le_one_left hmin0 hPinv).trans (min_le_left _ _))
  have hqQleX : (q : ℝ) * Q ≤ 2 * X := by
    calc
      (q : ℝ) * Q ≤ (2 * Q) * Q := by gcongr
      _ = 2 * U := by rw [hUQ]; ring
      _ ≤ 2 * X := by linarith
  have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQR
  have hABx : 1 ≤ A * Bx := by
    rw [show A * Bx = 2 * X / ((q : ℝ) * Q) by
      dsimp [A, Bx]; field_simp]
    exact (le_div_iff₀ hqQpos).2 (by simpa [mul_comm] using hqQleX)
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq0
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C) := by
    simpa only [A, C, E, show 2 * (X / (a : ℝ)) = 2 * X / a by ring,
      show 2 * (Y / (b : ℝ)) = 2 * Y / b by ring] using
      dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hM : 0 ≤ M := by
    dsimp [M]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hMixedMass : ∀ i ≤ 2 * k,
      (∫ y in Set.Icc C (2 * C),
        ∫ x in Set.Icc A (2 * A), ‖dfiMixedDeriv i 0 E x y‖) ≤
          M * Bx ^ i := by
    intro i hi
    let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
    have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
      simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
        (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
    have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
        Set.Icc C (2 * C) ×ˢ Set.Icc A (2 * A) := by
      intro p hp
      have hs := hSupport (show
        (p.2, p.1) ∈ Function.support (Function.uncurry E) by
          simpa only [Eswap, Function.mem_support,
            Function.uncurry_apply_pair] using hp)
      exact ⟨hs.2, hs.1⟩
    have hRect := integral_Icc_integral_Icc_norm_dfiMixedDeriv_le
      hEswap hSupportSwap 0 i
    let F : ℝ → ℝ → ℝ := fun x y ↦ ‖dfiMixedDeriv i 0 E x y‖
    have hDerivSmooth : ContDiff ℝ ∞
        (Function.uncurry (dfiMixedDeriv i 0 E)) :=
      contDiff_uncurry_dfiMixedDeriv hE i 0
    have hDerivSupport :
        Function.support (Function.uncurry (dfiMixedDeriv i 0 E)) ⊆
          Set.Icc A (2 * A) ×ˢ Set.Icc C (2 * C) :=
      (support_dfiMixedDeriv_subset_tsupport hE i 0).trans
        (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
    have hFint : Integrable (Function.uncurry F) (volume.prod volume) :=
      hDerivSmooth.continuous.norm.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact
          (isCompact_Icc.prod isCompact_Icc) (by
            intro p hp
            change ‖dfiMixedDeriv i 0 E p.1 p.2‖ ≠ 0 at hp
            exact hDerivSupport (by
              simpa only [Function.mem_support,
                Function.uncurry_apply_pair] using (norm_ne_zero_iff.mp hp))))
    have hswap :
        (∫ y : ℝ, ∫ x : ℝ, ‖dfiMixedDeriv 0 i Eswap y x‖) =
          ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i 0 E x y‖ := by
      calc
        _ = ∫ y : ℝ, ∫ x : ℝ, F x y := by
          apply integral_congr_ae
          filter_upwards [] with y
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [Eswap, F, dfiMixedDeriv, iteratedDeriv_zero]
        _ = ∫ x : ℝ, ∫ y : ℝ, F x y :=
          (MeasureTheory.integral_integral_swap hFint).symm
        _ = _ := by rfl
    have hRaw := hMass a b ha hb q hq0 hqQ h i 0 hi (by omega)
    have hxi : ((a : ℝ) / ((q : ℝ) * Q)) ^ i ≤ Bx ^ i := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [Bx]
      linarith [div_nonneg haR.le hqQpos.le]
    calc
      _ ≤ ∫ y : ℝ, ∫ x : ℝ, ‖dfiMixedDeriv 0 i Eswap y x‖ := by
        simpa only [Eswap, dfiMixedDeriv, iteratedDeriv_zero] using hRect
      _ = ∫ x : ℝ, ∫ y : ℝ, ‖dfiMixedDeriv i 0 E x y‖ := hswap
      _ ≤ K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q *
          (((a : ℝ) / ((q : ℝ) * Q)) ^ i) *
          (((b : ℝ) / ((q : ℝ) * Q)) ^ 0) := by
        simpa only [E] using hRaw
      _ ≤ M * Bx ^ i := by
        dsimp only [M]
        simp only [pow_zero, mul_one]
        exact mul_le_mul_of_nonneg_left hxi hM
  have hRec := norm_dfiEquation24DoubleDualMellinAmplitude_le_mixed_l1_x_recurrence
    hE hA hC hBx hABx hSupport k (by exact le_rfl) hMixedMass
      qx qy xBranch yBranch hm hn
  have hqxq : (qx : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hxRatio : Rx ^ k * Sx ^ k ≤
      (4 * D) ^ k * (Zx / (m : ℝ)) ^ k := by
    simpa only [Rx, Sx, Zx, A, Bx, qx, D] using
      dfiReducedRecurrenceRatio_le_sourceTransitionRatio
        ha hq0 hqxq hX0 hQR hD (Nat.cast_pos.mpr hm)
  have hFm : Fm ≤ Gm := by
    simpa only [Fm, Gm] using
      divisor_recurrence_frequency_le hm hCdiv.le
        (by dsimp [Rx]; positivity) (by dsimp [Sx, D, A, Bx]; positivity)
        (hDiv m hm) hxRatio
  have hFn : Fn ≤ Gn := by
    dsimp only [Fn, Gn]
    calc
      ‖divisorWeight n‖ * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
          (Cdiv * (n : ℝ) ^ ε) * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hDiv n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = Cdiv * ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
      _ = Cdiv * (n : ℝ) ^ (ε - 1 / 4) := by
        rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]
        congr 2
  have hCore0 : 0 ≤ Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
      C ^ (-(1 / 4 : ℝ)) * Core := by
    dsimp [Hx, Hy, A, C, Core, M]
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hRec' :
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Fm * Fn * Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
          C ^ (-(1 / 4 : ℝ)) * Core := by
    dsimp only [A, C, Bx, M, D, Rx, Sx] at hRec
    convert hRec using 1
    all_goals dsimp [Fm, Fn, Hx, Hy, Core, M, D, A, C, Rx, Sx]; ring
  calc
    _ ≤ Fm * Fn * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by
      simpa only [mul_assoc] using hRec'
    _ ≤ Gm * Gn * (Hx * Hy * A ^ (-(1 / 4 : ℝ)) *
        C ^ (-(1 / 4 : ℝ)) * Core) := by gcongr
    _ = dfiEquation29MixedXTailCoefficient
          K Cdiv k Q X Y a b qx qy *
        (m : ℝ) ^ (ε - 1 / 4 - k) *
        (n : ℝ) ^ (ε - 1 / 4) := by
      dsimp [dfiEquation29MixedXTailCoefficient, Gm, Gn, Hx, Hy,
        A, C, Core, M, D, Zx]
      ring

set_option maxHeartbeats 1000000 in
/-- Swapped-order physical realization of the DFI (24) double-dual
amplitude.  It complements the source-order identity above and exposes an
`x`-frequency tail before the outer `y` transform. -/
theorem dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm_swapped
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ) :
    dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n =
      dfiVoronoiDualTerm qy yBranch
        (fun y ↦ dfiVoronoiDualTerm qx xBranch (fun x ↦ E x y) m) n := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  rw [dfiEquation24DoubleDualMellinAmplitude_swap
    hE hA hC hSupport qx qy xBranch yBranch m n]
  simpa only [Eswap] using
    dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
      hEswap hC hCD hA hAB hSupportSwap
        qy qx yBranch xBranch n m

/-- Pointwise physical equation-(29) estimate after inserting the native
divisor bound.  The modulus, physical quarter mass, and dual-frequency
exponents are all exposed for the double-dual summation. -/
theorem exists_dfiVoronoiDualTerm_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) (_hq : NeZero q)
      (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ)
      (_hg : DFIVoronoiTestFunction g) (n : ℕ), 0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  let C : ℝ := 14 * Real.pi + 8
  refine ⟨D * C, mul_nonneg hD.le (by dsimp [C]; positivity), ?_⟩
  intro q hq branch g hg n hn
  letI : NeZero q := hq
  have hqR : (0 : ℝ) < q := by
    exact_mod_cast NeZero.pos q
  have hqScale : (Real.sqrt q)⁻¹ =
      (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hqR.le]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  have hPhysical :=
    hg.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
      q branch hn (hg.integrableOn_besselQuarterWeight_mul_nat n hn)
  rw [dfiBesselQuarterNorm_eq_rpow_mul_base g n hn,
    div_eq_mul_inv, hqScale] at hPhysical
  have hTransform : ‖dfiEquation29InitialTransform q branch g n‖ ≤
      C * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hPhysical
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ ε) *
          (C * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul hWeight hTransform (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * C) * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g *
          ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
      ring
    _ = (D * C) * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (ε - 1 / 4) := by
      rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]
      ring_nf

/-- If one frequency of the iterated DFI (24) transform has a uniform
pointwise bound on the source interval, the remaining physical Voronoi
transform costs exactly one quarter-weighted interval mass. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_le_of_inner_uniform
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D M : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        0 ≤ M →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          (∀ x, ‖dfiVoronoiDualTerm qy yBranch (E x) n‖ ≤ M) →
          ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖ ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * ((B - A) * M) *
              (m : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hPhysical⟩ :=
    exists_dfiVoronoiDualTerm_physical_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro E A B C D M hE hA hAB hC hCD hSupport hM
    qx qy hqx hqy xBranch yBranch m n hm hn hPoint
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let G : ℝ → ℂ := fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n
  have hG : DFIVoronoiTestFunction G := by
    simpa only [G] using dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport qy yBranch n
  have hGSupport : Function.support G ⊆ Set.Icc A B := by
    intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm qy yBranch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl
  have hBase : dfiBesselQuarterBaseNorm G ≤
      A ^ (-(1 / 4 : ℝ)) * ((B - A) * M) :=
    dfiBesselQuarterBaseNorm_le_of_uniform_norm hA hAB hG hGSupport
      (by simpa only [G] using hPoint)
  have hOuter := hPhysical qx hqx xBranch G hG m hm
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAB hC hCD hSupport qx qy xBranch yBranch m n]
  calc
    ‖dfiVoronoiDualTerm qx xBranch G m‖ ≤
        K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm G *
          (m : ℝ) ^ (ε - 1 / 4) := hOuter
    _ ≤ K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (A ^ (-(1 / 4 : ℝ)) * ((B - A) * M)) *
          (m : ℝ) ^ (ε - 1 / 4) := by
      gcongr
    _ = _ := by ring

/-- The frequency-independent coefficient in the one-sided `y` recurrence
bound.  Keeping it named makes the double-tail summation expose only the
two powers that are actually summed. -/
noncomputable def dfiEquation29YTailCoefficient
    (C D K : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b q qx qy : ℕ) : ℝ :=
  K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) *
    (((2 * X / a) - (X / a)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((b : ℝ) * Y) / Q ^ 2)) ^ k *
        (D * ((14 * Real.pi + 8) / Real.sqrt qy *
          ((Y / b) ^ (-(1 / 4 : ℝ)) *
            ((Y / b) * (C * ((q : ℝ) * Q)⁻¹)))))))

/-- The frequency-independent coefficient in the one-sided `x` recurrence
bound. -/
noncomputable def dfiEquation29XTailCoefficient
    (C D K : ℝ) (k : ℕ) (Q X Y : ℝ)
    (a b q qx qy : ℕ) : ℝ :=
  K * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) *
    (((2 * Y / b) - (Y / b)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((a : ℝ) * X) / Q ^ 2)) ^ k *
        (D * ((14 * Real.pi + 8) / Real.sqrt qx *
          ((X / a) ^ (-(1 / 4 : ℝ)) *
            ((X / a) * (C * ((q : ℝ) * Q)⁻¹)))))))

theorem dfiEquation29YTailCoefficient_nonneg
    {C D K Q X Y : ℝ} {k a b q qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hQ : 0 < Q) (hX : 0 < X) (hY : 0 < Y)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29YTailCoefficient C D K k Q X Y a b q qx qy := by
  unfold dfiEquation29YTailCoefficient
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqxR : (0 : ℝ) < qx := by exact_mod_cast hqx
  have hqyR : (0 : ℝ) < qy := by exact_mod_cast hqy
  have hdiff : 0 ≤ 2 * X / (a : ℝ) - X / a := by
    rw [show 2 * X / (a : ℝ) - X / a = X / a by ring]
    positivity
  positivity

theorem dfiEquation29XTailCoefficient_nonneg
    {C D K Q X Y : ℝ} {k a b q qx qy : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hQ : 0 < Q) (hX : 0 < X) (hY : 0 < Y)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hqx : 0 < qx) (hqy : 0 < qy) :
    0 ≤ dfiEquation29XTailCoefficient C D K k Q X Y a b q qx qy := by
  unfold dfiEquation29XTailCoefficient
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqxR : (0 : ℝ) < qx := by exact_mod_cast hqx
  have hqyR : (0 : ℝ) < qy := by exact_mod_cast hqy
  have hdiff : 0 ≤ 2 * Y / (b : ℝ) - Y / b := by
    rw [show 2 * Y / (b : ℝ) - Y / b = Y / b by ring]
    positivity
  positivity

/-- Source-specialized DFI (29) pointwise estimate with decay imposed only
on the second frequency.  The first frequency is left on the physical
quarter line, matching the retained-`x`/tail-`y` decomposition. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D K : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xBranch yBranch : DFIVoronoiDualBranch)
        (m n : ℕ), 0 < m → 0 < n →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let M :=
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ)))))
        ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖ ≤
          K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (((2 * X / a) - (X / a)) * M) *
            (m : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨C, D, hC, hD, hInner⟩ :=
    exists_dfiEquation29_ySlice_source_ratio_dualTerm_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  obtain ⟨K, hK, hOuter⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_le_of_inner_uniform ε hε
  refine ⟨C, D, K, hC, hD, hK, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let M : ℝ :=
    ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
      ((D * (n : ℝ) ^ ε) *
        ((14 * Real.pi + 8) / Real.sqrt qy *
          (((Y / b) ^ (-(1 / 4 : ℝ)) *
            ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)))))
  have hY0 : 0 ≤ Y := zero_le_one.trans hf.one_le_Y
  have hQ0 : 0 ≤ Q := w.Q_pos.le
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q (NeZero.pos q)
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hPoint (x : ℝ) :
      ‖dfiVoronoiDualTerm qy yBranch (E x) n‖ ≤ M := by
    have hqyq : (qy : ℝ) ≤ q := by
      exact_mod_cast dfiReducedModulus_denominator_le b q
    simpa only [qy, E, M] using
      hInner a b q qy ha hb hq inferInstance hqyq hqQ h x yBranch n hn
  have hout := hOuter hE hXA hXAB hYC hYCD hSupport hM
    qx qy inferInstance inferInstance xBranch yBranch m n hm hn hPoint
  simpa only [qx, qy, E, M] using hout

/-- Source-specialized companion with decay imposed only on the first
frequency.  The exact amplitude-swap theorem makes this the other half of
DFI's disjoint complement decomposition. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D K : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xBranch yBranch : DFIVoronoiDualBranch)
        (m n : ℕ), 0 < m → 0 < n →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let M :=
          ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((m : ℝ) * Q ^ 2))) ^ k *
            ((D * (m : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qx *
                (((X / a) ^ (-(1 / 4 : ℝ)) *
                  ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (m : ℝ) ^ (-(1 / 4 : ℝ)))))
        ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖ ≤
          K * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((2 * Y / b) - (Y / b)) * M) *
            (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨C, D, hC, hD, hInner⟩ :=
    exists_dfiEquation29_xSlice_source_ratio_dualTerm_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  obtain ⟨K, hK, hOuter⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_le_of_inner_uniform ε hε
  refine ⟨C, D, K, hC, hD, hK, ?_⟩
  intro a b q ha hb hq hqQ h xBranch yBranch m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  let M : ℝ :=
    ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((a : ℝ) * X) / ((m : ℝ) * Q ^ 2))) ^ k *
      ((D * (m : ℝ) ^ ε) *
        ((14 * Real.pi + 8) / Real.sqrt qx *
          (((X / a) ^ (-(1 / 4 : ℝ)) *
            ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
            (m : ℝ) ^ (-(1 / 4 : ℝ)))))
  have hX0 : 0 ≤ X := zero_le_one.trans hf.one_le_X
  have hQ0 : 0 ≤ Q := w.Q_pos.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hψ a b h q (NeZero.pos q)
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hp' := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hp'.2, hp'.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hPoint (y : ℝ) :
      ‖dfiVoronoiDualTerm qx xBranch (fun x ↦ E x y) m‖ ≤ M := by
    have hqxq : (qx : ℝ) ≤ q := by
      exact_mod_cast dfiReducedModulus_denominator_le a q
    simpa only [qx, E, M] using
      hInner a b q qx ha hb hq inferInstance hqxq hqQ h y xBranch m hm
  have hout := hOuter hEswap hYC hYCD hXA hXAB hSupportSwap hM
    qy qx inferInstance inferInstance yBranch xBranch n m hn hm
      (by simpa only [Eswap] using hPoint)
  rw [dfiEquation24DoubleDualMellinAmplitude_swap
    hE hXA hYC hSupport qx qy xBranch yBranch m n]
  simpa only [qx, qy, E, Eswap, M] using hout

/-- The one-sided `y` recurrence with all frequency dependence normalized
to the exact exponent `ε-1/4-k`. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_power_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D K : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xb yb : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
          ‖dfiEquation24DoubleDualMellinAmplitude qx xb qy yb E m n‖ ≤
            dfiEquation29YTailCoefficient C D K k Q X Y a b q qx qy *
              (m : ℝ) ^ (ε - 1 / 4) *
              (n : ℝ) ^ (ε - 1 / 4 - k) := by
  obtain ⟨C, D, K, hC, hD, hK, hraw⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_bound
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, K, hC, hD, hK, ?_⟩
  intro a b q ha hb hq hqQ h xb yb m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  have hr := hraw a b q ha hb hq hqQ h xb yb m n hm hn
  have hfreq := dfiEquation29_frequency_power_normalization
    (R := (((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2))
    (Z := (b : ℝ) * Y) (Q := Q) (ε := ε) w.Q_pos hn k
  dsimp only at hr
  dsimp only [dfiEquation29YTailCoefficient]
  calc
    _ ≤ _ := hr
    _ = _ := by
      rw [show
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((D * (n : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qy *
                (((Y / b) ^ (-(1 / 4 : ℝ)) *
                  ((Y / b) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (n : ℝ) ^ (-(1 / 4 : ℝ))))) =
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / ((n : ℝ) * Q ^ 2))) ^ k *
            ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            (D * ((14 * Real.pi + 8) / Real.sqrt qy *
              ((Y / b) ^ (-(1 / 4 : ℝ)) *
                ((Y / b) * (C * ((q : ℝ) * Q)⁻¹)))))) by ring]
      rw [hfreq]
      ring

/-- The one-sided `x` recurrence with all frequency dependence normalized
to the exact exponent `ε-1/4-k`. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_power_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ C D K : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xb yb : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
          ‖dfiEquation24DoubleDualMellinAmplitude qx xb qy yb E m n‖ ≤
            dfiEquation29XTailCoefficient C D K k Q X Y a b q qx qy *
              (m : ℝ) ^ (ε - 1 / 4 - k) *
              (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨C, D, K, hC, hD, hK, hraw⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_bound
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, K, hC, hD, hK, ?_⟩
  intro a b q ha hb hq hqQ h xb yb m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  have hr := hraw a b q ha hb hq hqQ h xb yb m n hm hn
  have hfreq := dfiEquation29_frequency_power_normalization
    (R := (((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2))
    (Z := (a : ℝ) * X) (Q := Q) (ε := ε) w.Q_pos hm k
  dsimp only at hr
  dsimp only [dfiEquation29XTailCoefficient]
  calc
    _ ≤ _ := hr
    _ = _ := by
      rw [show
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((m : ℝ) * Q ^ 2))) ^ k *
            ((D * (m : ℝ) ^ ε) *
              ((14 * Real.pi + 8) / Real.sqrt qx *
                (((X / a) ^ (-(1 / 4 : ℝ)) *
                  ((X / a) * (C * ((q : ℝ) * Q)⁻¹))) *
                  (m : ℝ) ^ (-(1 / 4 : ℝ))))) =
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / ((m : ℝ) * Q ^ 2))) ^ k *
            ((m : ℝ) ^ ε * (m : ℝ) ^ (-(1 / 4 : ℝ)))) *
            (D * ((14 * Real.pi + 8) / Real.sqrt qx *
              ((X / a) ^ (-(1 / 4 : ℝ)) *
                ((X / a) * (C * ((q : ℝ) * Q)⁻¹)))))) by ring]
      rw [hfreq]
      ring

/-- In the corner where both frequencies exceed the DFI (29) cutoffs, the
geometric mean of the exact one-sided recurrences supplies summable decay
in both variables. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_doubleTail_bound
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ Cx Dx Kx Cy Dy Ky : ℝ,
      0 < Cx ∧ 0 ≤ Dx ∧ 0 ≤ Kx ∧
      0 < Cy ∧ 0 ≤ Dy ∧ 0 ≤ Ky ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b →
        (_hq : NeZero q) → (q : ℝ) ≤ 2 * Q →
        ∀ (h : ℤ) (xb yb : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
          let Ax := dfiEquation29XTailCoefficient
            Cx Dx Kx k Q X Y a b q qx qy
          let Ay := dfiEquation29YTailCoefficient
            Cy Dy Ky k Q X Y a b q qx qy
          ‖dfiEquation24DoubleDualMellinAmplitude qx xb qy yb E m n‖ ≤
            Real.sqrt (Ax * Ay) *
              (m : ℝ) ^ (ε - 1 / 4 - (k : ℝ) / 2) *
              (n : ℝ) ^ (ε - 1 / 4 - (k : ℝ) / 2) := by
  obtain ⟨Cy, Dy, Ky, hCy, hDy, hKy, hy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_power_bound
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  obtain ⟨Cx, Dx, Kx, hCx, hDx, hKx, hx⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_power_bound
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨Cx, Dx, Kx, Cy, Dy, Ky,
    hCx, hDx, hKx, hCy, hDy, hKy, ?_⟩
  intro a b q ha hb hq hqQ h xb yb m n hm hn
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let Ax := dfiEquation29XTailCoefficient
    Cx Dx Kx k Q X Y a b q qx qy
  let Ay := dfiEquation29YTailCoefficient
    Cy Dy Ky k Q X Y a b q qx qy
  have hqx : 0 < qx := by exact NeZero.pos qx
  have hqy : 0 < qy := by exact NeZero.pos qy
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hAx : 0 ≤ Ax := by
    exact dfiEquation29XTailCoefficient_nonneg hCx.le hDx hKx
      w.Q_pos hX hY ha hb (NeZero.pos q) hqx hqy
  have hAy : 0 ≤ Ay := by
    exact dfiEquation29YTailCoefficient_nonneg hCy.le hDy hKy
      w.Q_pos hX hY ha hb (NeZero.pos q) hqx hqy
  have hx' := hx a b q ha hb hq hqQ h xb yb m n hm hn
  have hy' := hy a b q ha hb hq hqQ h xb yb m n hm hn
  dsimp only [qx, qy, E, Ax, Ay] at hx' hy' ⊢
  simpa only [show ε - 1 / 4 - (k : ℝ) / 2 =
      (ε - 1 / 4) - (k : ℝ) / 2 by ring] using
    two_frequency_geometric_mean (norm_nonneg _)
      hAx hAy (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn) hx' hy'

/-- Uniform equation-(29) quarter-mass estimate for the family obtained
after transforming the second variable.  This is the physical, source-scale
input for the second Voronoi transform in DFI equation (24). -/
theorem exists_dfiVoronoiDualTerm_family_besselQuarterBaseNorm_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (q : ℕ) (_hq : NeZero q) (branch : DFIVoronoiDualBranch)
          (n : ℕ), 0 < n →
          dfiBesselQuarterBaseNorm
              (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ≤
            K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hPointwise⟩ :=
    exists_dfiVoronoiDualTerm_physical_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport q hq branch n hn
  letI : NeZero q := hq
  have hFamily : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport q branch n
  have hFamilySupport : Function.support
      (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ⊆ Set.Icc A B := by
    intro x hx
    by_contra hxnot
    have hxE : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hxnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiDualTerm q branch (E x) n ≠ 0 at hx
    rw [hxE, dfiVoronoiDualTerm_zero_function] at hx
    exact hx rfl
  have hSliceSupport (x : ℝ) :
      Function.support (E x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support,
          Function.uncurry_apply_pair] using hy)).2
  have hSlice (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := hSliceSupport x }
  let R : ℝ := K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
    C ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (ε - 1 / 4)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hInnerContinuous : Continuous (fun x : ℝ ↦
      ∫ y in Set.Icc C D, ‖E x y‖) :=
    continuous_parametric_integral_of_continuous
      hE.continuous.norm isCompact_Icc
  have hLeft : IntegrableOn (fun x : ℝ ↦
      ‖dfiVoronoiDualTerm q branch (E x) n‖) (Set.Icc A B) :=
    hFamily.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hRight : IntegrableOn (fun x : ℝ ↦
      R * (∫ y in Set.Icc C D, ‖E x y‖)) (Set.Icc A B) :=
    (hInnerContinuous.const_mul R).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hPoint (x : ℝ) :
      ‖dfiVoronoiDualTerm q branch (E x) n‖ ≤
        R * (∫ y in Set.Icc C D, ‖E x y‖) := by
    have hDual := hPointwise q inferInstance branch (E x) (hSlice x) n hn
    have hBase := dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
      hC (hSlice x) (hSliceSupport x)
    calc
      ‖dfiVoronoiDualTerm q branch (E x) n‖ ≤
          K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiBesselQuarterBaseNorm (E x) * (n : ℝ) ^ (ε - 1 / 4) := hDual
      _ ≤ K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C ^ (-(1 / 4 : ℝ)) *
              (∫ y in Set.Icc C D, ‖E x y‖)) *
            (n : ℝ) ^ (ε - 1 / 4) := by
          gcongr
      _ = R * (∫ y in Set.Icc C D, ‖E x y‖) := by
          dsimp [R]
          ring
  have hIntegral :
      (∫ x in Set.Icc A B,
          ‖dfiVoronoiDualTerm q branch (E x) n‖) ≤
        ∫ x in Set.Icc A B,
          R * (∫ y in Set.Icc C D, ‖E x y‖) := by
    apply integral_mono_ae hLeft hRight
    filter_upwards with x
    exact hPoint x
  calc
    dfiBesselQuarterBaseNorm
        (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) ≤
        A ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A B,
            ‖dfiVoronoiDualTerm q branch (E x) n‖) :=
      dfiBesselQuarterBaseNorm_le_lower_rpow_mul_integral_norm
        hA hFamily hFamilySupport
    _ ≤ A ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B,
          R * (∫ y in Set.Icc C D, ‖E x y‖)) := by
      exact mul_le_mul_of_nonneg_left hIntegral
        (Real.rpow_nonneg hA.le _)
    _ = K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
        (n : ℝ) ^ (ε - 1 / 4) := by
      rw [integral_const_mul]
      dsimp [R]
      ring

/-- The exact double-dual Mellin amplitude in DFI equation (24), bounded
frequency by frequency through the two literal physical Bessel transforms.
The two `ε / 2` divisor losses combine to the source `ε` loss. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (xBranch yBranch : DFIVoronoiDualBranch) (m n : ℕ),
          0 < m → 0 < n →
          ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖ ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (m : ℝ) ^ (ε / 2 - 1 / 4) *
              (n : ℝ) ^ (ε / 2 - 1 / 4) := by
  have hHalf : 0 < ε / 2 := by linarith
  obtain ⟨K₁, hK₁, hOuter⟩ :=
    exists_dfiVoronoiDualTerm_physical_bound (ε / 2) hHalf
  obtain ⟨K₂, hK₂, hFamily⟩ :=
    exists_dfiVoronoiDualTerm_family_besselQuarterBaseNorm_bound
      (ε / 2) hHalf
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy xBranch yBranch m n hm hn
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let G : ℝ → ℂ := fun x ↦ dfiVoronoiDualTerm qy yBranch (E x) n
  have hG : DFIVoronoiTestFunction G :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport qy yBranch n
  have hOuterBound := hOuter qx inferInstance xBranch G hG m hm
  have hFamilyBound := hFamily hE hA hAB hC hCD hSupport
    qy inferInstance yBranch n hn
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAB hC hCD hSupport qx qy xBranch yBranch m n]
  calc
    ‖dfiVoronoiDualTerm qx xBranch G m‖ ≤
        K₁ * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm G *
          (m : ℝ) ^ (ε / 2 - 1 / 4) := hOuterBound
    _ ≤ K₁ * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (K₂ * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
            (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
            (n : ℝ) ^ (ε / 2 - 1 / 4)) *
          (m : ℝ) ^ (ε / 2 - 1 / 4) := by
      gcongr
    _ = (K₁ * K₂) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
          (m : ℝ) ^ (ε / 2 - 1 / 4) *
          (n : ℝ) ^ (ε / 2 - 1 / 4) := by ring

/-- The finite right-contour rectangle in the double-dual part of DFI
equation (24).  This is the two-variable summation of the physical
equation-(29) estimate, before the transition cutoffs are specialized. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_retained_bound
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (xBranch yBranch : DFIVoronoiDualBranch) (Lx Ly : ℕ),
          (∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (Lx : ℝ) ^ (3 / 4 + ε / 2) *
              (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
  obtain ⟨K, hK, hPoint⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_physical_bound ε hε
  let c : ℝ := (3 / 4 + ε / 2)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨K * c ^ 2, mul_nonneg hK (sq_nonneg c), ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy xBranch yBranch Lx Ly
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let R : ℝ := K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
    (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖)
  have hMass : 0 ≤ ∫ x in Set.Icc A B,
      ∫ y in Set.Icc C D, ‖E x y‖ := by
    apply integral_nonneg
    intro x
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hSumX : ∑ m ∈ Finset.Icc 1 Lx,
      (m : ℝ) ^ (ε / 2 - 1 / 4) ≤
      c * (Lx : ℝ) ^ (3 / 4 + ε / 2) := by
    simpa [c] using sum_Icc_natCast_rpow_sub_quarter_le
      (by positivity : 0 ≤ ε / 2) (by linarith : ε / 2 < 1 / 4) Lx
  have hSumY : ∑ n ∈ Finset.Icc 1 Ly,
      (n : ℝ) ^ (ε / 2 - 1 / 4) ≤
      c * (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
    simpa [c] using sum_Icc_natCast_rpow_sub_quarter_le
      (by positivity : 0 ≤ ε / 2) (by linarith : ε / 2 < 1 / 4) Ly
  calc
    (∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
      ∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
        R * (m : ℝ) ^ (ε / 2 - 1 / 4) *
          (n : ℝ) ^ (ε / 2 - 1 / 4) := by
      apply Finset.sum_le_sum
      intro m hmMem
      apply Finset.sum_le_sum
      intro n hnMem
      have hm : 0 < m := by
        have := (Finset.mem_Icc.mp hmMem).1
        omega
      have hn : 0 < n := by
        have := (Finset.mem_Icc.mp hnMem).1
        omega
      simpa only [R, mul_assoc] using
        hPoint hE hA hAB hC hCD hSupport qx qy
          inferInstance inferInstance xBranch yBranch m n hm hn
    _ = R *
        (∑ m ∈ Finset.Icc 1 Lx, (m : ℝ) ^ (ε / 2 - 1 / 4)) *
        (∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ (ε / 2 - 1 / 4)) := by
      have hInner (m : ℕ) :
          (∑ n ∈ Finset.Icc 1 Ly,
            R * (m : ℝ) ^ (ε / 2 - 1 / 4) *
              (n : ℝ) ^ (ε / 2 - 1 / 4)) =
            (R * (m : ℝ) ^ (ε / 2 - 1 / 4)) *
              (∑ n ∈ Finset.Icc 1 Ly,
                (n : ℝ) ^ (ε / 2 - 1 / 4)) := by
        rw [Finset.mul_sum]
      simp_rw [hInner]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ R * (c * (Lx : ℝ) ^ (3 / 4 + ε / 2)) *
        (c * (Ly : ℝ) ^ (3 / 4 + ε / 2)) := by
      gcongr
    _ = (K * c ^ 2) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        A ^ (-(1 / 4 : ℝ)) * C ^ (-(1 / 4 : ℝ)) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
        (Lx : ℝ) ^ (3 / 4 + ε / 2) *
        (Ly : ℝ) ^ (3 / 4 + ε / 2) := by
      dsimp [R]
      ring

/-- The physical equation-(29) estimate for an `x`-dual/`y`-main term.
The logarithmic factor is the literal Voronoi main-term weight; the
remaining source dependence is exactly the two-variable absolute mass. -/
theorem exists_dfiEquation24XSingleDualAmplitude_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
          ‖dfiVoronoiDualTerm qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖ ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
              (|Real.log C| + |Real.log D| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hDual⟩ :=
    exists_dfiVoronoiDualTerm_physical_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy branch n hn
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let g : ℝ → ℂ := fun x ↦ dfiVoronoiMainTerm qy (E x)
  have hg : DFIVoronoiTestFunction g := by
    simpa only [g] using dfiVoronoiMainTermSecondFamilyTestFunction
      hE hA hAB hC hSupport qy
  have hBase := dfiBesselQuarterBaseNorm_dfiVoronoiMainTerm_second_le
    hE hA hAB hC hCD hSupport qy (NeZero.pos qy)
  have hRaw := hDual qx inferInstance branch g hg n hn
  have hFactor : 0 ≤ K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc
    ‖dfiVoronoiDualTerm qx branch g n‖ ≤
        K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (ε - 1 / 4) := hRaw
    _ ≤ K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log C| + |Real.log D| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖)) *
          (n : ℝ) ^ (ε - 1 / 4) := by
      gcongr
    _ = K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log C| + |Real.log D| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
          (n : ℝ) ^ (ε - 1 / 4) := by ring

/-- Finite retained-frequency sum for the one-transform branch in DFI
equation (29). -/
theorem exists_dfiEquation24XSingleDualAmplitude_retained_bound
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (branch : DFIVoronoiDualBranch) (L : ℕ),
          (∑ n ∈ Finset.Icc 1 L,
            ‖dfiVoronoiDualTerm qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
            K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
              (|Real.log C| + |Real.log D| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨K, hK, hPoint⟩ :=
    exists_dfiEquation24XSingleDualAmplitude_physical_bound ε hε
  let c : ℝ := (3 / 4 + ε)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨K * c, mul_nonneg hK hc, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy branch L
  letI : NeZero qx := hqx
  letI : NeZero qy := hqy
  let R : ℝ := K * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
    (|Real.log C| + |Real.log D| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
    (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖)
  have hMass : 0 ≤ ∫ x in Set.Icc A B,
      ∫ y in Set.Icc C D, ‖E x y‖ := by
    apply integral_nonneg
    intro x
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hSum : ∑ n ∈ Finset.Icc 1 L,
      (n : ℝ) ^ (ε - 1 / 4) ≤
      c * (L : ℝ) ^ (3 / 4 + ε) := by
    simpa [c] using sum_Icc_natCast_rpow_sub_quarter_le hε.le hεlt L
  calc
    (∑ n ∈ Finset.Icc 1 L,
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
        ∑ n ∈ Finset.Icc 1 L, R * (n : ℝ) ^ (ε - 1 / 4) := by
      apply Finset.sum_le_sum
      intro n hnMem
      have hn : 0 < n := by
        have := (Finset.mem_Icc.mp hnMem).1
        omega
      simpa only [R, mul_assoc] using
        hPoint hE hA hAB hC hCD hSupport qx qy
          inferInstance inferInstance branch n hn
    _ = R * ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (ε - 1 / 4) := by
      rw [Finset.mul_sum]
    _ ≤ R * (c * (L : ℝ) ^ (3 / 4 + ε)) :=
      mul_le_mul_of_nonneg_left hSum hR
    _ = (K * c) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        A ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
        (L : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R]
      ring

/-- Fubini symmetry for the compact rectangle mass used in the retained
equation-(29) estimates. -/
theorem integral_integral_norm_swap_Icc
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    (∫ y in Set.Icc C D, ∫ x in Set.Icc A B, ‖E x y‖) =
      ∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖ := by
  let H : ℝ → ℝ → ℝ := fun x y ↦ ‖E x y‖
  have hHcont : Continuous H.uncurry := by
    simpa only [H, Function.uncurry_apply_pair] using hE.continuous.norm
  have hHsupport : Function.support H.uncurry ⊆
      Set.Icc A B ×ˢ Set.Icc C D := by
    intro p hp
    apply hSupport
    intro hz
    apply hp
    change ‖E p.1 p.2‖ = 0
    change E p.1 p.2 = 0 at hz
    rw [hz, norm_zero]
  have hHcompact : HasCompactSupport H.uncurry :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hswap := MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := H)
    (μ := MeasureTheory.volume.restrict (Set.Icc A B))
    (ν := MeasureTheory.volume.restrict (Set.Icc C D))
    hHcont hHcompact
  simpa only [H] using hswap.symm

/-- Symmetric physical equation-(29) estimate for an `x`-main/`y`-dual
term. -/
theorem exists_dfiEquation24YSingleDualAmplitude_physical_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (branch : DFIVoronoiDualBranch) (n : ℕ), 0 < n →
          ‖dfiVoronoiDualTerm qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖ ≤
            K * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              C ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
              (|Real.log A| + |Real.log B| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨K, hK, hX⟩ :=
    exists_dfiEquation24XSingleDualAmplitude_physical_bound ε hε
  refine ⟨K, hK, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy branch n hn
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hRaw := hX hEswap hC hCD hA hAB hSupportSwap
    qy qx hqy hqx branch n hn
  rw [integral_integral_norm_swap_Icc hE hSupport] at hRaw
  simpa only [Eswap] using hRaw

/-- Finite retained-frequency sum for the symmetric one-transform branch
in DFI equation (29). -/
theorem exists_dfiEquation24YSingleDualAmplitude_retained_bound
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {E : ℝ → ℝ → ℂ} {A B C D : ℝ},
        ContDiff ℝ ∞ (Function.uncurry E) →
        0 < A → A ≤ B → 0 < C → C ≤ D →
        Function.support (Function.uncurry E) ⊆
          Set.Icc A B ×ˢ Set.Icc C D →
        ∀ (qx qy : ℕ) (_hqx : NeZero qx) (_hqy : NeZero qy)
          (branch : DFIVoronoiDualBranch) (L : ℕ),
          (∑ n ∈ Finset.Icc 1 L,
            ‖dfiVoronoiDualTerm qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
            K * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              C ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
              (|Real.log A| + |Real.log B| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
              (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨K, hK, hX⟩ :=
    exists_dfiEquation24XSingleDualAmplitude_retained_bound ε hε hεlt
  refine ⟨K, hK, ?_⟩
  intro E A B C D hE hA hAB hC hCD hSupport
    qx qy hqx hqy branch L
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have hRaw := hX hEswap hC hCD hA hAB hSupportSwap
    qy qx hqy hqx branch L
  rw [integral_integral_norm_swap_Icc hE hSupport] at hRaw
  simpa only [Eswap] using hRaw

/-- A compact rectangle contained in the positive quadrant carries the
same nonnegative mass whether integrated over the rectangle or the whole
positive quadrant. -/
theorem integral_integral_norm_Icc_eq_Ioi
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hA : 0 < A) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, ‖E x y‖) =
      ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ := by
  have hySubset : Set.Icc C D ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact hC.trans_le hy.1
  have hInnerEq (x : ℝ) :
      (∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        ∫ y in Set.Icc C D, ‖E x y‖ := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hySubset
    intro y hy
    have hzero : E x y = 0 := by
      by_contra hne
      exact hy.2 (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    simp [hzero]
  have hxSubset : Set.Icc A B ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hA.trans_le hx.1
  have hOuterEq :
      (∫ x in Set.Ioi (0 : ℝ),
          ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖) =
        ∫ x in Set.Icc A B,
          ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hxSubset
    intro x hx
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hx.2 (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).1
    simp [hzero]
  rw [hOuterEq]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact (hInnerEq x).symm

/-- The literal first-variable transition in DFI equation (29):
`m < a X Q^{-2+ε}`. -/
noncomputable def dfiEquation29SourceXTransition
    (a : ℕ) (X Q ε : ℝ) : ℝ :=
  (a : ℝ) * X * Q ^ (-2 + ε)

/-- The symmetric second-variable transition in DFI equation (29). -/
noncomputable def dfiEquation29SourceYTransition
    (b : ℕ) (Y Q ε : ℝ) : ℝ :=
  (b : ℝ) * Y * Q ^ (-2 + ε)

theorem dfiEquation29SourceXTransition_rpow
    (a : ℕ) {X Q ε α : ℝ} (hX : 0 < X) (hQ : 0 < Q) :
    dfiEquation29SourceXTransition a X Q ε ^ α =
      (a : ℝ) ^ α * X ^ α * Q ^ ((-2 + ε) * α) := by
  unfold dfiEquation29SourceXTransition
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (a : ℝ) * X)
      (Real.rpow_nonneg hQ.le (-2 + ε)),
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ a) hX.le,
    ← Real.rpow_mul hQ.le]

theorem dfiEquation29SourceYTransition_rpow
    (b : ℕ) {Y Q ε α : ℝ} (hY : 0 < Y) (hQ : 0 < Q) :
    dfiEquation29SourceYTransition b Y Q ε ^ α =
      (b : ℝ) ^ α * Y ^ α * Q ^ ((-2 + ε) * α) := by
  unfold dfiEquation29SourceYTransition
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (b : ℝ) * Y)
      (Real.rpow_nonneg hQ.le (-2 + ε)),
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ b) hY.le,
    ← Real.rpow_mul hQ.le]

/-- The literal first-variable frequency window in DFI equation (29). -/
noncomputable def dfiEquation29SourceXCutoff
    (a : ℕ) (X Q ε : ℝ) : ℕ :=
  ⌈dfiEquation29SourceXTransition a X Q ε⌉₊

/-- The literal second-variable frequency window in DFI equation (29). -/
noncomputable def dfiEquation29SourceYCutoff
    (b : ℕ) (Y Q ε : ℝ) : ℕ :=
  ⌈dfiEquation29SourceYTransition b Y Q ε⌉₊

theorem dfiEquation29SourceXCutoff_pos
    {a : ℕ} {X Q : ℝ} (ha : 0 < a) (hX : 0 < X) (hQ : 0 < Q)
    (ε : ℝ) :
    0 < dfiEquation29SourceXCutoff a X Q ε := by
  unfold dfiEquation29SourceXCutoff
  unfold dfiEquation29SourceXTransition
  exact Nat.ceil_pos.mpr (by positivity)

theorem dfiEquation29SourceYCutoff_pos
    {b : ℕ} {Y Q : ℝ} (hb : 0 < b) (hY : 0 < Y) (hQ : 0 < Q)
    (ε : ℝ) :
    0 < dfiEquation29SourceYCutoff b Y Q ε := by
  unfold dfiEquation29SourceYCutoff
  unfold dfiEquation29SourceYTransition
  exact Nat.ceil_pos.mpr (by positivity)

/-- The optimized DFI choice `U = Q²`, together with the source
admissibility `P ≥ 1`, places the delta scale below both dyadic lengths. -/
theorem dfiEquation29_optimized_scale_le_lengths
    {f : ℝ → ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y)
    (hscale : U ≤ P⁻¹ * min X Y) (hU : U = Q ^ 2) :
    Q ^ 2 ≤ X ∧ Q ^ 2 ≤ Y := by
  have hmin : 0 ≤ min X Y :=
    le_min (zero_le_one.trans hf.one_le_X)
      (zero_le_one.trans hf.one_le_Y)
  have hPinv : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hf.one_le_P
  have hUmin : U ≤ min X Y := hscale.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hPinv hmin)
  rw [hU] at hUmin
  exact ⟨hUmin.trans (min_le_left X Y),
    hUmin.trans (min_le_right X Y)⟩

/-- The source transition scale in the first Voronoi variable is
`a Q^(2+ε) / X`.  The additive `1` is the exact cost of passing to the
natural-number ceiling; the transition need not
be at least one. -/
theorem dfiEquation29SourceXCutoff_lt_transition_add_one
    (a : ℕ) {X Q ε : ℝ} (hX : 0 < X) (hQ : 0 < Q) :
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) <
      (a : ℝ) * X * Q ^ (-2 + ε) + 1 := by
  unfold dfiEquation29SourceXCutoff
  unfold dfiEquation29SourceXTransition
  exact Nat.ceil_lt_add_one (by positivity)

/-- Symmetric exact ceiling bound for the second Voronoi variable. -/
theorem dfiEquation29SourceYCutoff_lt_transition_add_one
    (b : ℕ) {Y Q ε : ℝ} (hY : 0 < Y) (hQ : 0 < Q) :
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) <
      (b : ℝ) * Y * Q ^ (-2 + ε) + 1 := by
  unfold dfiEquation29SourceYCutoff
  unfold dfiEquation29SourceYTransition
  exact Nat.ceil_lt_add_one (by positivity)

theorem dfiEquation29SourceXCutoff_le_two_mul_max
    (a : ℕ) {X Q ε : ℝ} (hX : 0 < X) (hQ : 0 < Q) :
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ≤
      2 * max 1 (dfiEquation29SourceXTransition a X Q ε) := by
  calc
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ≤
        dfiEquation29SourceXTransition a X Q ε + 1 :=
      (dfiEquation29SourceXCutoff_lt_transition_add_one a hX hQ).le
    _ ≤ 2 * max 1 (dfiEquation29SourceXTransition a X Q ε) := by
      have hOne := le_max_left (1 : ℝ)
        (dfiEquation29SourceXTransition a X Q ε)
      have hTransition := le_max_right (1 : ℝ)
        (dfiEquation29SourceXTransition a X Q ε)
      linarith

theorem dfiEquation29SourceYCutoff_le_two_mul_max
    (b : ℕ) {Y Q ε : ℝ} (hY : 0 < Y) (hQ : 0 < Q) :
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ≤
      2 * max 1 (dfiEquation29SourceYTransition b Y Q ε) := by
  calc
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ≤
        dfiEquation29SourceYTransition b Y Q ε + 1 :=
      (dfiEquation29SourceYCutoff_lt_transition_add_one b hY hQ).le
    _ ≤ 2 * max 1 (dfiEquation29SourceYTransition b Y Q ε) := by
      have hOne := le_max_left (1 : ℝ)
        (dfiEquation29SourceYTransition b Y Q ε)
      have hTransition := le_max_right (1 : ℝ)
        (dfiEquation29SourceYTransition b Y Q ε)
      linarith

theorem dfiEquation29SourceXCutoff_rpow_le
    (a : ℕ) {X Q ε α : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (hα : 0 ≤ α) :
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ α ≤
      ((a : ℝ) * X * Q ^ (-2 + ε) + 1) ^ α := by
  exact Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceXCutoff_lt_transition_add_one a hX hQ).le hα

theorem dfiEquation29SourceYCutoff_rpow_le
    (b : ℕ) {Y Q ε α : ℝ} (hY : 0 < Y) (hQ : 0 < Q)
    (hα : 0 ≤ α) :
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ α ≤
      ((b : ℝ) * Y * Q ^ (-2 + ε) + 1) ^ α := by
  exact Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceYCutoff_lt_transition_add_one b hY hQ).le hα

/-- The retained `x`-dual/`y`-main part of source equation (29), at the
literal DFI transition cutoff and with the equation-(30) source mass
inserted. -/
theorem exists_dfiEquation29_xSingleDual_source_retained_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          (Kret * ((dfiEquation2FiniteConstant Cf 0 *
              dfiCutoffFiniteConstant Cφ 0) *
            ((24 * max (Cw 0) (Cw 1)) *
              (2 / Real.log 2 + 4)))) *
            (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24XSingleDualAmplitude_retained_bound ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  refine ⟨Kret, hKret, ?_⟩
  intro a b ha hb h q hq0 branch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance branch (dfiEquation29SourceXCutoff a X Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
    (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
          simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R, Kmass]
      ring

/-- The retained `x`-dual source constant is uniform in all physical scales
and arithmetic parameters.  Its only analytic dependence is the Mellin--
Voronoi exponent `ε`; the fixed equation-(2), cutoff, and delta profiles
remain visible in the bound rather than being absorbed into a scale-dependent
choice. -/
theorem exists_uniform_dfiEquation29_xSingleDual_source_retained_bound_of_profiles
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
        {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ},
        DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
        DFILocalizedBox f X Y →
        ∀ (hφ : DFIRedundantCutoff φ U),
        DFIRedundantCutoffProfile hφ Cφ →
        U ≤ P⁻¹ * min X Y →
        ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
        2 ≤ Q → U = Q ^ 2 →
        ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
          (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
          (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
            ‖dfiVoronoiDualTerm qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
            (Kret * ((dfiEquation2FiniteConstant Cf 0 *
                dfiCutoffFiniteConstant Cφ 0) *
              ((24 * max (Cw 0) (Cw 1)) *
                (2 / Real.log 2 + 4)))) *
              (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
              (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
              (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
              (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24XSingleDualAmplitude_retained_bound ε hε₀ hε
  refine ⟨Kret, hKret, ?_⟩
  intro f φ P X Y U Q Cf Cφ Cw hf hfC hbox hφ hφC hscale w hwC hQ hU
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  intro a b ha hb h q hq0 branch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance branch (dfiEquation29SourceXCutoff a X Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
    (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
          simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R, Kmass]
      ring

/-- Source-uniform retained `x`-dual bound for a fixed admissible weight. -/
theorem exists_dfiEquation29_xSingleDual_source_retained_bound_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  obtain ⟨Kret, hKret, hbound⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  refine ⟨Kret * Kmass, mul_nonneg hKret ?_, ?_⟩
  · dsimp [Kmass]
    have hCf : 0 ≤ dfiEquation2FiniteConstant Cf 0 :=
      (hfC.finiteConstant_pos 0).le
    have hCφ : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_nonneg (fun k _hk ↦ (hφC.positive k).le)
    have hCw : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    have hlog : 0 ≤ 2 / Real.log 2 + 4 := by positivity
    exact mul_nonneg (mul_nonneg hCf hCφ)
      (mul_nonneg (mul_nonneg (by positivity) hCw) hlog)
  · simpa only [Kmass] using hbound

/-- Fixed-parameter projection of the source-uniform retained
`x`-dual/`y`-main estimate. -/
theorem exists_dfiEquation29_xSingleDual_source_retained_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_bound_uniform
      hf hbox hφ hscale w hQ hU ε hε₀ hε
  exact ⟨C, hC, hbound a b ha hb h⟩

/-- The symmetric retained `x`-main/`y`-dual part of source equation
(29), at the literal DFI transition cutoff and with equation (30)
inserted. -/
theorem exists_dfiEquation29_ySingleDual_source_retained_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          (Kret * ((dfiEquation2FiniteConstant Cf 0 *
              dfiCutoffFiniteConstant Cφ 0) *
            ((24 * max (Cw 0) (Cw 1)) *
              (2 / Real.log 2 + 4)))) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24YSingleDualAmplitude_retained_bound ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  refine ⟨Kret, hKret, ?_⟩
  intro a b ha hb h q hq0 branch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance branch (dfiEquation29SourceYCutoff b Y Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
    (|Real.log (X / a)| + |Real.log (2 * X / a)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
          simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R, Kmass]
      ring

/-- The retained `y`-dual source constant is uniform in all physical scales
and arithmetic parameters. -/
theorem exists_uniform_dfiEquation29_ySingleDual_source_retained_bound_of_profiles
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
        {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ},
        DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
        DFILocalizedBox f X Y →
        ∀ (hφ : DFIRedundantCutoff φ U),
        DFIRedundantCutoffProfile hφ Cφ →
        U ≤ P⁻¹ * min X Y →
        ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
        2 ≤ Q → U = Q ^ 2 →
        ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
          (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
          (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiVoronoiDualTerm qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
            (Kret * ((dfiEquation2FiniteConstant Cf 0 *
                dfiCutoffFiniteConstant Cφ 0) *
              ((24 * max (Cw 0) (Cw 1)) *
                (2 / Real.log 2 + 4)))) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
              (|Real.log (X / a)| + |Real.log (2 * X / a)| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
              (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
              (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24YSingleDualAmplitude_retained_bound ε hε₀ hε
  refine ⟨Kret, hKret, ?_⟩
  intro f φ P X Y U Q Cf Cφ Cw hf hfC hbox hφ hφC hscale w hwC hQ hU
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  intro a b ha hb h q hq0 branch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance branch (dfiEquation29SourceYCutoff b Y Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
    (|Real.log (X / a)| + |Real.log (2 * X / a)| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
          simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R, Kmass]
      ring

/-- Source-uniform retained `x`-main/`y`-dual bound for a fixed admissible weight. -/
theorem exists_dfiEquation29_ySingleDual_source_retained_bound_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  obtain ⟨Kret, hKret, hbound⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  refine ⟨Kret * Kmass, mul_nonneg hKret ?_, ?_⟩
  · dsimp [Kmass]
    have hCf : 0 ≤ dfiEquation2FiniteConstant Cf 0 :=
      (hfC.finiteConstant_pos 0).le
    have hCφ : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_nonneg (fun k _hk ↦ (hφC.positive k).le)
    have hCw : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    have hlog : 0 ≤ 2 / Real.log 2 + 4 := by positivity
    exact mul_nonneg (mul_nonneg hCf hCφ)
      (mul_nonneg (mul_nonneg (by positivity) hCw) hlog)
  · simpa only [Kmass] using hbound

/-- Fixed-parameter projection of the source-uniform retained
`x`-main/`y`-dual estimate. -/
theorem exists_dfiEquation29_ySingleDual_source_retained_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq0 : NeZero q) (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_bound_uniform
      hf hbox hφ hscale w hQ hU ε hε₀ hε
  exact ⟨C, hC, hbound a b ha hb h⟩

/-- The retained two-transform rectangle in source equation (29), using
both literal DFI transition cutoffs and the exact equation-(30) mass. -/
theorem exists_dfiEquation29_doubleDual_source_retained_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q)
        (xBranch yBranch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤
          (Kret * ((dfiEquation2FiniteConstant Cf 0 *
              dfiCutoffFiniteConstant Cφ 0) *
            ((24 * max (Cw 0) (Cw 1)) *
              (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
              (3 / 4 + ε / 2) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
              (3 / 4 + ε / 2) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_retained_bound ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  refine ⟨Kret, hKret, ?_⟩
  intro a b ha hb h q hq0 xBranch yBranch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance xBranch yBranch
    (dfiEquation29SourceXCutoff a X Q ε)
    (dfiEquation29SourceYCutoff b Y Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
          (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
          (3 / 4 + ε / 2) := by
      simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
          (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
          (3 / 4 + ε / 2) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
            (3 / 4 + ε / 2) := by
      dsimp [R, Kmass]
      ring

/-- The retained double-dual source constant is uniform in all physical
scales and arithmetic parameters. -/
theorem exists_uniform_dfiEquation29_doubleDual_source_retained_bound_of_profiles
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ Kret : ℝ, 0 ≤ Kret ∧
      ∀ {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
        {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ},
        DFIEquation2 f P X Y → DFIEquation2Profile f P X Y Cf →
        DFILocalizedBox f X Y →
        ∀ (hφ : DFIRedundantCutoff φ U),
        DFIRedundantCutoffProfile hφ Cφ → U ≤ P⁻¹ * min X Y →
        ∀ (w : DFIDeltaWeight Q), DFIDeltaWeightProfile w Cw →
        2 ≤ Q → U = Q ^ 2 →
        ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
          (q : ℕ) (_hq0 : NeZero q)
          (xBranch yBranch : DFIVoronoiDualBranch),
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
          (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
            ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
              ‖dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m n‖) ≤
            (Kret * ((dfiEquation2FiniteConstant Cf 0 *
                dfiCutoffFiniteConstant Cφ 0) *
              ((24 * max (Cw 0) (Cw 1)) *
                (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              (X / a) ^ (-(1 / 4 : ℝ)) *
              (Y / b) ^ (-(1 / 4 : ℝ)) *
              (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
              (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
                (3 / 4 + ε / 2) *
              (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
                (3 / 4 + ε / 2) := by
  obtain ⟨Kret, hKret, hRetained⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_retained_bound ε hε₀ hε
  refine ⟨Kret, hKret, ?_⟩
  intro f φ P X Y U Q Cf Cφ Cw hf hfC hbox hφ hφC hscale w hwC hQ hU
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hMassBound := dfiEquation30_uniform_all_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU
  intro a b ha hb h q hq0 xBranch yBranch
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hLocalizedSupport : Function.support (Function.uncurry
      (dfiLocalizedWeight f φ (h : ℝ))) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    intro p hp
    have hm := support_uncurry_dfiLocalizedWeight_subset hbox hp
    exact ⟨(zero_lt_one.trans_le hf.one_le_X).trans_le hm.1.1,
      (zero_lt_one.trans_le hf.one_le_Y).trans_le hm.2.1⟩
  have hMassEq :
      (∫ x in Set.Icc (X / a) (2 * X / a),
        ∫ y in Set.Icc (Y / b) (2 * Y / b), ‖E x y‖) =
        dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
    calc
      _ = ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), ‖E x y‖ :=
        integral_integral_norm_Icc_eq_Ioi hXA hYC hSupport
      _ = dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h := by
        simpa only [E] using
          integral_norm_dfiEquation23Weight_Ioi_eq_equation30Divisor
            w q a b ha hb (dfiLocalizedWeight f φ h) h hLocalizedSupport
  have hRaw := hRetained hE hXA hXAB hYC hYCD hSupport qx qy
    inferInstance inferInstance xBranch yBranch
    (dfiEquation29SourceXCutoff a X Q ε)
    (dfiEquation29SourceYCutoff b Y Q ε)
  rw [hMassEq] at hRaw
  have hMass := hMassBound (h : ℝ) a b ha hb q hq
  let R : ℝ := Kret * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
    (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
      R * dfiEquation30DivisorAbsoluteIntegral w q a b
        (dfiLocalizedWeight f φ h) h *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
          (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
          (3 / 4 + ε / 2) := by
      simpa only [R, mul_assoc] using hRaw
    _ ≤ R * (Kmass * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
          (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
          (3 / 4 + ε / 2) := by
      gcongr
    _ = (Kret * ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4)))) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
            (3 / 4 + ε / 2) := by
      dsimp [R, Kmass]
      ring

/-- Source-uniform retained two-transform rectangle bound for a fixed
admissible weight. -/
theorem exists_dfiEquation29_doubleDual_source_retained_bound_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (q : ℕ) (_hq0 : NeZero q)
        (xBranch yBranch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
              (3 / 4 + ε / 2) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
              (3 / 4 + ε / 2) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  obtain ⟨Kret, hKret, hbound⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  refine ⟨Kret * Kmass, mul_nonneg hKret ?_, ?_⟩
  · dsimp [Kmass]
    have hCf : 0 ≤ dfiEquation2FiniteConstant Cf 0 :=
      (hfC.finiteConstant_pos 0).le
    have hCφ : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_nonneg (fun k _hk ↦ (hφC.positive k).le)
    have hCw : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    have hlog : 0 ≤ 2 / Real.log 2 + 4 := by positivity
    exact mul_nonneg (mul_nonneg hCf hCφ)
      (mul_nonneg (mul_nonneg (by positivity) hCw) hlog)
  · simpa only [Kmass] using hbound

/-- Fixed-parameter projection of the source-uniform retained
two-transform rectangle estimate. -/
theorem exists_dfiEquation29_doubleDual_source_retained_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq0 : NeZero q)
        (xBranch yBranch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
              (3 / 4 + ε / 2) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
              (3 / 4 + ε / 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound_uniform
      hf hbox hφ hscale w hQ hU ε hε₀ hε
  exact ⟨C, hC, hbound a b ha hb h⟩

/-- Source logarithmic factor for the `x`-dual/`y`-main retained branch,
uniformized over the delta moduli `q < 2Q`. -/
noncomputable def dfiEquation29XSingleLogMajorant
    (Q Y : ℝ) (b : ℕ) : ℝ :=
  |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)

/-- Symmetric logarithmic factor for the `y`-dual/`x`-main branch. -/
noncomputable def dfiEquation29YSingleLogMajorant
    (Q X : ℝ) (a : ℕ) : ℝ :=
  |Real.log (X / a)| + |Real.log (2 * X / a)| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)

private theorem dfiEquation29_weil_mul_single_reduced_moduli_le
    (q a b : ℕ) [NeZero q] (hab : a.Coprime b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ ≤
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hgdvd := gcd_mul_gcd_dvd_right_of_coprime a b q hab
  have hgleN : Nat.gcd a q * Nat.gcd b q ≤ q := Nat.le_of_dvd hqN hgdvd
  have hgaPos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hqN
  have hsqrtga_le : Real.sqrt (Nat.gcd a q) ≤ Nat.gcd a q := by
    have hone : (1 : ℝ) ≤ Nat.gcd a q := by exact_mod_cast hgaPos
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Nat.gcd a q),
      Real.sqrt_nonneg (Nat.gcd a q)]
  have hprod : Real.sqrt (Nat.gcd a q) * Nat.gcd b q ≤ q := by
    calc
      _ ≤ (Nat.gcd a q : ℝ) * Nat.gcd b q := by gcongr
      _ ≤ q := by exact_mod_cast hgleN
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) * Nat.gcd b q) / q) := by field_simp
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) * ((q : ℝ) / q) := by gcongr
    _ = _ := by field_simp

private theorem dfiEquation29_weil_mul_double_reduced_moduli_le
    (q a b : ℕ) [NeZero q] (hab : a.Coprime b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hgdvd := gcd_mul_gcd_dvd_right_of_coprime a b q hab
  have hgleN : Nat.gcd a q * Nat.gcd b q ≤ q := Nat.le_of_dvd hqN hgdvd
  have hgle : (Nat.gcd a q : ℝ) * Nat.gcd b q ≤ q := by exact_mod_cast hgleN
  have hsqrtprod :
      Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q) ≤ Real.sqrt q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd a q))]
    exact Real.sqrt_le_sqrt hgle
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_rpow_neg_half_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q)) /
          Real.sqrt q) := by field_simp
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) * (Real.sqrt q / Real.sqrt q) := by
      gcongr
    _ = _ := by field_simp

/-- In the `x`-dual/`y`-main branch, the source factor `a/(ab)` must be
combined with the two reduced Voronoi denominators before estimating gcds.
This is the exact cancellation behind the normalized equation-(25) average;
estimating the denominators separately would introduce a false `sqrt a`
loss. -/
theorem dfiEquation29_weil_mul_xSingle_source_scale_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ *
        (a : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hga : Nat.gcd a q ≤ q := Nat.gcd_le_right a hqN
  have hgb : Nat.gcd b q ≤ b := Nat.gcd_le_left q hb
  have hsqrtga : Real.sqrt (Nat.gcd a q) ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast hga)
  have hgbR : (Nat.gcd b q : ℝ) ≤ b := by exact_mod_cast hgb
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          ((Nat.gcd b q : ℝ) / b) * (Real.sqrt q)⁻¹) := by
      field_simp
      rw [Real.sq_sqrt hq.le]
      ring
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt q / Real.sqrt q) * ((b : ℝ) / b) *
          (Real.sqrt q)⁻¹) := by gcongr
    _ = _ := by field_simp

/-- The symmetric cancellation for the `x`-main/`y`-dual branch. -/
theorem dfiEquation29_weil_mul_ySingle_source_scale_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ)⁻¹ *
        (b : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  simpa only [mul_comm (a : ℝ) b] using
    dfiEquation29_weil_mul_xSingle_source_scale_le q b a hb ha h

/-- The two retained `x`-dual signs after equation (25), with the literal
equation-(29) cutoff and equation-(30) mass. -/
theorem exists_dfiEquation29_xSingleDual_source_retained_weil_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq0 : NeZero q),
      (q : ℝ) ≤ 2 * Q →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (∑ branch : DFIVoronoiDualBranch,
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
            ‖dfiVoronoiDualTerm qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
        2 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29XSingleLogMajorant Q Y b *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) *
          (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨C, hC, hRet⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * (X / a) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29XSingleLogMajorant Q Y b *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)
  have hlogq : |Real.log (qy : ℝ)| ≤ Real.log (2 * Q) := by
    exact (abs_log_dfiReducedModulus_denominator_le b q).trans
      (Real.log_le_log (by exact_mod_cast NeZero.pos q)
        hqQ)
  have hlog :
      |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| ≤
        dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    linarith
  have hEach (branch : DFIVoronoiDualBranch) :
      (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
        B * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ := by
    have hr := hRet q hq0 branch
    dsimp only [qx, qy, E] at hr
    dsimp only [B]
    have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
      have hmin : 0 ≤ min X Y := by
        exact le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
      have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
      positivity
    have hprefix : 0 ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg qx) _))
          (Real.rpow_nonneg
            (div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)) _))
        (inv_nonneg.mpr (Nat.cast_nonneg qy))
    calc
      _ ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := hr
      _ ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          dfiEquation29XSingleLogMajorant Q Y b *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
        gcongr
      _ = B * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ := by
        dsimp [B]
        ring
  have hNorm := dfiEquation29_weil_mul_single_reduced_moduli_le
    q a b hab h
  have hLogMajorant : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hMassFactor : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC
            (Real.rpow_nonneg
              (div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)) _))
          hLogMajorant)
        hMassFactor)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  change W * (∑ branch : DFIVoronoiDualBranch,
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤ _
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        B * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹) := by
      gcongr with branch
      exact hEach branch
    _ = 2 * B * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ ≤ 2 * B * (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [W] using hNorm)
        (mul_nonneg (by norm_num) hB)
    _ = _ := by
      dsimp [B]
      ring

/-- The modulus average used after equations (25) and (29), placed here so
the source-order retained-frequency assembly can consume it directly. -/
private theorem sum_dfiEquation22Moduli_weil_gcd_divisor_average_le_early
    {Q : ℝ} (h : ℤ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        ((h.natAbs.divisors.card : ℝ) * Real.sqrt L *
          Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
  dsimp only
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ) =
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ _ := sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_le
      L h.natAbs (Int.natAbs_ne_zero.mpr hh) δ hδ

/-- DFI's published modulus average, uniform in the shift.  Unlike the
sparser optional estimate above, this is the form needed for Theorem 1's
error constant, which is independent of `h`. -/
theorem sum_dfiEquation22Moduli_weil_gcd_divisor_average_uniform_le
    {Q : ℝ} (h : ℤ) (δ : ℝ) (hδ : 0 < δ) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L := by
  dsimp only
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    (∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) =
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ _ := sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_uniform_le
      0 L h.natAbs δ hδ

/-- The unnormalized equation-(25) Weil factor acquires exactly one factor
`sqrt L` on the modulus range `q < L`.  This is the form produced after the
coprime cancellation of the two reduced Voronoi denominators. -/
theorem sum_dfiEquation22Moduli_weil_gcd_divisor_uniform_le
    {Q : ℝ} (h : ℤ) (δ : ℝ) (hδ : 0 < δ) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q,
        Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) ≤
      Real.sqrt L *
        (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L) := by
  dsimp only
  let L := ⌈2 * Q⌉₊
  have hterm (q : ℕ) (hqMem : q ∈ dfiEquation22Moduli Q) :
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ) ≤
        Real.sqrt L *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by
    have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
    have hqLt : q < L := by
      have hmem : q ∈ Finset.Ico 1 L := by
        rw [← dfiEquation22Moduli_eq_Ico]
        exact hqMem
      exact (Finset.mem_Ico.mp hmem).2
    letI : NeZero q := ⟨hqPos.ne'⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
    have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hqR
    have hsqrt : Real.sqrt q ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by exact_mod_cast hqLt.le)
    calc
      _ = Real.sqrt q *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by field_simp
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ q ∈ dfiEquation22Moduli Q,
        Real.sqrt L *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = Real.sqrt L *
        (∑ q ∈ dfiEquation22Moduli Q,
          (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      gcongr
      exact sum_dfiEquation22Moduli_weil_gcd_divisor_average_uniform_le h δ hδ

/-- Recombination of a pointwise unnormalized Weil estimate with the sharp
coprime equation-(25) modulus sum. -/
theorem sum_dfiEquation22Moduli_le_of_weil_uniform
    {Q : ℝ} (h : ℤ) (δ : ℝ) (hδ : 0 < δ)
    (F : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hPoint : ∀ q ∈ dfiEquation22Moduli Q,
      F q ≤ K * (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ))) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q, F q) ≤
      K * (Real.sqrt L *
        (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L)) := by
  dsimp only
  calc
    _ ≤ ∑ q ∈ dfiEquation22Moduli Q,
        K * (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hPoint q hq
    _ = K * (∑ q ∈ dfiEquation22Moduli Q,
        Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_dfiEquation22Moduli_weil_gcd_divisor_uniform_le h δ hδ) hK

/-- Abstract recombination of a pointwise normalized Weil estimate with the
uniform equation-(25) modulus average. -/
theorem sum_dfiEquation22Moduli_le_of_weil_average_uniform
    {Q : ℝ} (h : ℤ) (δ : ℝ) (hδ : 0 < δ)
    (F : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hPoint : ∀ q ∈ dfiEquation22Moduli Q,
      F q ≤ K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ))) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q, F q) ≤
      K * (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L) := by
  dsimp only
  calc
    _ ≤ ∑ q ∈ dfiEquation22Moduli Q,
        K * ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hPoint q hq
    _ = K * (∑ q ∈ dfiEquation22Moduli Q,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K * (divisorEpsilonConstant δ *
        max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) * ⌈2 * Q⌉₊) := by
      exact mul_le_mul_of_nonneg_left
        (sum_dfiEquation22Moduli_weil_gcd_divisor_average_uniform_le h δ hδ) hK

/-- Totalized retained `x`-dual Weil mass, so it can be summed over the
finite equation-(22) modulus set without carrying local typeclass binders. -/
noncomputable def dfiEquation29XSingleRetainedWeilTotal
    {Q : ℝ} (X : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ branch : DFIVoronoiDualBranch,
        ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖)

/-- The retained `x`-dual branches summed over all DFI moduli.  The entire
arithmetic dependence is now the sparse uniform Weil average, rather than
a pointwise `gcd ≤ q` loss. -/
theorem exists_sum_dfiEquation29_xSingle_retained_weil_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29XSingleLogMajorant Q Y b *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 2 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29XSingleLogMajorant Q Y b *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)
  have hlog : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
    have hXa : 0 ≤ X / (a : ℝ) :=
      div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg _)
    have hXPower : 0 ≤ (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg hXa _
    have hCutoffPower : 0 ≤
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hTwoC hXPower) hlog) hmass)
      hCutoffPower
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29XSingleRetainedWeilTotal X w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29XSingleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance hqQ
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- The retained `x`-dual branches summed with the shift-uniform DFI
equation-(25) estimate. -/
theorem exists_sum_dfiEquation29_xSingle_retained_weil_uniform_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29XSingleLogMajorant Q Y b *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 2 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29XSingleLogMajorant Q Y b *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)
  have hlog : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
    have hXa : 0 ≤ X / (a : ℝ) :=
      div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg _)
    have hXPower : 0 ≤ (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg hXa _
    have hCutoffPower : 0 ≤
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hTwoC hXPower) hlog) hmass)
      hCutoffPower
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29XSingleRetainedWeilTotal X w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29XSingleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance hqQ
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- The two retained `y`-dual signs after equation (25), normalized to the
same sparse shift-gcd average as the `x`-dual signs. -/
theorem exists_dfiEquation29_ySingleDual_source_retained_weil_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq0 : NeZero q),
      (q : ℝ) ≤ 2 * Q →
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (∑ branch : DFIVoronoiDualBranch,
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiVoronoiDualTerm qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
        2 * C * (Y / b) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29YSingleLogMajorant Q X a *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) *
          (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨C, hC, hRet⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * (Y / b) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29YSingleLogMajorant Q X a *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)
  have hlogq : |Real.log (qx : ℝ)| ≤ Real.log (2 * Q) := by
    exact (abs_log_dfiReducedModulus_denominator_le a q).trans
      (Real.log_le_log (by exact_mod_cast NeZero.pos q) hqQ)
  have hlog :
      |Real.log (X / a)| + |Real.log (2 * X / a)| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| ≤
        dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    linarith
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hEach (branch : DFIVoronoiDualBranch) :
      (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
        B * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ := by
    have hr := hRet q hq0 branch
    dsimp only [qx, qy, E] at hr
    have hprefix : 0 ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg qy) _))
          (Real.rpow_nonneg
            (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _))
        (inv_nonneg.mpr (Nat.cast_nonneg qx))
    calc
      _ ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := hr
      _ ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          dfiEquation29YSingleLogMajorant Q X a *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
        gcongr
      _ = B * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ := by
        dsimp [B]
        ring
  have hNorm := dfiEquation29_weil_mul_single_reduced_moduli_le
    q b a hab.symm h
  have hLogMajorant : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have hlogQ : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC
            (Real.rpow_nonneg
              (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _))
          hLogMajorant)
        hmass)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  change W * (∑ branch : DFIVoronoiDualBranch,
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤ _
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        B * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹) := by
      gcongr with branch
      exact hEach branch
    _ = 2 * B * (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ ≤ 2 * B * (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [W, qx, qy] using hNorm)
        (mul_nonneg (by norm_num) hB)
    _ = _ := by
      dsimp [B]
      ring

/-- Totalized retained `y`-dual Weil mass over one modulus. -/
noncomputable def dfiEquation29YSingleRetainedWeilTotal
    {Q : ℝ} (Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ branch : DFIVoronoiDualBranch,
        ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖)

/-- The retained `y`-dual branches summed over all DFI moduli. -/
theorem exists_sum_dfiEquation29_ySingle_retained_weil_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * C * (Y / b) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29YSingleLogMajorant Q X a *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 2 * C * (Y / b) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29YSingleLogMajorant Q X a *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)
  have hlog : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
    have hYPower : 0 ≤ (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _
    have hCutoffPower : 0 ≤
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hTwoC hYPower) hlog) hmass)
      hCutoffPower
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29YSingleRetainedWeilTotal Y w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29YSingleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance hqQ
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- The retained `y`-dual branches summed with the shift-uniform DFI
equation-(25) estimate. -/
theorem exists_sum_dfiEquation29_ySingle_retained_weil_uniform_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * C * (Y / b) ^ (-(1 / 4 : ℝ)) *
          dfiEquation29YSingleLogMajorant Q X a *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 2 * C * (Y / b) ^ (-(1 / 4 : ℝ)) *
    dfiEquation29YSingleLogMajorant Q X a *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)
  have hlog : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hTwoC : 0 ≤ 2 * C := mul_nonneg (by norm_num) hC
    have hYPower : 0 ≤ (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _
    have hCutoffPower : 0 ≤
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hTwoC hYPower) hlog) hmass)
      hCutoffPower
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29YSingleRetainedWeilTotal Y w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29YSingleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance hqQ
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- The four retained double-dual sign pairs after equation (25), with the
two reduced moduli normalized to the uniform shift-gcd average. -/
theorem exists_dfiEquation29_doubleDual_source_retained_weil_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq0 : NeZero q),
      let qx := (dfiReducedModulus a q).denominator
      let qy := (dfiReducedModulus b q).denominator
      let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (∑ xBranch : DFIVoronoiDualBranch,
          ∑ yBranch : DFIVoronoiDualBranch,
            ∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
              ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
                ‖dfiEquation24DoubleDualMellinAmplitude
                  qx xBranch qy yBranch E m n‖) ≤
        4 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨C, hC, hRet⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro q hq0
  dsimp only
  letI : NeZero q := hq0
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2)
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hC
              (Real.rpow_nonneg
                (div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)) _))
            (Real.rpow_nonneg
              (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _))
          hmass)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hEach (xBranch yBranch : DFIVoronoiDualBranch) :
      (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤
        B * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hr := hRet q hq0 xBranch yBranch
    dsimp only [qx, qy, E] at hr
    dsimp [B, qx, qy, E]
    convert hr using 1
    ring
  have hNorm := dfiEquation29_weil_mul_double_reduced_moduli_le
    q a b hab h
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  change W * (∑ xBranch : DFIVoronoiDualBranch,
      ∑ yBranch : DFIVoronoiDualBranch,
        ∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤ _
  calc
    _ ≤ W * (∑ _xBranch : DFIVoronoiDualBranch,
        ∑ _yBranch : DFIVoronoiDualBranch,
          B * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply Finset.sum_le_sum
      intro xBranch _
      apply Finset.sum_le_sum
      intro yBranch _
      exact hEach xBranch yBranch
    _ = 4 * B * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ ≤ 4 * B * (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [W, qx, qy] using hNorm)
        (mul_nonneg (by norm_num) hB)
    _ = _ := by
      dsimp [B]
      ring

/-- Totalized retained double-dual Weil mass over one modulus. -/
noncomputable def dfiEquation29DoubleRetainedWeilTotal
    {Q : ℝ} (X Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ xBranch : DFIVoronoiDualBranch,
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
            ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
              ‖dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m n‖)

/-- The retained double-dual rectangle summed over all DFI moduli. -/
theorem exists_sum_dfiEquation29_double_retained_weil_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (4 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
            (3 / 4 + ε / 2)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 4 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2)
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hFourC : 0 ≤ 4 * C := mul_nonneg (by norm_num) hC
    have hXPower : 0 ≤ (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)) _
    have hYPower : 0 ≤ (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _
    have hXCut : 0 ≤
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hYCut : 0 ≤
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h₁ : 0 ≤ (4 * C) * (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      mul_nonneg hFourC hXPower
    have h₂ : 0 ≤ (4 * C) * (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) := mul_nonneg h₁ hYPower
    have h₃ : 0 ≤ (4 * C) * (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) := mul_nonneg h₂ hmass
    have h₄ : 0 ≤ (4 * C) * (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      mul_nonneg h₃ hXCut
    have h₅ : 0 ≤ (4 * C) * (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      mul_nonneg h₄ hYCut
    exact h₅
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29DoubleRetainedWeilTotal X Y w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29DoubleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- The retained double-dual rectangle summed over all DFI moduli with the
published shift-uniform equation-(25) estimate. -/
theorem exists_sum_dfiEquation29_double_retained_weil_uniform_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (4 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
            (3 / 4 + ε / 2) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
            (3 / 4 + ε / 2)) *
        (Real.sqrt ⌈2 * Q⌉₊ *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            ⌈2 * Q⌉₊)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_weil_bound
      hf hbox hφ hscale w hQ hU a b ha hb hab h ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  let K : ℝ := 4 * C * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) *
    (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2)
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hmin : 0 ≤ min X Y :=
      le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hFourC : 0 ≤ 4 * C := mul_nonneg (by norm_num) hC
    have hXPower : 0 ≤ (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)) _
    have hYPower : 0 ≤ (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)) _
    have hXCut : 0 ≤
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hYCut : 0 ≤
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hFourC hXPower) hYPower) hmass) hXCut) hYCut
  apply sum_dfiEquation22Moduli_le_of_weil_uniform
    h δ hδ
      (fun q ↦ dfiEquation29DoubleRetainedWeilTotal X Y w
        (dfiLocalizedWeight f φ h) a b h ε q) K hK
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  letI : NeZero q := ⟨hqPos.ne'⟩
  rw [dfiEquation29DoubleRetainedWeilTotal, dif_neg hqPos.ne']
  have hp := hPoint q inferInstance
  dsimp only at hp
  simpa only [K, mul_assoc] using hp

/-- Source-order copy of the exact retained mass, introduced before the
later general equation-(29) API so the sharp DFI assembly can use it. -/
private noncomputable def dfiVoronoiDualMassUpToEarly
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖

/-- Source-order copy of the complementary equation-(29) tail mass. -/
private noncomputable def dfiVoronoiDualMassAfterEarly
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖

private theorem dfiVoronoiDualMassUpToEarly_add_after
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) :
    dfiVoronoiDualMassUpToEarly q branch g L +
        dfiVoronoiDualMassAfterEarly q branch g L =
      ∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖ := by
  let F : ℕ → ℝ := fun n ↦ ‖dfiVoronoiDualTerm q branch g n‖
  have hF : Summable F := summable_norm_dfiVoronoiDualTerm q branch g
  have hSplit := hF.sum_add_tsum_nat_add (L + 1)
  have hFinite : ∑ n ∈ Finset.range (L + 1), F n =
      dfiVoronoiDualMassUpToEarly q branch g L := by
    unfold dfiVoronoiDualMassUpToEarly
    rw [show Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) by
      ext n
      simp
      omega]
    simp [F]
  have hTail : (∑' j : ℕ, F (j + (L + 1))) =
      dfiVoronoiDualMassAfterEarly q branch g L := by
    unfold dfiVoronoiDualMassAfterEarly
    apply tsum_congr
    intro j
    rw [show j + (L + 1) = L + (j + 1) by omega]
  rw [hFinite, hTail] at hSplit
  simpa only [F] using hSplit

/-- Totalized complementary `x`-dual tail after the literal source cutoff
in equation (29). -/
noncomputable def dfiEquation29XSingleTailWeilTotal
    {Q : ℝ} (X : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ branch : DFIVoronoiDualBranch,
        dfiVoronoiDualMassAfterEarly qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (dfiEquation29SourceXCutoff a X Q ε))

/-- Totalized complementary `y`-dual tail after the literal source cutoff
in equation (29). -/
noncomputable def dfiEquation29YSingleTailWeilTotal
    {Q : ℝ} (Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ branch : DFIVoronoiDualBranch,
        dfiVoronoiDualMassAfterEarly qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (dfiEquation29SourceYCutoff b Y Q ε))

/-- Exact equation-(29) split of the complete two-sign `x`-dual mass. -/
theorem dfiEquation24XSingleDualMass_weil_eq_retained_add_tail
    {Q : ℝ} (X : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b q : ℕ) [NeZero q] (h : ℤ) (ε : ℝ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        dfiEquation24XSingleDualMass q a b
          (dfiEquation23Weight w F a b h q) =
      dfiEquation29XSingleRetainedWeilTotal X w F a b h ε q +
        dfiEquation29XSingleTailWeilTotal X w F a b h ε q := by
  have hq : q ≠ 0 := NeZero.ne q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w F a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let L := dfiEquation29SourceXCutoff a X Q ε
  calc
    W * dfiEquation24XSingleDualMass q a b E =
        W * (∑ branch : DFIVoronoiDualBranch,
          (dfiVoronoiDualMassUpToEarly qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) L +
            dfiVoronoiDualMassAfterEarly qx branch
              (fun x ↦ dfiVoronoiMainTerm qy (E x)) L)) := by
      unfold dfiEquation24XSingleDualMass
      congr 1
      apply Finset.sum_congr rfl
      intro branch _
      exact (dfiVoronoiDualMassUpToEarly_add_after qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) L).symm
    _ = W * (∑ branch : DFIVoronoiDualBranch,
          dfiVoronoiDualMassUpToEarly qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) L) +
        W * (∑ branch : DFIVoronoiDualBranch,
          dfiVoronoiDualMassAfterEarly qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) L) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = _ := by
      rw [dfiEquation29XSingleRetainedWeilTotal,
        dfiEquation29XSingleTailWeilTotal, dif_neg hq, dif_neg hq]
      rfl

/-- Exact equation-(29) split of the complete two-sign `y`-dual mass. -/
theorem dfiEquation24YSingleDualMass_weil_eq_retained_add_tail
    {Q : ℝ} (Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b q : ℕ) [NeZero q] (h : ℤ) (ε : ℝ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        dfiEquation24YSingleDualMass q a b
          (dfiEquation23Weight w F a b h q) =
      dfiEquation29YSingleRetainedWeilTotal Y w F a b h ε q +
        dfiEquation29YSingleTailWeilTotal Y w F a b h ε q := by
  have hq : q ≠ 0 := NeZero.ne q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w F a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let L := dfiEquation29SourceYCutoff b Y Q ε
  calc
    W * dfiEquation24YSingleDualMass q a b E =
        W * (∑ branch : DFIVoronoiDualBranch,
          (dfiVoronoiDualMassUpToEarly qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L +
            dfiVoronoiDualMassAfterEarly qy branch
              (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L)) := by
      unfold dfiEquation24YSingleDualMass
      congr 1
      apply Finset.sum_congr rfl
      intro branch _
      exact (dfiVoronoiDualMassUpToEarly_add_after qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L).symm
    _ = W * (∑ branch : DFIVoronoiDualBranch,
          dfiVoronoiDualMassUpToEarly qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L) +
        W * (∑ branch : DFIVoronoiDualBranch,
          dfiVoronoiDualMassAfterEarly qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = _ := by
      rw [dfiEquation29YSingleRetainedWeilTotal,
        dfiEquation29YSingleTailWeilTotal, dif_neg hq, dif_neg hq]
      rfl

/-- Exact equation-(29) retained window. -/
noncomputable def dfiVoronoiDualMassUpTo
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖

/-- Exact equation-(29) tail beyond the retained window. -/
noncomputable def dfiVoronoiDualMassAfter
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖

/-- Exact integer cutoff for the transition in DFI (29).  Here `S` is the
physical support scale and `R` is the harmless source power. -/
noncomputable def dfiEquation29RetainedCutoff
    (q : ℕ) (S R : ℝ) : ℕ :=
  ⌈(q : ℝ) ^ 2 / S * R⌉₊

theorem dfiEquation29RetainedCutoff_pos
    (q : ℕ) [NeZero q] {S R : ℝ} (hS : 0 < S) (hR : 0 < R) :
    0 < dfiEquation29RetainedCutoff q S R := by
  have hTransition : 0 < (q : ℝ) ^ 2 / S * R := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  unfold dfiEquation29RetainedCutoff
  exact Nat.ceil_pos.mpr hTransition

theorem dfiEquation29_transition_le_retainedCutoff
    (q : ℕ) {S R : ℝ} :
    (q : ℝ) ^ 2 / S * R ≤ dfiEquation29RetainedCutoff q S R := by
  unfold dfiEquation29RetainedCutoff
  exact Nat.le_ceil _

/-- The exact integer window differs from DFI's real transition scale by
less than one.  This is the rounding estimate needed when the retained
frequency count is converted back to the source powers of `Q`. -/
theorem dfiEquation29RetainedCutoff_lt_transition_add_one
    (q : ℕ) {S R : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R) :
    (dfiEquation29RetainedCutoff q S R : ℝ) <
      (q : ℝ) ^ 2 / S * R + 1 := by
  unfold dfiEquation29RetainedCutoff
  exact Nat.ceil_lt_add_one hTransition

/-- Weak form of the preceding estimate, convenient under monotone real
powers. -/
theorem dfiEquation29RetainedCutoff_le_transition_add_one
    (q : ℕ) {S R : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R) :
    (dfiEquation29RetainedCutoff q S R : ℝ) ≤
      (q : ℝ) ^ 2 / S * R + 1 :=
  (dfiEquation29RetainedCutoff_lt_transition_add_one q hTransition).le

/-- Monotone-power form of the exact rounding estimate. -/
theorem dfiEquation29RetainedCutoff_rpow_le
    (q : ℕ) {S R α : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R)
    (hα : 0 ≤ α) :
    (dfiEquation29RetainedCutoff q S R : ℝ) ^ α ≤
      ((q : ℝ) ^ 2 / S * R + 1) ^ α := by
  exact Real.rpow_le_rpow
    (Nat.cast_nonneg (dfiEquation29RetainedCutoff q S R))
    (dfiEquation29RetainedCutoff_le_transition_add_one q hTransition) hα

/-- Passing to the reduced additive-character modulus does not enlarge the
equation-(29) transition. -/
theorem dfiEquation29_reduced_transition_le_original
    (a q : ℕ) [NeZero q] {S R : ℝ} (hS : 0 < S) (hR : 0 ≤ R) :
    ((dfiReducedModulus a q).denominator : ℝ) ^ 2 / S * R ≤
      (q : ℝ) ^ 2 / S * R := by
  have hden : ((dfiReducedModulus a q).denominator : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hdenNonneg : (0 : ℝ) ≤ (dfiReducedModulus a q).denominator := by
    positivity
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hsquare : ((dfiReducedModulus a q).denominator : ℝ) ^ 2 ≤
      (q : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hsquare hS.le) hR

/-- Under the delta-method support `q ≤ 2Q`, the reduced transition is at
most the literal source scale `4 Q²/S`, before inserting the harmless
`Q^ε` enlargement. -/
theorem dfiEquation29_reduced_transition_le_four_mul
    (a q : ℕ) [NeZero q] {S R Q : ℝ} (hS : 0 < S) (hR : 0 ≤ R)
    (hQ : 0 ≤ Q) (hqQ : (q : ℝ) ≤ 2 * Q) :
    ((dfiReducedModulus a q).denominator : ℝ) ^ 2 / S * R ≤
      4 * Q ^ 2 / S * R := by
  refine (dfiEquation29_reduced_transition_le_original a q hS hR).trans ?_
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hsquare : (q : ℝ) ^ 2 ≤ 4 * Q ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hsquare hS.le) hR

/-- Summed retained-frequency bound from the right-shifted equation-(29)
contour. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassUpTo_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassUpTo q branch g L ≤
        C * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_retained_bound S hS branch
  refine ⟨(4 / 3 : ℝ) * A, by positivity, ?_⟩
  intro q L hq
  letI : NeZero q := hq
  have hScale : 0 ≤ A * S ^ (1 / 2 : ℝ) :=
    mul_nonneg hA (Real.rpow_nonneg hS.le _)
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L,
          A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc : n ∈ Finset.Icc 1 L := by simpa using hn
      exact hPoint q hq n (by
        have := (Finset.mem_Icc.mp hnIcc).1
        omega)
    _ = (A * S ^ (1 / 2 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (A * S ^ (1 / 2 : ℝ)) *
        ((4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_natCast_rpow_neg_quarter_le L) hScale
    _ = ((4 / 3 : ℝ) * A) * S ^ (1 / 2 : ℝ) *
        (L : ℝ) ^ (3 / 4 : ℝ) := by ring

/-- Source-strength retained mass from the `Re z = 3/4` contour. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassUpTo_threeQuarter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassUpTo q branch g L ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
          (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_threeQuarter_bound
      S hS ε hε₀ branch
  let cε : ℝ := (3 / 4 + ε)⁻¹
  have hcε : 0 ≤ cε := by
    dsimp [cε]
    positivity
  refine ⟨cε * A, mul_nonneg hcε hA, ?_⟩
  intro q L hq
  letI : NeZero q := hq
  have hScale : 0 ≤ A * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
      S ^ (3 / 4 : ℝ) := by positivity
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L,
          A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
            (n : ℝ) ^ (ε - 1 / 4) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hPoint q hq n (by
        have hnIcc := (Finset.mem_Icc.mp hn).1
        omega)
    _ = (A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (ε - 1 / 4) := by
      rw [Finset.mul_sum]
    _ ≤ (A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        (cε * (L : ℝ) ^ (3 / 4 + ε)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [cε] using
          sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε L)
        hScale
    _ = (cε * A) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
        (L : ℝ) ^ (3 / 4 + ε) := by ring

/-- Universal passage from a source-normalized three-quarter-line transform
bound to its retained divisor-weighted mass. -/
theorem exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq : NeZero q) (branch : DFIVoronoiDualBranch)
        (g : ℝ → ℂ) (K B : ℝ),
        (∀ n : ℕ, 0 < n →
          ‖dfiEquation29InitialTransform q branch g n‖ ≤
            K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
              (n : ℝ) ^ (-(1 / 4 : ℝ))) →
        ∀ L : ℕ,
          dfiVoronoiDualMassUpTo q branch g L ≤
            C * K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε₀
  let cε : ℝ := (3 / 4 + ε)⁻¹
  have hcε : 0 ≤ cε := by dsimp [cε]; positivity
  refine ⟨cε * D, mul_nonneg hcε hD.le, ?_⟩
  intro q hq branch g K B hTransform L
  letI : NeZero q := hq
  let R : ℝ := K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B
  have hR : 0 ≤ R := by
    have hOne := hTransform 1 (by omega)
    have hnonneg : 0 ≤ ‖dfiEquation29InitialTransform q branch g 1‖ := norm_nonneg _
    dsimp [R]
    norm_num at hOne
    exact hnonneg.trans hOne
  have hPoint (n : ℕ) (hn : 0 < n) :
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        D * R * (n : ℝ) ^ (ε - 1 / 4) := by
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
    have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
      simpa [divisorWeight] using hDivisor n hn
    have hTransform' := hTransform n hn
    calc
      ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
          (D * (n : ℝ) ^ ε) *
            (R * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
        exact mul_le_mul hWeight (by simpa [R, mul_assoc] using hTransform')
          (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      _ = D * R * (n : ℝ) ^ (ε - 1 / 4) := by
        calc
          (D * (n : ℝ) ^ ε) * (R * (n : ℝ) ^ (-(1 / 4 : ℝ))) =
              (D * R) * ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
          _ = (D * R) * (n : ℝ) ^ (ε + (-(1 / 4 : ℝ))) := by
            rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
          _ = D * R * (n : ℝ) ^ (ε - 1 / 4) := by ring
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L, D * R * (n : ℝ) ^ (ε - 1 / 4) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hPoint n (by
        have hnIcc := (Finset.mem_Icc.mp hn).1
        omega)
    _ = (D * R) * ∑ n ∈ Finset.Icc 1 L,
        (n : ℝ) ^ (ε - 1 / 4) := by rw [Finset.mul_sum]
    _ ≤ (D * R) * (cε * (L : ℝ) ^ (3 / 4 + ε)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [cε] using
          sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε L)
        (mul_nonneg hD.le hR)
    _ = (cε * D) * K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
        (L : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R]
      ring

/-- DFI's literal `Y₀/K₀` estimate inserted into the retained
frequency summation.  Unlike the earlier contour majorant, the source
dependence here is exactly the physical quarter-weighted mass. -/
theorem exists_dfiVoronoiDualMassUpTo_le_of_besselQuarterNorm
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq : NeZero q) (branch : DFIVoronoiDualBranch)
        (g : ℝ → ℂ) (_hg : DFIVoronoiTestFunction g) (L : ℕ),
          dfiVoronoiDualMassUpTo q branch g L ≤
            C * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
              dfiBesselQuarterBaseNorm g * (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨A, hA, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  let K : ℝ := 14 * Real.pi + 8
  refine ⟨A * K, mul_nonneg hA (by dsimp [K]; positivity), ?_⟩
  intro q hq branch g hg L
  letI : NeZero q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqScale : (Real.sqrt q)⁻¹ =
      (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hqR.le]
  have hTransform (n : ℕ) (hn : 0 < n) :
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        K * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          dfiBesselQuarterBaseNorm g * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hPhysical :=
      hg.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
        q branch hn (hg.integrableOn_besselQuarterWeight_mul_nat n hn)
    rw [dfiBesselQuarterNorm_eq_rpow_mul_base g n hn,
      div_eq_mul_inv, hqScale] at hPhysical
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hPhysical
  have hBound := hMass q inferInstance branch g K
    (dfiBesselQuarterBaseNorm g) hTransform L
  simpa [K, mul_assoc, mul_left_comm, mul_comm] using hBound

/-- Retained frequencies in the x-dual/y-main branch, with the source
equation-(30) mass inserted. -/
theorem exists_dfiEquation24_xSingleDualRetained_physical_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (h : ℤ) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        ∀ (branch : DFIVoronoiDualBranch) (L : ℕ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        dfiVoronoiDualMassUpTo qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) L ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiEquation29MixedPhysicalMajorant K Q X Y a b qy *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hRetained⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_besselQuarterNorm
      ε hε₀ hε
  obtain ⟨K, hK, hBessel⟩ :=
    exists_dfiEquation24_xMixedPhysicalBesselBase_bound
      hf hbox hφ hscale w hQ hU h
  refine ⟨C, K, hC, hK, ?_⟩
  intro a b q hq0 ha hb branch L
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hg : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) := by
    exact dfiVoronoiMainTermSecondFamilyTestFunction hE
      (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
      ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
      (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
      hSupport qy
  have hBase := hBessel a b q qy ha hb hq hqy
  have hRaw := hRetained qx inferInstance branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) hg L
  have hFactor : 0 ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) := by
    positivity
  calc
    dfiVoronoiDualMassUpTo qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) L ≤
      C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) *
            (L : ℝ) ^ (3 / 4 + ε) := hRaw
    _ ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiEquation29MixedPhysicalMajorant K Q X Y a b qy *
          (L : ℝ) ^ (3 / 4 + ε) := by
      have hScaled := mul_le_mul_of_nonneg_left hBase hFactor
      exact mul_le_mul_of_nonneg_right hScaled
        (Real.rpow_nonneg (Nat.cast_nonneg L) _)

/-- Retained frequencies in the symmetric x-main/y-dual branch, with the
same source equation-(30) mass inserted. -/
theorem exists_dfiEquation24_ySingleDualRetained_physical_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (h : ℤ) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        ∀ (branch : DFIVoronoiDualBranch) (L : ℕ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        dfiVoronoiDualMassUpTo qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L ≤
          C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            dfiEquation29MixedPhysicalMajorant K Q Y X b a qx *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hRetained⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_besselQuarterNorm
      ε hε₀ hε
  obtain ⟨K, hK, hBessel⟩ :=
    exists_dfiEquation24_yMixedPhysicalBesselBase_bound
      hf hbox hφ hscale w hQ hU h
  refine ⟨C, K, hC, hK, ?_⟩
  intro a b q hq0 ha hb branch L
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hg : DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
    exact dfiVoronoiMainTermFamilyTestFunction hE
      (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
      (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
      ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
      hSupport qx
  have hBaseRaw := hBessel a b q qx ha hb hq hqx
  have hBase :
      dfiBesselQuarterBaseNorm
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) ≤
        dfiEquation29MixedPhysicalMajorant K Q Y X b a qx := by
    simpa only [E, dfiEquation29MixedPhysicalMajorant, min_comm,
      mul_comm] using hBaseRaw
  have hRaw := hRetained qy inferInstance branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) hg L
  have hFactor : 0 ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) := by
    positivity
  calc
    dfiVoronoiDualMassUpTo qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L ≤
      C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiBesselQuarterBaseNorm
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) *
            (L : ℝ) ^ (3 / 4 + ε) := hRaw
    _ ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        dfiEquation29MixedPhysicalMajorant K Q Y X b a qx *
          (L : ℝ) ^ (3 / 4 + ε) := by
      have hScaled := mul_le_mul_of_nonneg_left hBase hFactor
      exact mul_le_mul_of_nonneg_right hScaled
        (Real.rpow_nonneg (Nat.cast_nonneg L) _)

/-- Absolute convergence decomposes the complete transformed mass exactly
into DFI's retained frequencies `1 ≤ n ≤ L` and the tail `n > L`. -/
theorem dfiVoronoiDualMassUpTo_add_after
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) :
    dfiVoronoiDualMassUpTo q branch g L +
        dfiVoronoiDualMassAfter q branch g L =
      ∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖ := by
  let F : ℕ → ℝ := fun n ↦ ‖dfiVoronoiDualTerm q branch g n‖
  have hF : Summable F := summable_norm_dfiVoronoiDualTerm q branch g
  have hSplit := hF.sum_add_tsum_nat_add (L + 1)
  have hFinite : ∑ n ∈ Finset.range (L + 1), F n =
      dfiVoronoiDualMassUpTo q branch g L := by
    unfold dfiVoronoiDualMassUpTo
    rw [show Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) by
      ext n
      simp
      omega]
    simp [F]
  have hTail : (∑' j : ℕ, F (j + (L + 1))) =
      dfiVoronoiDualMassAfter q branch g L := by
    unfold dfiVoronoiDualMassAfter
    apply tsum_congr
    intro j
    rw [show j + (L + 1) = L + (j + 1) by omega]
  rw [hFinite, hTail] at hSplit
  simpa only [F] using hSplit

/-- Quantitative equation-(29) tail for an arbitrary admissible test
function, expressed using the exact tail object above. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassAfter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      dfiVoronoiDualMassAfter q branch g L ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  simpa only [dfiVoronoiDualMassAfter] using
    hg.exists_dfiVoronoiDualTerm_tail_scaled_decay S hS k hk branch

/-- Equation-(29) tail evaluated at its exact retained cutoff. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassAfter_cutoff_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassAfter q branch g
          (dfiEquation29RetainedCutoff q S R) ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ :=
    hg.exists_dfiVoronoiDualTerm_tail_of_transition S hS k hk branch
  refine ⟨C, hC, ?_⟩
  intro q hq
  letI : NeZero q := hq
  have hL : 0 < dfiEquation29RetainedCutoff q S R :=
    dfiEquation29RetainedCutoff_pos q hS (lt_of_lt_of_le zero_lt_one hR)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  simpa only [dfiVoronoiDualMassAfter] using
    hTail q (dfiEquation29RetainedCutoff q S R) hq R hL hRpos
      (dfiEquation29_transition_le_retainedCutoff q)

/-- Full one-variable Voronoi mass split at an arbitrary positive retained
window.  The first term is the right-contour estimate and the second is the
arbitrary-order left-contour tail. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMass_split_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      (∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖) ≤
        A * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) +
        B * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A, hA, hRetained⟩ := hg.exists_dfiVoronoiDualMassUpTo_le S hS branch
  obtain ⟨B, hB, hTail⟩ := hg.exists_dfiVoronoiDualMassAfter_le S hS k hk branch
  refine ⟨A, B, hA, hB, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  rw [← dfiVoronoiDualMassUpTo_add_after q branch g L]
  exact add_le_add (hRetained q L hq) (hTail q L hq hL)

/-- Complete divisor-weighted Voronoi mass from the two literal Mellin
contours used in DFI (29).  The right contour controls the retained window;
the arbitrarily deep left contour controls its complement. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMass_le_of_mellin_bounds
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch)
    {B₃ Bk : ℝ}
    (h₃ : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃)
    (hkLine : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
        (∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖) ≤
          A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B₃ *
              (L : ℝ) ^ (3 / 4 + ε) +
            D * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * Bk *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hRetainedFromTransform⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  have hB₃ : 0 ≤ B₃ := by
    have h := h₃ 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans h
  have hBk : 0 ≤ Bk := by
    have h := hkLine 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans h
  have hInitial := hTransform hg h₃ q hq
  have hRetained := hRetainedFromTransform q hq branch g A₁ B₃
    hInitial L
  have hAfter := hTail hg hBk hkLine q L hq hL
  rw [← dfiVoronoiDualMassUpTo_add_after q branch g L]
  exact add_le_add (by simpa [mul_assoc] using hRetained) hAfter

/-- Retained first-variable frequencies for the literal equation-(23)
source weight, with physical scale `X/a`. -/
theorem exists_dfiEquation29_xSlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) L ≤
        C * (X / a) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiVoronoiDualMassUpTo_le (X / a) hScale branch

/-- Retained second-variable frequencies for the literal equation-(23)
source weight, with physical scale `Y/b`. -/
theorem exists_dfiEquation29_ySlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) L ≤
        C * (Y / b) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiVoronoiDualMassUpTo_le (Y / b) hScale branch

/-- Source-uniform retained first-variable mass on the three-quarter
contour, including the divisor-function loss `ε`. -/
theorem exists_dfiEquation29_xSlice_retained_mass_threeQuarter
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (hUQ : U = Q ^ 2) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (r : ℕ) (_hr : NeZero r) (L : ℕ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        dfiVoronoiDualMassUpTo r branch
            (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x y) L ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨M, hM, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨K, hK, C, hC, hTransform⟩ :=
    exists_dfiEquation29_xSlice_threeQuarter_transform_bound
      hf hbox hφ hscale w hUQ branch
  refine ⟨M * K, mul_nonneg hM hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r hr L
  dsimp only
  have hApply := hMass r hr branch
    (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
      a b h q x y) K
    ((1 + 2 * Real.pi) ^ 6 *
      (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
        (max 1 (2 * X / a) *
            ((∑ i ∈ Finset.range 7, C i) * ((q : ℝ) * Q)⁻¹) +
          max 1 (2 * X / a) *
            (1024 * ((∑ i ∈ Finset.range 7, C i) * ((q : ℝ) * Q)⁻¹) *
              (1 + max 1 (2 * X / a) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^ 6))))
    (hTransform a b q ha hb hq hqQ h y r hr) L
  simpa [mul_assoc] using hApply

/-- Source-uniform retained second-variable mass, symmetric to the preceding
first-variable theorem. -/
theorem exists_dfiEquation29_ySlice_retained_mass_threeQuarter
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (hUQ : U = Q ^ 2) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (r : ℕ) (_hr : NeZero r) (L : ℕ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        dfiVoronoiDualMassUpTo r branch
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x) L ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨M, hM, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨K, hK, C, hC, hTransform⟩ :=
    exists_dfiEquation29_ySlice_threeQuarter_transform_bound
      hf hbox hφ hscale w hUQ branch
  refine ⟨M * K, mul_nonneg hM hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r hr L
  dsimp only
  have hApply := hMass r hr branch
    (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x) K
    ((1 + 2 * Real.pi) ^ 6 *
      (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
        (max 1 (2 * Y / b) *
            ((∑ j ∈ Finset.range 7, C j) * ((q : ℝ) * Q)⁻¹) +
          max 1 (2 * Y / b) *
            (1024 * ((∑ j ∈ Finset.range 7, C j) * ((q : ℝ) * Q)⁻¹) *
              (1 + max 1 (2 * Y / b) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^ 6))))
    (hTransform a b q ha hb hq hqQ h x r hr) L
  simpa [mul_assoc] using hApply

/-- The literal source majorant produced by equation (28) after a logarithmic
Voronoi main operator is applied in the other variable.  `S/c` is the Mellin
variable's physical scale and `R/d` is the interval integrated by the main
operator. -/
noncomputable def dfiEquation28MixedMajorant
    (C : ℕ → ℝ) (p : ℕ) (σ Q S R : ℝ)
    (a b q qMain c d : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1), C i
  let qQ := (q : ℝ) * Q
  let A := Csum * qQ⁻¹
  let B := ((a : ℝ) * (b : ℝ)) / qQ
  let D := max 1 (max (2 * S / c) (S / c)⁻¹)
  dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
    ((1 + 2 * Real.pi) ^ p *
      ((2 : ℝ) ^ p *
        ((-Real.log (S / c)) - (-Real.log (2 * S / c))) *
        (D ^ |σ| * A +
          D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p))))

/-- Sign-sensitive mixed-branch majorant on a nonpositive Mellin line. -/
noncomputable def dfiEquation28NonposMixedMajorant
    (C : ℕ → ℝ) (p : ℕ) (σ Q S R : ℝ)
    (a b q qMain c d : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1), C i
  let qQ := (q : ℝ) * Q
  let A := Csum * qQ⁻¹
  let B := ((a : ℝ) * (b : ℝ)) / qQ
  dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
    dfiMellinNonposProfileMajorant (S / c) (2 * S / c) σ p A B

/-- The equation-(29) mixed-branch majorant retaining the derivative scale
of the Mellin variable.  For an `x` transform `c = a`; for a `y` transform
`c = b`.  This is the uncoarsened equation-(28) estimate. -/
noncomputable def dfiEquation28SeparatedNonposMixedMajorant
    (C : ℕ → ℝ) (p : ℕ) (σ Q S R : ℝ)
    (q qMain c d : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1), C i
  let qQ := (q : ℝ) * Q
  let A := Csum * qQ⁻¹
  let B := (c : ℝ) / qQ
  dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
    dfiMellinNonposProfileMajorant (S / c) (2 * S / c) σ p A B

/-- Source-uniform all-orders Mellin estimate for the `x`-dual/`y`-main
mixed branch of DFI (24).  This is not a separately assumed mixed estimate:
it is obtained by commuting the actual Mellin transform with the actual
logarithmic main term and inserting equation (28) for every source slice. -/
theorem exists_dfiEquation28_xMellin_yMain_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
            (D ^ |σ| * A +
              D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p)))
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiVoronoiMainIntervalNorm qy (Y / b) (2 * Y / b) * M := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_xSlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h u
  dsimp only
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hXA hYC hYCD hSupport qy hqy
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun y _hy ↦ hRaw a b q ha hb hq hqQ h y u)
  simpa only [E, dfiVoronoiMainIntervalNorm] using hMixed

/-- Source-uniform mixed `x`-Mellin/`y`-main estimate with the negative-line
source scale retained. -/
theorem exists_dfiEquation28_xMellin_yMain_nonpos_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28NonposMixedMajorant C p σ Q X Y
            a b q qy a b := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_xSlice_mellin_nonpos_line_bound_order
      hf hbox hφ hscale w hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h u
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hXA hYC hYCD hSupport qy hqy
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun y _hy ↦ hRaw a b q ha hb hq hqQ h y u)
  simpa only [E, dfiEquation28NonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- Symmetric source-uniform all-orders Mellin estimate for the
`x`-main/`y`-dual mixed branch of DFI (24). -/
theorem exists_dfiEquation28_yMellin_xMain_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
            (D ^ |σ| * A +
              D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p)))
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiVoronoiMainIntervalNorm qx (X / a) (2 * X / a) * M := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_ySlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h u
  dsimp only
  let E : ℝ → ℝ → ℂ := fun y x ↦
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x y
  have hSource : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    simpa only [E, Function.uncurry_apply_pair] using hSource.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSourceSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
        Set.Icc (X / a) (2 * X / a) ×ˢ
          Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSourceSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q)) by
      simpa only [E, Function.mem_support,
        Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hXC : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXCD : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hYA hXC hXCD hSupport qx hqx
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun x _hx ↦ hRaw a b q ha hb hq hqQ h x u)
  simpa only [E, dfiVoronoiMainIntervalNorm] using hMixed

/-- Symmetric source-uniform mixed estimate with the negative-line source
scale retained. -/
theorem exists_dfiEquation28_yMellin_xMain_nonpos_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28NonposMixedMajorant C p σ Q Y X
            a b q qx b a := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_ySlice_mellin_nonpos_line_bound_order
      hf hbox hφ hscale w hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h u
  let E : ℝ → ℝ → ℂ := fun y x ↦
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x y
  have hSource : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    simpa only [E, Function.uncurry_apply_pair] using hSource.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSourceSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
        Set.Icc (X / a) (2 * X / a) ×ˢ
          Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSourceSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q)) by
      simpa only [E, Function.mem_support,
        Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hXC : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXCD : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hYA hXC hXCD hSupport qx hqx
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun x _hx ↦ hRaw a b q ha hb hq hqQ h x u)
  simpa only [E, dfiEquation28NonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- The mixed `x`-dual/`y`-main line bound with the uncoarsened `x`
derivative scale retained. -/
theorem exists_dfiEquation28_xMellin_yMain_nonpos_separated_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28SeparatedNonposMixedMajorant C p σ Q X Y
            q qy a b := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_xSlice_mellin_nonpos_separated_line_bound_order
      hf hbox hφ hscale w hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h u
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hXA hYC hYCD hSupport qy hqy
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun y _hy ↦ hRaw a b q ha hb hq hqQ h y u)
  simpa only [E, dfiEquation28SeparatedNonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- Symmetric mixed bound with the uncoarsened `y` derivative scale. -/
theorem exists_dfiEquation28_yMellin_xMain_nonpos_separated_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28SeparatedNonposMixedMajorant C p σ Q Y X
            q qx b a := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_ySlice_mellin_nonpos_separated_line_bound_order
      hf hbox hφ hscale w hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h u
  let E : ℝ → ℝ → ℂ := fun y x ↦
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x y
  have hSource : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    simpa only [E, Function.uncurry_apply_pair] using hSource.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSourceSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
        Set.Icc (X / a) (2 * X / a) ×ˢ
          Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro z hz
    have hm := hSourceSupport (show
      (z.2, z.1) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q)) by
      simpa only [E, Function.mem_support,
        Function.uncurry_apply_pair] using hz)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hXC : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXCD : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hYA hXC hXCD hSupport qx hqx
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun x _hx ↦ hRaw a b q ha hb hq hqQ h x u)
  simpa only [E, dfiEquation28SeparatedNonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- Profile-explicit `x`-dual/`y`-main Mellin line bound. -/
theorem exists_dfiEquation28_xMellin_yMain_nonpos_separated_line_bound_order_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28SeparatedNonposMixedMajorant C p σ Q X Y
            q qy a b := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_xSlice_mellin_nonpos_separated_line_bound_order_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h u
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hXA hYC hYCD hSupport qy hqy
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun y _hy ↦ hRaw a b q ha hb hq hqQ h y u)
  simpa only [E, dfiEquation28SeparatedNonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- Profile-explicit symmetric `y`-dual/`x`-main Mellin line bound. -/
theorem exists_dfiEquation28_yMellin_xMain_nonpos_separated_line_bound_order_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28SeparatedNonposMixedMajorant C p σ Q Y X
            q qx b a := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_ySlice_mellin_nonpos_separated_line_bound_order_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ σ hσ p
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h u
  let E : ℝ → ℝ → ℂ := fun y x ↦
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x y
  have hSource : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    simpa only [E, Function.uncurry_apply_pair] using hSource.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSourceSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
        Set.Icc (X / a) (2 * X / a) ×ˢ
          Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro z hz
    have hm := hSourceSupport (show
      (z.2, z.1) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q)) by
      simpa only [E, Function.mem_support,
        Function.uncurry_apply_pair] using hz)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hXC : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXCD : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hYA hXC hXCD hSupport qx hqx
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun x _hx ↦ hRaw a b q ha hb hq hqQ h x u)
  simpa only [E, dfiEquation28SeparatedNonposMixedMajorant,
    dfiVoronoiMainIntervalNorm] using hMixed

/-- Concise source form of the mixed `x`-Mellin/`y`-main estimate. -/
theorem exists_dfiEquation28_xMellin_yMain_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28MixedMajorant C p σ Q X Y a b q qy a b := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_dfiEquation28_xMellin_yMain_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  exact ⟨C, hC, by
    intro a b q qy ha hb hq hqy hqQ h u
    simpa only [dfiEquation28MixedMajorant] using
      hBound a b q qy ha hb hq hqy hqQ h u⟩

/-- Concise source form of the symmetric mixed `y`-Mellin/`x`-main
estimate. -/
theorem exists_dfiEquation28_yMellin_xMain_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28MixedMajorant C p σ Q Y X a b q qx b a := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_dfiEquation28_yMellin_xMain_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  exact ⟨C, hC, by
    intro a b q qx ha hb hq hqx hqQ h u
    simpa only [dfiEquation28MixedMajorant] using
      hBound a b q qx ha hb hq hqx hqQ h u⟩

theorem exists_dfiEquation28_xMellin_yMain_nonpos_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28NonposMixedMajorant C p σ Q X Y
            a b q qy a b :=
  exists_dfiEquation28_xMellin_yMain_nonpos_line_bound_order
    hf hbox hφ hscale w hUQ σ hσ p

theorem exists_dfiEquation28_yMellin_xMain_nonpos_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28NonposMixedMajorant C p σ Q Y X
            a b q qx b a :=
  exists_dfiEquation28_yMellin_xMain_nonpos_line_bound_order
    hf hbox hφ hscale w hUQ σ hσ p

/-- The actual `x`-dual/`y`-main equation-(24) test function, with all
smoothness and support obligations discharged from equations (2), (21), and
(23). -/
noncomputable def dfiEquation23XMainFamilyTestFunction
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm (dfiReducedModulus b q).denominator
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x)) := by
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact dfiVoronoiMainTermSecondFamilyTestFunction hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    hSupport (dfiReducedModulus b q).denominator

/-- The actual `x`-main/`y`-dual equation-(24) test function. -/
noncomputable def dfiEquation23YMainFamilyTestFunction
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm (dfiReducedModulus a q).denominator
        (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y)) := by
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact dfiVoronoiMainTermFamilyTestFunction hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport (dfiReducedModulus a q).denominator

/-- Full `x`-dual/`y`-main source branch split at DFI's literal equation
(29) cutoff.  The first summand is the physical retained estimate with
equation (30) inserted; the second is the arbitrarily deep left-contour
tail from equation (29). -/
theorem exists_dfiEquation29_xSingleDual_source_full_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          A * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
            (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) +
          D * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
            dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
              (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b *
            ((dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
              (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A, hA, hRetained⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_xMellin_yMain_source_bound
      hf hbox hφ hscale w hU (-(1 / 2 : ℝ) - k)
        (2 * (k + 1) + 4)
  refine ⟨A, D, hA, hD, Ck, hCk, ?_⟩
  intro q hq0 hqQ
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  have hqy : 0 < qy := NeZero.pos qy
  have hg : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) := by
    simpa only [qx, qy, E] using dfiEquation23XMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  let Bk := dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b
  have hLeftLine : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    intro u
    simpa only [E, Bk] using hLeft a b q qy ha hb hq hqy hqQ h u
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hL : 0 < L :=
    dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) (by linarith) ε
  have hRet := hRetained q inferInstance branch
  have hAfter := hTail hg hBk hLeftLine qx L inferInstance hL
  dsimp only [qx, qy, E, L]
  rw [← dfiVoronoiDualMassUpTo_add_after qx branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) L]
  exact add_le_add
    (by simpa only [dfiVoronoiDualMassUpTo] using hRet)
    (by simpa only [dfiVoronoiDualMassAfter, Bk, L, mul_assoc] using hAfter)

/-- Symmetric full `x`-main/`y`-dual source branch split at DFI's literal
equation-(29) cutoff. -/
theorem exists_dfiEquation29_ySingleDual_source_full_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          A * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
            (|Real.log (X / a)| + |Real.log (2 * X / a)| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) +
          D * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
            dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
              (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a *
            ((dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
              (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A, hA, hRetained⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_yMellin_xMain_source_bound
      hf hbox hφ hscale w hU (-(1 / 2 : ℝ) - k)
        (2 * (k + 1) + 4)
  refine ⟨A, D, hA, hD, Ck, hCk, ?_⟩
  intro q hq0 hqQ
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  have hqx : 0 < qx := NeZero.pos qx
  have hg : DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
    simpa only [qx, qy, E] using dfiEquation23YMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  let Bk := dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a
  have hLeftLine : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    intro u
    simpa only [E, Bk] using hLeft a b q qx ha hb hq hqx hqQ h u
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hL : 0 < L :=
    dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith) ε
  have hRet := hRetained q inferInstance branch
  have hAfter := hTail hg hBk hLeftLine qy L inferInstance hL
  dsimp only [qx, qy, E, L]
  rw [← dfiVoronoiDualMassUpTo_add_after qy branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L]
  exact add_le_add
    (by simpa only [dfiVoronoiDualMassUpTo] using hRet)
    (by simpa only [dfiVoronoiDualMassAfter, Bk, L, mul_assoc] using hAfter)

/-- The complete complementary `x`-dual tail from equation (29), before
the final elementary power simplification.  The contour order `k` is
arbitrary and the majorant retains the source-derived `x` derivative scale. -/
theorem exists_dfiEquation29_xSingleTailWeilTotal_le_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ D : DFIVoronoiDualBranch → ℝ,
      (∀ branch, 0 ≤ D branch) ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ branch : DFIVoronoiDualBranch,
            D branch * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q X Y q qy a b *
              ((dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
                (-(k : ℝ)) / (k : ℝ))) := by
  choose D hD hTail using fun branch : DFIVoronoiDualBranch ↦
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_xMellin_yMain_nonpos_separated_line_bound_order_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hU (-(1 / 2 : ℝ) - k)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (2 * (k + 1) + 4)
  refine ⟨D, hD, Ck, hCk, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL : 0 < L :=
    dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) (by linarith) ε
  have hEach (branch : DFIVoronoiDualBranch) :
      dfiVoronoiDualMassAfterEarly qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) L ≤
        D branch * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
          dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
            (-(1 / 2 : ℝ) - k) Q X Y q qy a b *
          ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
    have hqy : 0 < qy := NeZero.pos qy
    have hg : DFIVoronoiTestFunction
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) := by
      simpa only [qx, qy, E] using dfiEquation23XMainFamilyTestFunction
        w hf hbox hφ a b ha hb h q hq
    let Bk := dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
      (-(1 / 2 : ℝ) - k) Q X Y q qy a b
    have hLeftLine : ∀ u : ℝ,
        (1 + |u|) ^ (2 * (k + 1) + 4) *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
            (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
      intro u
      simpa only [E, Bk] using hLeft a b q qy ha hb hq hqy hqQ h u
    have hBk : 0 ≤ Bk := by
      have hu := hLeftLine 0
      exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
    have ht := hTail branch hg hBk hLeftLine qx L inferInstance hL
    simpa only [dfiVoronoiDualMassAfterEarly, Bk, L, mul_assoc] using ht
  rw [dfiEquation29XSingleTailWeilTotal, dif_neg hq.ne']
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  exact hEach branch

/-- Fixed-weight projection of the profile-explicit `x`-dual tail bound. -/
theorem exists_dfiEquation29_xSingleTailWeilTotal_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ D : DFIVoronoiDualBranch → ℝ,
      (∀ branch, 0 ≤ D branch) ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ branch : DFIVoronoiDualBranch,
            D branch * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q X Y q qy a b *
              ((dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
                (-(k : ℝ)) / (k : ℝ))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_xSingleTailWeilTotal_le_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hQ hU a b ha hb h ε k hk

/-- Symmetric complete `y`-dual tail from equation (29), retaining the
source-derived `y` derivative scale. -/
theorem exists_dfiEquation29_ySingleTailWeilTotal_le_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ D : DFIVoronoiDualBranch → ℝ,
      (∀ branch, 0 ≤ D branch) ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ branch : DFIVoronoiDualBranch,
            D branch * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q Y X q qx b a *
              ((dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
                (-(k : ℝ)) / (k : ℝ))) := by
  choose D hD hTail using fun branch : DFIVoronoiDualBranch ↦
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_yMellin_xMain_nonpos_separated_line_bound_order_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hU (-(1 / 2 : ℝ) - k)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (2 * (k + 1) + 4)
  refine ⟨D, hD, Ck, hCk, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL : 0 < L :=
    dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith) ε
  have hEach (branch : DFIVoronoiDualBranch) :
      dfiVoronoiDualMassAfterEarly qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L ≤
        D branch * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
          dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
            (-(1 / 2 : ℝ) - k) Q Y X q qx b a *
          ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
    have hqx : 0 < qx := NeZero.pos qx
    have hg : DFIVoronoiTestFunction
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
      simpa only [qx, qy, E] using dfiEquation23YMainFamilyTestFunction
        w hf hbox hφ a b ha hb h q hq
    let Bk := dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
      (-(1 / 2 : ℝ) - k) Q Y X q qx b a
    have hLeftLine : ∀ u : ℝ,
        (1 + |u|) ^ (2 * (k + 1) + 4) *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
            (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
      intro u
      simpa only [E, Bk] using hLeft a b q qx ha hb hq hqx hqQ h u
    have hBk : 0 ≤ Bk := by
      have hu := hLeftLine 0
      exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
    have ht := hTail branch hg hBk hLeftLine qy L inferInstance hL
    simpa only [dfiVoronoiDualMassAfterEarly, Bk, L, mul_assoc] using ht
  rw [dfiEquation29YSingleTailWeilTotal, dif_neg hq.ne']
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  exact hEach branch

/-- Fixed-weight projection of the profile-explicit `y`-dual tail bound. -/
theorem exists_dfiEquation29_ySingleTailWeilTotal_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ D : DFIVoronoiDualBranch → ℝ,
      (∀ branch, 0 ≤ D branch) ∧
      ∃ Ck : ℕ → ℝ, (∀ i, 0 < Ck i) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ branch : DFIVoronoiDualBranch,
            D branch * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28SeparatedNonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q Y X q qx b a *
              ((dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
                (-(k : ℝ)) / (k : ℝ))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_ySingleTailWeilTotal_le_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hQ hU a b ha hb h ε k hk

/-- Split a nonnegative source frequency series at the literal positive
window `1 ≤ n ≤ L`, keeping the complementary tail in source order. -/
private theorem Summable.tsum_eq_sum_Icc_add_tail_of_zero
    {F : ℕ → ℝ} (hF : Summable F) (hzero : F 0 = 0) (L : ℕ) :
    (∑' n : ℕ, F n) =
      (∑ n ∈ Finset.Icc 1 L, F n) +
        ∑' j : ℕ, F (L + (j + 1)) := by
  have hSplit := hF.sum_add_tsum_nat_add (L + 1)
  have hFinite : ∑ n ∈ Finset.range (L + 1), F n =
      ∑ n ∈ Finset.Icc 1 L, F n := by
    rw [show Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) by
      ext n
      simp
      omega]
    simp [hzero]
  have hTail : (∑' j : ℕ, F (j + (L + 1))) =
      ∑' j : ℕ, F (L + (j + 1)) := by
    apply tsum_congr
    intro j
    rw [show j + (L + 1) = L + (j + 1) by omega]
  rw [hFinite, hTail] at hSplit
  exact hSplit.symm

/-- The part of a double-dual branch with retained first frequency and
second frequency beyond the source equation-(29) window. -/
noncomputable def dfiEquation29DoubleRetainedXTailYMass
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 Lx,
    ∑' j : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
      qx xBranch qy yBranch E m (Ly + (j + 1))‖

/-- The part of a double-dual branch whose first frequency is beyond the
source equation-(29) window; the second frequency is left complete. -/
noncomputable def dfiEquation29DoubleTailXAllYMass
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx : ℕ) : ℝ :=
  ∑' i : ℕ, ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
    qx xBranch qy yBranch E (Lx + (i + 1)) n‖

/-- Totalized double-dual complement to the literal equation-(29)
rectangle, including both exact tail regions and all four sign pairs. -/
noncomputable def dfiEquation29DoubleTailWeilTotal
    {Q : ℝ} (X Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (ε : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let E := dfiEquation23Weight w F a b h q
    let Lx := dfiEquation29SourceXCutoff a X Q ε
    let Ly := dfiEquation29SourceYCutoff b Y Q ε
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (∑ xBranch : DFIVoronoiDualBranch,
        ∑ yBranch : DFIVoronoiDualBranch,
          (dfiEquation29DoubleRetainedXTailYMass
              qx xBranch qy yBranch E Lx Ly +
            dfiEquation29DoubleTailXAllYMass
              qx xBranch qy yBranch E Lx))

/-- Exact rectangular equation-(29) partition of one complete double-dual
absolute mass.  There is no omitted corner: the outer tail contains all
second frequencies, while the retained outer window is split in `n`. -/
theorem tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_eq_retained_add_tails
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly : ℕ) :
    (∑' m : ℕ, ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) =
      (∑ m ∈ Finset.Icc 1 Lx, ∑ n ∈ Finset.Icc 1 Ly,
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) +
      dfiEquation29DoubleRetainedXTailYMass
        qx xBranch qy yBranch E Lx Ly +
      dfiEquation29DoubleTailXAllYMass
        qx xBranch qy yBranch E Lx := by
  let A : ℕ → ℕ → ℝ := fun m n ↦
    ‖dfiEquation24DoubleDualMellinAmplitude
      qx xBranch qy yBranch E m n‖
  have hInner (m : ℕ) : Summable (A m) := by
    exact summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      qx xBranch qy yBranch m
  have hOuter : Summable (fun m ↦ ∑' n, A m n) := by
    exact summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      qx xBranch qy yBranch
  have hAZeroLeft (n : ℕ) : A 0 n = 0 := by
    simp [A, dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]
  have hAZeroRight (m : ℕ) : A m 0 = 0 := by
    simp [A, dfiEquation24DoubleDualMellinAmplitude,
      dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]
  have hRowZero : (∑' n, A 0 n) = 0 := by
    simp [hAZeroLeft]
  have hInnerSplit (m : ℕ) :
      (∑' n, A m n) =
        (∑ n ∈ Finset.Icc 1 Ly, A m n) +
          ∑' j, A m (Ly + (j + 1)) :=
    Summable.tsum_eq_sum_Icc_add_tail_of_zero
      (hInner m) (hAZeroRight m) Ly
  rw [Summable.tsum_eq_sum_Icc_add_tail_of_zero hOuter hRowZero Lx]
  have hFiniteRows :
      (∑ m ∈ Finset.Icc 1 Lx, ∑' n, A m n) =
        ∑ m ∈ Finset.Icc 1 Lx,
          ((∑ n ∈ Finset.Icc 1 Ly, A m n) +
            ∑' j, A m (Ly + (j + 1))) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact hInnerSplit m
  rw [hFiniteRows, Finset.sum_add_distrib]
  rfl

/-- Exact equation-(29) decomposition of the complete four-sign
double-dual Weil mass.  The two complement regions are disjoint and cover
the whole complement of the retained rectangle. -/
theorem dfiEquation24DoubleDualMass_weil_eq_retained_add_tail
    {Q : ℝ} (X Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b q : ℕ) [NeZero q] (h : ℤ) (ε : ℝ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        dfiEquation24DoubleDualMass q a b
          (dfiEquation23Weight w F a b h q) =
      dfiEquation29DoubleRetainedWeilTotal X Y w F a b h ε q +
        dfiEquation29DoubleTailWeilTotal X Y w F a b h ε q := by
  have hq : q ≠ 0 := NeZero.ne q
  rw [dfiEquation29DoubleRetainedWeilTotal,
    dfiEquation29DoubleTailWeilTotal, dif_neg hq, dif_neg hq]
  dsimp only [dfiEquation24DoubleDualMass]
  rw [Finset.sum_comm]
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (∑ xBranch : DFIVoronoiDualBranch,
          ∑ yBranch : DFIVoronoiDualBranch,
            ((∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
                ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
                  ‖dfiEquation24DoubleDualMellinAmplitude
                    (dfiReducedModulus a q).denominator xBranch
                    (dfiReducedModulus b q).denominator yBranch
                    (dfiEquation23Weight w F a b h q) m n‖) +
              dfiEquation29DoubleRetainedXTailYMass
                (dfiReducedModulus a q).denominator xBranch
                (dfiReducedModulus b q).denominator yBranch
                (dfiEquation23Weight w F a b h q)
                (dfiEquation29SourceXCutoff a X Q ε)
                (dfiEquation29SourceYCutoff b Y Q ε) +
              dfiEquation29DoubleTailXAllYMass
                (dfiReducedModulus a q).denominator xBranch
                (dfiReducedModulus b q).denominator yBranch
                (dfiEquation23Weight w F a b h q)
                (dfiEquation29SourceXCutoff a X Q ε))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro xBranch _
        apply Finset.sum_congr rfl
        intro yBranch _
        exact tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_eq_retained_add_tails
          (dfiReducedModulus a q).denominator xBranch
          (dfiReducedModulus b q).denominator yBranch
          (dfiEquation23Weight w F a b h q)
          (dfiEquation29SourceXCutoff a X Q ε)
          (dfiEquation29SourceYCutoff b Y Q ε)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      ring

/-- The literal two-contour form of one double-dual frequency, with the two
vertical lines exposed independently.  At `σ = τ = -1/2` this is equation
(24); equation (29) permits either line to be moved arbitrarily far left. -/
noncomputable def dfiEquation29DoubleTransformAt
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (m n : ℕ) (σ τ : ℝ) : ℂ :=
  divisorWeight m *
    VerticalIntegral'
      (fun z =>
        (m : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier qx xBranch z *
          (divisorWeight n *
            VerticalIntegral'
              (fun w =>
                (n : ℂ) ^ (-(1 - w)) *
                  dfiEquation29Multiplier qy yBranch w *
                    dfiBiMellin E z w)
              τ))
      σ

set_option maxHeartbeats 1000000 in
/-- Exact two-variable contour displacement behind the discarded-frequency
part of DFI equation (29).  This theorem starts from the physical iterated
Voronoi term, moves the outer line, uses Mellin/Fubini to expose the inner
term, and then moves the inner line.  Thus the tail estimate below applies to
the actual equation-(24) amplitude rather than to a separately postulated
model. -/
theorem dfiEquation24DoubleDualMellinAmplitude_eq_doubleTransformAt_shift
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (kx ky : ℕ) :
    dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n =
      dfiEquation29DoubleTransformAt qx xBranch qy yBranch E m n
        (-(1 / 2 : ℝ) - kx) (-(1 / 2 : ℝ) - ky) := by
  let gx : ℝ → ℂ := fun x => dfiVoronoiDualTerm qy yBranch (E x) n
  have hgx : DFIVoronoiTestFunction gx := by
    exact dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport qy yBranch n
  have hMellin (z : ℂ) :
      mellin gx z =
        dfiVoronoiDualTerm qy yBranch
          (fun y => mellin (fun x => E x y) z) n := by
    simpa only [gx] using mellin_dfiVoronoiDualTerm_family
      hE hA hC hCD hSupport qy yBranch n z
  have hInnerShift (z : ℂ) :
      dfiVoronoiDualTerm qy yBranch
          (fun y => mellin (fun x => E x y) z) n =
        divisorWeight n *
          dfiEquation29TransformAt qy yBranch
            (fun y => mellin (fun x => E x y) z) n
              (-(1 / 2 : ℝ) - ky) := by
    let gy : ℝ → ℂ := fun y => mellin (fun x => E x y) z
    have hgy : DFIVoronoiTestFunction gy :=
      dfiMellinTransposeTestFunction hE hA hC hCD hSupport z
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    rw [hgy.dfiEquation29TransformAt_shift qy ky yBranch hn]
  rw [dfiEquation24DoubleDualMellinAmplitude_eq_iteratedDualTerm
    hE hA hAB hC hCD hSupport qx qy xBranch yBranch m n]
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
  rw [← dfiEquation29TransformAt_initial]
  rw [hgx.dfiEquation29TransformAt_shift qx kx xBranch hm]
  unfold dfiEquation29TransformAt dfiEquation29DoubleTransformAt
    dfiEquation29Integrand VerticalIntegral'
  simp only [smul_eq_mul]
  simp_rw [hMellin, hInnerShift]
  unfold dfiEquation29TransformAt dfiEquation29Integrand VerticalIntegral'
  simp only [smul_eq_mul]
  have hBi (z w : ℂ) :
      mellin (fun y => mellin (fun x => E x y) z) w =
        dfiBiMellin E z w := by
    simpa [dfiBiMellin] using
      (mellin_mellin_comm_of_rectangular_support
        hE hA hC hSupport z w).symm
  simp_rw [hBi]

/-- Two polynomially growing shifted-line multipliers consume the matching
Mellin decay in both variables, leaving the same integrable Cauchy kernel as
on the initial line. -/
theorem two_frequency_pow_decay
    {a b c Cx Cy M u v : ℝ} (p : ℕ)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hA : a ≤ Cx * (1 + |u|) ^ p)
    (hB : b ≤ Cy * (1 + |v|) ^ p)
    (hC : (1 + |u|) ^ (p + 4) * (1 + |v|) ^ (p + 4) * c ≤ M) :
    a * b * c ≤
      Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
  let wu : ℝ := 1 + |u|
  let wv : ℝ := 1 + |v|
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hwv : 0 < wv := by dsimp [wv]; positivity
  have hc' : c ≤ M / (wu ^ (p + 4) * wv ^ (p + 4)) := by
    apply (le_div_iff₀
      (mul_pos (pow_pos hwu (p + 4)) (pow_pos hwv (p + 4)))).2
    simpa only [wu, wv, mul_comm, mul_left_comm, mul_assoc] using hC
  have huDen : 0 < 1 + u ^ 2 := by positivity
  have hvDen : 0 < 1 + v ^ 2 := by positivity
  have huPow : 1 + u ^ 2 ≤ wu ^ 4 := by
    dsimp [wu]
    nlinarith [abs_nonneg u, sq_abs u]
  have hvPow : 1 + v ^ 2 ≤ wv ^ 4 := by
    dsimp [wv]
    nlinarith [abs_nonneg v, sq_abs v]
  have huInv : (wu ^ 4)⁻¹ ≤ (1 + u ^ 2)⁻¹ :=
    inv_anti₀ huDen huPow
  have hvInv : (wv ^ 4)⁻¹ ≤ (1 + v ^ 2)⁻¹ :=
    inv_anti₀ hvDen hvPow
  calc
    a * b * c ≤
        (Cx * wu ^ p) * (Cy * wv ^ p) *
          (M / (wu ^ (p + 4) * wv ^ (p + 4))) := by gcongr
    _ = Cx * Cy * M * (wu ^ 4)⁻¹ * (wv ^ 4)⁻¹ := by
      rw [pow_add, pow_add]
      field_simp [ne_of_gt hwu, ne_of_gt hwv]
    _ ≤ Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
      gcongr

/-- The one-dimensional Cauchy mass used after each shifted vertical
integration. -/
noncomputable def dfiCauchyLineMass : ℝ :=
  ∫ u : ℝ, (1 + u ^ 2)⁻¹

theorem dfiCauchyLineMass_nonneg : 0 ≤ dfiCauchyLineMass := by
  exact integral_nonneg fun _ => inv_nonneg.mpr (by positivity)

set_option maxHeartbeats 1000000 in
/-- Quantitative two-contour bound on a shifted double-dual frequency.  The
statement keeps the multiplier and equation-(28) majorants abstract so the
next theorem can choose them uniformly before the arithmetic parameters. -/
theorem norm_dfiEquation29DoubleTransformAt_shift_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (k : ℕ)
    {Cx Cy M : ℝ} (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hx : ∀ u : ℝ,
      ‖dfiEquation29Multiplier qx xBranch
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        Cx * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (1 + |u|) ^ (2 * (k + 1)))
    (hy : ∀ v : ℝ,
      ‖dfiEquation29Multiplier qy yBranch
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        Cy * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (1 + |v|) ^ (2 * (k + 1)))
    (hBi : ∀ u v : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
          (1 + |v|) ^ (2 * (k + 1) + 4) *
        ‖dfiBiMellin E
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    ‖dfiEquation29DoubleTransformAt qx xBranch qy yBranch E m n
        (-(1 / 2 : ℝ) - k) (-(1 / 2 : ℝ) - k)‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ ^ 2 *
        ‖divisorWeight m‖ * ‖divisorWeight n‖ *
        (m : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        (n : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        ((Cx * (qx : ℝ) ^ (2 + 2 * (k : ℝ))) *
          (Cy * (qy : ℝ) ^ (2 + 2 * (k : ℝ))) * M) *
        dfiCauchyLineMass ^ 2 := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  let K₀ : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  let R : ℝ :=
    (Cx * (qx : ℝ) ^ (2 + 2 * (k : ℝ))) *
      (Cy * (qy : ℝ) ^ (2 + 2 * (k : ℝ))) * M
  let pm : ℝ := (m : ℝ) ^ (-(3 / 2 : ℝ) - k)
  let pn : ℝ := (n : ℝ) ^ (-(3 / 2 : ℝ) - k)
  have hK₀ : 0 ≤ K₀ := norm_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpm : 0 ≤ pm := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hpn : 0 ≤ pn := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmPower (u : ℝ) :
      ‖(m : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = pm := by
    rw [Complex.norm_natCast_cpow_of_pos hm]
    dsimp [σ, pm]
    congr 1
    simp
    ring
  have hnPower (v : ℝ) :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (v : ℂ) * I)))‖ = pn := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    dsimp [σ, pn]
    congr 1
    simp
    ring
  have hDecay (u v : ℝ) :
      ‖dfiEquation29Multiplier qx xBranch
          ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖dfiEquation29Multiplier qy yBranch
          ((σ : ℂ) + (v : ℂ) * I)‖ *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((σ : ℂ) + (v : ℂ) * I)‖ ≤
        R * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
    simpa only [σ, p, R, mul_assoc] using
      two_frequency_pow_decay p
        (norm_nonneg _) (norm_nonneg _)
        (mul_nonneg hCx (Real.rpow_nonneg (Nat.cast_nonneg qx) _))
        (mul_nonneg hCy (Real.rpow_nonneg (Nat.cast_nonneg qy) _)) hM
        (by simpa only [σ, p, mul_assoc] using hx u)
        (by simpa only [σ, p, mul_assoc] using hy v)
        (by simpa only [σ, p] using hBi u v)
  let gx : ℝ → ℂ := fun x => dfiVoronoiDualTerm qy yBranch (E x) n
  have hgx : DFIVoronoiTestFunction gx :=
    dfiVoronoiDualTerm_family_testFunction
      hE hA hAB hC hCD hSupport qy yBranch n
  have hMellinGx (z : ℂ) :
      mellin gx z = dfiVoronoiDualTerm qy yBranch
        (fun y => mellin (fun x => E x y) z) n := by
    simpa only [gx] using mellin_dfiVoronoiDualTerm_family
      hE hA hC hCD hSupport qy yBranch n z
  have hInnerShift (z : ℂ) :
      dfiVoronoiDualTerm qy yBranch
          (fun y => mellin (fun x => E x y) z) n =
        divisorWeight n *
          dfiEquation29TransformAt qy yBranch
            (fun y => mellin (fun x => E x y) z) n σ := by
    let gy : ℝ → ℂ := fun y => mellin (fun x => E x y) z
    have hgy : DFIVoronoiTestFunction gy :=
      dfiMellinTransposeTestFunction hE hA hC hCD hSupport z
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial]
    rw [← dfiEquation29TransformAt_initial]
    simpa only [σ] using congrArg (fun t => divisorWeight n * t)
      (hgy.dfiEquation29TransformAt_shift qy k yBranch hn)
  have hOuterInt : Integrable (fun u : ℝ =>
      (m : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I))) *
        dfiEquation29Multiplier qx xBranch ((σ : ℂ) + (u : ℂ) * I) *
          (divisorWeight n *
            VerticalIntegral'
              (fun w =>
                (n : ℂ) ^ (-(1 - w)) *
                  dfiEquation29Multiplier qy yBranch w *
                    dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w)
              σ)) := by
    have hBase := hgx.integrable_dfiEquation29Integrand_vertical
      qx k xBranch hm (σ := σ) (by rfl) (by dsimp [σ]; linarith)
    apply hBase.congr
    filter_upwards with u
    unfold dfiEquation29Integrand
    rw [hMellinGx, hInnerShift]
    unfold dfiEquation29TransformAt VerticalIntegral'
    simp only [smul_eq_mul]
    have hBiEq (w : ℂ) :
        mellin (fun y => mellin (fun x => E x y)
            ((σ : ℂ) + (u : ℂ) * I)) w =
          dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w := by
      simpa [dfiBiMellin] using
        (mellin_mellin_comm_of_rectangular_support hE hA hC hSupport
          ((σ : ℂ) + (u : ℂ) * I) w).symm
    unfold dfiEquation29Integrand
    simp_rw [hBiEq]
  have hOuterPoint (u : ℝ) :
      ‖(m : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I))) *
        dfiEquation29Multiplier qx xBranch ((σ : ℂ) + (u : ℂ) * I) *
          (divisorWeight n *
            VerticalIntegral'
              (fun w =>
                (n : ℂ) ^ (-(1 - w)) *
                  dfiEquation29Multiplier qy yBranch w *
                    dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w)
              σ)‖ ≤
        pm * ‖divisorWeight n‖ * K₀ *
          (pn * R * (1 + u ^ 2)⁻¹ * dfiCauchyLineMass) := by
    let gy : ℝ → ℂ := fun y => mellin (fun x => E x y)
      ((σ : ℂ) + (u : ℂ) * I)
    have hgy : DFIVoronoiTestFunction gy :=
      dfiMellinTransposeTestFunction hE hA hC hCD hSupport
        ((σ : ℂ) + (u : ℂ) * I)
    have hInnerBase := hgy.integrable_dfiEquation29Integrand_vertical
      qy k yBranch hn (σ := σ) (by rfl) (by dsimp [σ]; linarith)
    have hBiEq (w : ℂ) : mellin gy w =
        dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w := by
      simpa [gy, dfiBiMellin] using
        (mellin_mellin_comm_of_rectangular_support hE hA hC hSupport
          ((σ : ℂ) + (u : ℂ) * I) w).symm
    have hInnerInt : Integrable (fun v : ℝ =>
        (n : ℂ) ^ (-(1 - ((σ : ℂ) + (v : ℂ) * I))) *
          dfiEquation29Multiplier qy yBranch ((σ : ℂ) + (v : ℂ) * I) *
            dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((σ : ℂ) + (v : ℂ) * I)) := by
      apply hInnerBase.congr
      filter_upwards with v
      unfold dfiEquation29Integrand
      rw [hBiEq]
    have hTargetInt : Integrable (fun v : ℝ =>
        ‖dfiEquation29Multiplier qx xBranch
            ((σ : ℂ) + (u : ℂ) * I)‖ *
          (pn * ‖dfiEquation29Multiplier qy yBranch
              ((σ : ℂ) + (v : ℂ) * I)‖ *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((σ : ℂ) + (v : ℂ) * I)‖)) := by
      have hNorm := hInnerInt.norm
      rw [show (fun v : ℝ =>
          ‖dfiEquation29Multiplier qx xBranch
              ((σ : ℂ) + (u : ℂ) * I)‖ *
            (pn * ‖dfiEquation29Multiplier qy yBranch
                ((σ : ℂ) + (v : ℂ) * I)‖ *
              ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                ((σ : ℂ) + (v : ℂ) * I)‖)) =
          fun v : ℝ => ‖dfiEquation29Multiplier qx xBranch
              ((σ : ℂ) + (u : ℂ) * I)‖ *
            ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (v : ℂ) * I))) *
              dfiEquation29Multiplier qy yBranch
                ((σ : ℂ) + (v : ℂ) * I) *
                dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                  ((σ : ℂ) + (v : ℂ) * I)‖ by
        funext v
        rw [norm_mul, norm_mul, hnPower]
        ]
      exact hNorm.const_mul _
    have hMajorInt : Integrable (fun v : ℝ =>
        pn * R * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹) := by
      exact integrable_inv_one_add_sq.const_mul
        (pn * R * (1 + u ^ 2)⁻¹)
    have hIntegral :
        (∫ v : ℝ,
          ‖dfiEquation29Multiplier qx xBranch
              ((σ : ℂ) + (u : ℂ) * I)‖ *
            (pn * ‖dfiEquation29Multiplier qy yBranch
                ((σ : ℂ) + (v : ℂ) * I)‖ *
              ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                ((σ : ℂ) + (v : ℂ) * I)‖)) ≤
          pn * R * (1 + u ^ 2)⁻¹ * dfiCauchyLineMass := by
      calc
        _ ≤ ∫ v : ℝ, pn * R * (1 + u ^ 2)⁻¹ *
            (1 + v ^ 2)⁻¹ := by
          apply integral_mono hTargetInt hMajorInt
          intro v
          calc
            _ = pn *
                (‖dfiEquation29Multiplier qx xBranch
                    ((σ : ℂ) + (u : ℂ) * I)‖ *
                  ‖dfiEquation29Multiplier qy yBranch
                    ((σ : ℂ) + (v : ℂ) * I)‖ *
                  ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                    ((σ : ℂ) + (v : ℂ) * I)‖) := by ring
            _ ≤ pn * (R * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹) := by
              exact mul_le_mul_of_nonneg_left (hDecay u v) hpn
            _ = _ := by ring
        _ = pn * R * (1 + u ^ 2)⁻¹ * dfiCauchyLineMass := by
          rw [MeasureTheory.integral_const_mul]
          rfl
    rw [norm_mul, norm_mul, hmPower, norm_mul]
    have hVI :
        ‖VerticalIntegral'
          (fun w =>
            (n : ℂ) ^ (-(1 - w)) *
              dfiEquation29Multiplier qy yBranch w *
                dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w) σ‖ ≤
          K₀ * ∫ v : ℝ,
            ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (v : ℂ) * I))) *
              dfiEquation29Multiplier qy yBranch
                ((σ : ℂ) + (v : ℂ) * I) *
                dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                  ((σ : ℂ) + (v : ℂ) * I)‖ := by
      simpa only [K₀] using norm_verticalIntegral'_le_integral_norm
        (fun w =>
          (n : ℂ) ^ (-(1 - w)) *
            dfiEquation29Multiplier qy yBranch w *
              dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w) σ
    calc
      pm * ‖dfiEquation29Multiplier qx xBranch
          ((σ : ℂ) + (u : ℂ) * I)‖ *
          (‖divisorWeight n‖ *
            ‖VerticalIntegral'
              (fun w =>
                (n : ℂ) ^ (-(1 - w)) *
                  dfiEquation29Multiplier qy yBranch w *
                    dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I) w) σ‖) ≤
        pm * ‖dfiEquation29Multiplier qx xBranch
              ((σ : ℂ) + (u : ℂ) * I)‖ *
          (‖divisorWeight n‖ *
            (K₀ * ∫ v : ℝ,
              ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (v : ℂ) * I))) *
                dfiEquation29Multiplier qy yBranch
                  ((σ : ℂ) + (v : ℂ) * I) *
                  dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                    ((σ : ℂ) + (v : ℂ) * I)‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hVI (norm_nonneg _))
            (mul_nonneg hpm (norm_nonneg _))
      _ = pm * ‖divisorWeight n‖ * K₀ *
          (∫ v : ℝ,
            ‖dfiEquation29Multiplier qx xBranch
                ((σ : ℂ) + (u : ℂ) * I)‖ *
              (pn * ‖dfiEquation29Multiplier qy yBranch
                  ((σ : ℂ) + (v : ℂ) * I)‖ *
                ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
                  ((σ : ℂ) + (v : ℂ) * I)‖)) := by
          simp_rw [norm_mul, hnPower]
          rw [MeasureTheory.integral_const_mul]
          ring
      _ ≤ pm * ‖divisorWeight n‖ * K₀ *
          (pn * R * (1 + u ^ 2)⁻¹ * dfiCauchyLineMass) := by
          gcongr
      _ = _ := by ring
  have hOuterNormInt := hOuterInt.norm
  have hMajorOuter : Integrable (fun u : ℝ =>
      pm * ‖divisorWeight n‖ * K₀ *
        (pn * R * dfiCauchyLineMass) * (1 + u ^ 2)⁻¹) := by
    exact integrable_inv_one_add_sq.const_mul
      (pm * ‖divisorWeight n‖ * K₀ * (pn * R * dfiCauchyLineMass))
  unfold dfiEquation29DoubleTransformAt
  rw [norm_mul]
  calc
    ‖divisorWeight m‖ *
        ‖VerticalIntegral'
          (fun z =>
            (m : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier qx xBranch z *
              (divisorWeight n *
                VerticalIntegral'
                  (fun w =>
                    (n : ℂ) ^ (-(1 - w)) *
                      dfiEquation29Multiplier qy yBranch w *
                        dfiBiMellin E z w) σ)) σ‖ ≤
      ‖divisorWeight m‖ *
        (K₀ * ∫ u : ℝ,
          ‖(m : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I))) *
            dfiEquation29Multiplier qx xBranch
              ((σ : ℂ) + (u : ℂ) * I) *
                (divisorWeight n *
                  VerticalIntegral'
                    (fun w =>
                      (n : ℂ) ^ (-(1 - w)) *
                        dfiEquation29Multiplier qy yBranch w *
                          dfiBiMellin E
                            ((σ : ℂ) + (u : ℂ) * I) w) σ)‖) := by
        gcongr
        simpa only [K₀] using norm_verticalIntegral'_le_integral_norm
          (fun z =>
            (m : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier qx xBranch z *
              (divisorWeight n *
                VerticalIntegral'
                  (fun w =>
                    (n : ℂ) ^ (-(1 - w)) *
                      dfiEquation29Multiplier qy yBranch w *
                        dfiBiMellin E z w) σ)) σ
    _ ≤ ‖divisorWeight m‖ *
        (K₀ * ∫ u : ℝ,
          pm * ‖divisorWeight n‖ * K₀ *
            (pn * R * dfiCauchyLineMass) * (1 + u ^ 2)⁻¹) := by
        gcongr
        intro u
        exact (hOuterPoint u).trans_eq (by ring)
    _ = ‖divisorWeight m‖ *
        (K₀ * (pm * ‖divisorWeight n‖ * K₀ *
          (pn * R * dfiCauchyLineMass) * dfiCauchyLineMass)) := by
        rw [MeasureTheory.integral_const_mul]
        rfl
    _ = _ := by
      dsimp only [σ, K₀, R, pm, pn]
      ring

/-- The literal equation-(28) two-variable majorant on a common shifted
line. -/
noncomputable def dfiEquation28BiShiftMajorant
    (K : ℕ → ℕ → ℝ) (p : ℕ) (σ : ℝ) (Q X Y : ℝ)
    (a b q : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ := (q : ℝ) * Q
  let M := Csum * qQ⁻¹
  let R := ((a : ℝ) * (b : ℝ)) / qQ
  dfiMellinProfileMajorant (Y / b) (2 * Y / b) σ p
    (dfiMellinProfileMajorant (X / a) (2 * X / a) σ p M R) R

/-- In the nontrivial DFI range `a ≤ X`, `b ≤ Y`, the nested
equation-(28) majorant is exactly the composition of two source-normalized
dyadic profiles. -/
theorem dfiEquation28BiShiftMajorant_eq_dyadic
    (K : ℕ → ℕ → ℝ) (p : ℕ) (σ Q X Y : ℝ)
    (a b q : ℕ) (ha : 0 < a) (hb : 0 < b)
    (haX : (a : ℝ) ≤ X) (hbY : (b : ℝ) ≤ Y) :
    dfiEquation28BiShiftMajorant K p σ Q X Y a b q =
      let Csum := ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (p + 1), K i j
      let qQ := (q : ℝ) * Q
      let M := Csum * qQ⁻¹
      let R := ((a : ℝ) * (b : ℝ)) / qQ
      dfiMellinDyadicMajorant (Y / b) σ p
        (dfiMellinDyadicMajorant (X / a) σ p M R) R := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXa : 1 ≤ X / (a : ℝ) := by
    rw [le_div_iff₀ haR]
    simpa only [one_mul] using haX
  have hYb : 1 ≤ Y / (b : ℝ) := by
    rw [le_div_iff₀ hbR]
    simpa only [one_mul] using hbY
  have hXupper : 2 * X / (a : ℝ) = 2 * (X / (a : ℝ)) := by
    ring
  have hYupper : 2 * Y / (b : ℝ) = 2 * (Y / (b : ℝ)) := by
    ring
  simp only [dfiEquation28BiShiftMajorant]
  rw [hXupper, hYupper]
  rw [dfiMellinProfileMajorant_eq_dyadicMajorant_of_one_le
      (X / a) σ _ _ p hXa,
    dfiMellinProfileMajorant_eq_dyadicMajorant_of_one_le
      (Y / b) σ _ _ p hYb]

/-- Equation (28) on a dyadic source rectangle is the product of the two
one-variable integration-by-parts factors and the original equation-(28)
amplitude.  This is the exact algebraic form used in DFI's passage to the
frequency cutoffs in equation (29). -/
theorem dfiEquation28BiShiftMajorant_eq_factor_product
    (K : ℕ → ℕ → ℝ) (p : ℕ) (σ Q X Y : ℝ)
    (a b q : ℕ) (ha : 0 < a) (hb : 0 < b)
    (haX : (a : ℝ) ≤ X) (hbY : (b : ℝ) ≤ Y) :
    dfiEquation28BiShiftMajorant K p σ Q X Y a b q =
      dfiMellinDyadicFactor (Y / b) σ p
          (((a : ℝ) * b) / ((q : ℝ) * Q)) *
        dfiMellinDyadicFactor (X / a) σ p
          (((a : ℝ) * b) / ((q : ℝ) * Q)) *
        ((∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j) *
            (((q : ℝ) * Q)⁻¹)) := by
  rw [dfiEquation28BiShiftMajorant_eq_dyadic K p σ Q X Y a b q
    ha hb haX hbY]
  simp only [dfiMellinDyadicMajorant_eq_factor_mul]
  ring

/-- The literal equation-(28) majorant after a common nonpositive shift,
with both dyadic lower endpoints retained. -/
noncomputable def dfiEquation28BiNonposShiftMajorant
    (K : ℕ → ℕ → ℝ) (p : ℕ) (σ : ℝ) (Q X Y : ℝ)
    (a b q : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ := (q : ℝ) * Q
  let M := Csum * qQ⁻¹
  let R := ((a : ℝ) * (b : ℝ)) / qQ
  dfiMellinNonposProfileMajorant (Y / b) (2 * Y / b) σ p
    (dfiMellinNonposProfileMajorant (X / a) (2 * X / a) σ p M R) R

/-- The two-variable equation-(28) majorant before coarsening the separate
`x` and `y` derivative ratios. -/
noncomputable def dfiEquation28BiSeparatedNonposShiftMajorant
    (K : ℕ → ℕ → ℝ) (p : ℕ) (σ : ℝ) (Q X Y : ℝ)
    (a b q : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ := (q : ℝ) * Q
  let M := Csum * qQ⁻¹
  let Rx := (a : ℝ) / qQ
  let Ry := (b : ℝ) / qQ
  dfiMellinNonposProfileMajorant (Y / b) (2 * Y / b) σ p
    (dfiMellinNonposProfileMajorant (X / a) (2 * X / a) σ p M Rx) Ry

/-- On the left line `-1/2-k`, the two source factors in equation (28)
are exactly `(X/a)^(-1/2-k)` and `(Y/b)^(-1/2-k)`. -/
theorem dfiEquation28BiNonposShiftMajorant_neg_half_sub_nat
    (K : ℕ → ℕ → ℝ) (p k : ℕ) (Q X Y : ℝ) (a b q : ℕ) :
    dfiEquation28BiNonposShiftMajorant K p (-(1 / 2 : ℝ) - k)
        Q X Y a b q =
      let Csum := ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (p + 1), K i j
      let qQ := (q : ℝ) * Q
      let M := Csum * qQ⁻¹
      let R := ((a : ℝ) * (b : ℝ)) / qQ
      (1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p *
        ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
        (Y / b) ^ (-(1 / 2 : ℝ) - k) *
        (1 + (1 / 2 + (k : ℝ) + (p : ℝ) + (2 * Y / b) * R) ^ p) *
      ((1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p *
        ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
        (X / a) ^ (-(1 / 2 : ℝ) - k) *
        (1 + (1 / 2 + (k : ℝ) + (p : ℝ) + (2 * X / a) * R) ^ p) * M) := by
  simp only [dfiEquation28BiNonposShiftMajorant,
    dfiMellinNonposProfileMajorant, abs_neg_half_sub_natCast]
  ring

/-- Source-uniform shifted-line pointwise estimate for one of the four
double-dual branches.  It is the exact equation-(29) tail estimate after the
native `d(n) ≪ n^(1/2)` insertion. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_shifted_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (k : ℕ) (xBranch yBranch : DFIVoronoiDualBranch) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (m n : ℕ), 0 < m → 0 < n →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖ ≤
          B * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
            (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
            dfiEquation28BiSeparatedNonposShiftMajorant K (2 * (k + 1) + 4)
              (-(1 / 2 : ℝ) - k) Q X Y a b q *
            (m : ℝ) ^ (-(1 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
  obtain ⟨Cx, hCx, hx⟩ :=
    exists_dfiEquation29Multiplier_explicit_modulus_bound k xBranch
  obtain ⟨Cy, hCy, hy⟩ :=
    exists_dfiEquation29Multiplier_explicit_modulus_bound k yBranch
  obtain ⟨Ddiv, hDdiv, hDiv⟩ :=
    divisorCountBound_native (1 / 2 : ℝ) (by norm_num)
  obtain ⟨K, hK, hLine⟩ :=
    exists_dfiEquation28_biMellin_nonpos_separated_line_bound_order_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ
        (-(1 / 2 : ℝ) - k) (-(1 / 2 : ℝ) - k)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (2 * (k + 1) + 4)
  let K₀ : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  let B₀ : ℝ := K₀ ^ 2 * Ddiv ^ 2 * Cx * Cy * dfiCauchyLineMass ^ 2
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀, K₀]; positivity
  refine ⟨B₀, hB₀, K, hK, ?_⟩
  intro a b q hq0 ha hb hqQ h m n hm hn
  dsimp only
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let M := dfiEquation28BiSeparatedNonposShiftMajorant K (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q X Y a b q
  have hMellin : ∀ u v : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
          (1 + |v|) ^ (2 * (k + 1) + 4) *
        ‖dfiBiMellin E
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ M := by
    intro u v
    simpa only [E, M, dfiEquation28BiSeparatedNonposShiftMajorant] using
      hLine a b q ha hb hq hqQ h u v
  have hM : 0 ≤ M := by
    have h0 := hMellin 0 0
    exact (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (norm_nonneg _)).trans h0
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hShift := norm_dfiEquation29DoubleTransformAt_shift_le
    hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch hm hn k
      hCx.le hCy.le hM
      (fun u => hx qx inferInstance (-(1 / 2 : ℝ) - k)
        (by rfl) (by linarith) u)
      (fun v => hy qy inferInstance (-(1 / 2 : ℝ) - k)
        (by rfl) (by linarith) v)
      hMellin
  have hEq := dfiEquation24DoubleDualMellinAmplitude_eq_doubleTransformAt_shift
    hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch hm hn k k
  have hmDiv : ‖divisorWeight m‖ ≤ Ddiv * (m : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [divisorWeight] using hDiv m hm
  have hnDiv : ‖divisorWeight n‖ ≤ Ddiv * (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [divisorWeight] using hDiv n hn
  have hmPow :
      (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ) - k) =
        (m : ℝ) ^ (-(1 : ℝ) - k) := by
    rw [← Real.rpow_add (Nat.cast_pos.mpr hm)]
    congr 1
    ring
  have hnPow :
      (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ) - k) =
        (n : ℝ) ^ (-(1 : ℝ) - k) := by
    rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]
    congr 1
    ring
  rw [hEq]
  calc
    _ ≤ K₀ ^ 2 * ‖divisorWeight m‖ * ‖divisorWeight n‖ *
        (m : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        (n : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        ((Cx * (qx : ℝ) ^ (2 + 2 * (k : ℝ))) *
          (Cy * (qy : ℝ) ^ (2 + 2 * (k : ℝ))) * M) *
        dfiCauchyLineMass ^ 2 := by
      simpa only [K₀] using hShift
    _ ≤ K₀ ^ 2 * (Ddiv * (m : ℝ) ^ (1 / 2 : ℝ)) *
        (Ddiv * (n : ℝ) ^ (1 / 2 : ℝ)) *
        (m : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        (n : ℝ) ^ (-(3 / 2 : ℝ) - k) *
        ((Cx * (qx : ℝ) ^ (2 + 2 * (k : ℝ))) *
          (Cy * (qy : ℝ) ^ (2 + 2 * (k : ℝ))) * M) *
        dfiCauchyLineMass ^ 2 := by gcongr
    _ = B₀ * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
        (qy : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
        (m : ℝ) ^ (-(1 : ℝ) - k) *
        (n : ℝ) ^ (-(1 : ℝ) - k) := by
      dsimp only [B₀]
      calc
        _ = K₀ ^ 2 * Ddiv ^ 2 * Cx * Cy * dfiCauchyLineMass ^ 2 *
              (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
              (qy : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
              ((m : ℝ) ^ (1 / 2 : ℝ) *
                (m : ℝ) ^ (-(3 / 2 : ℝ) - k)) *
              ((n : ℝ) ^ (1 / 2 : ℝ) *
                (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) := by ring
        _ = _ := by rw [hmPow, hnPow]

/-- Fixed-weight projection of the profile-explicit shifted double-dual
amplitude bound. -/
theorem exists_dfiEquation24DoubleDualMellinAmplitude_source_shifted_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (k : ℕ) (xBranch yBranch : DFIVoronoiDualBranch) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (m n : ℕ), 0 < m → 0 < n →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖ ≤
          B * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
            (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
            dfiEquation28BiSeparatedNonposShiftMajorant K (2 * (k + 1) + 4)
              (-(1 / 2 : ℝ) - k) Q X Y a b q *
            (m : ℝ) ^ (-(1 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact
    exists_dfiEquation24DoubleDualMellinAmplitude_source_shifted_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ k xBranch yBranch

/-- The complete positive-frequency mass of the shifted contour power is
uniformly bounded.  The zero frequency vanishes because the exponent is
nonzero; the remaining tail is the integral-comparison estimate used in
DFI equation (29). -/
theorem tsum_natCast_rpow_neg_one_sub_nat_le
    (k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, (n : ℝ) ^ (-(1 : ℝ) - k)) ≤ 1 + 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 : ℝ) - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hsplit := hbase.sum_add_tsum_nat_add 2
  have htail := tsum_nat_add_one_rpow_neg_le
    (L := (1 : ℝ)) (p := 1 + (k : ℝ)) (by norm_num) (by linarith)
  have htail' :
      (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k)) ≤ 1 / (k : ℝ) := by
    calc
      _ = ∑' j : ℕ, (1 + ((j + 1 : ℕ) : ℝ)) ^ (-(1 + (k : ℝ))) := by
        apply tsum_congr
        intro j
        congr 2 <;> push_cast <;> ring
      _ ≤ 1 ^ (1 - (1 + (k : ℝ))) / (1 + (k : ℝ) - 1) := htail
      _ = 1 / (k : ℝ) := by rw [Real.one_rpow]; ring_nf
  calc
    (∑' n : ℕ, (n : ℝ) ^ (-(1 : ℝ) - k)) =
        (∑ n ∈ Finset.range 2, (n : ℝ) ^ (-(1 : ℝ) - k)) +
          ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k) := by
      simpa [Nat.cast_add, add_comm] using hsplit.symm
    _ = 1 + ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k) := by
      have hexp : -(1 : ℝ) - k < 0 := by linarith
      norm_num [Finset.sum_range_succ, Real.zero_rpow hexp.ne]
    _ ≤ 1 + 1 / (k : ℝ) := by gcongr

/-- The shifted positive-frequency tail in the precise exponent produced by
the double contour displacement. -/
theorem tsum_nat_add_rpow_neg_one_sub_nat_le
    (L k : ℕ) (hL : 0 < L) (hk : 0 < k) :
    (∑' j : ℕ, ((L + (j + 1) : ℕ) : ℝ) ^ (-(1 : ℝ) - k)) ≤
      (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htail := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 1 + (k : ℝ))
      (Nat.cast_pos.mpr hL) (by linarith)
  calc
    _ = ∑' j : ℕ, ((L : ℝ) + ((j + 1 : ℕ) : ℝ)) ^
        (-(1 + (k : ℝ))) := by
      apply tsum_congr
      intro j
      congr 2 <;> push_cast <;> ring
    _ ≤ (L : ℝ) ^ (1 - (1 + (k : ℝ))) /
        (1 + (k : ℝ) - 1) := htail
    _ = (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) := by ring_nf

/-- Tail summation in the exact exponent produced by the source recurrence,
including the divisor `ε` loss and Bessel quarter power. -/
theorem tsum_nat_add_rpow_sub_quarter_sub_nat_le
    (ε : ℝ) (L k : ℕ) (hL : 0 < L)
    (hk : ε + 3 / 4 < (k : ℝ)) :
    (∑' j : ℕ, ((L + (j + 1) : ℕ) : ℝ) ^
        (ε - 1 / 4 - k)) ≤
      (L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4) := by
  let p : ℝ := (k : ℝ) + 1 / 4 - ε
  have hp : 1 < p := by dsimp [p]; linarith
  have htail := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := p) (Nat.cast_pos.mpr hL) hp
  calc
    (∑' j : ℕ, ((L + (j + 1) : ℕ) : ℝ) ^
        (ε - 1 / 4 - k)) =
      ∑' j : ℕ, ((L : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ (-p) := by
        apply tsum_congr
        intro j
        rw [show ((L + (j + 1) : ℕ) : ℝ) =
          (L : ℝ) + ((j + 1 : ℕ) : ℝ) by push_cast; rfl]
        congr 1
        dsimp [p]
        ring
    _ ≤ (L : ℝ) ^ (1 - p) / (p - 1) := htail
    _ = (L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4) := by
      rw [show 1 - p = ε + 3 / 4 - k by dsimp [p]; ring,
        show p - 1 = (k : ℝ) - ε - 3 / 4 by dsimp [p]; ring]

/-- Sum the source-sharp `x`-dual/`y`-main recurrence estimate beyond
DFI's literal equation-(29) cutoff. -/
theorem exists_dfiEquation29_xSingleMainTailMass_source_l1_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let L := dfiEquation29SourceXCutoff a X Q ε
        dfiVoronoiDualMassAfterEarly qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) L ≤
          dfiEquation29XSingleMainTailL1Coefficient
              C D k Q X Y a b qx qy *
            ((L : ℝ) ^ (ε + 3 / 4 - k) /
              ((k : ℝ) - ε - 3 / 4)) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_xMain_source_l1_power_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h branch
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  let A := dfiEquation29XSingleMainTailL1Coefficient
    C D k Q X Y a b qx qy
  let F : ℕ → ℝ := fun j ↦
    ‖dfiVoronoiDualTerm qx branch
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) (L + (j + 1))‖
  let p : ℕ → ℝ := fun j ↦
    ((L + (j + 1) : ℕ) : ℝ) ^ (ε - 1 / 4 - k)
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hqxq : (qx : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hL : 0 < L := by
    simpa only [L] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) (by linarith : 0 < Q) ε
  have hA : 0 ≤ A := by
    dsimp only [A, qx, qy]
    exact dfiEquation29XSingleMainTailL1Coefficient_nonneg
      hC.le hD hQ (zero_lt_one.trans_le hf.one_le_X)
        (zero_lt_one.trans_le hf.one_le_Y) ha hb hqx hqy
  have hpAll : Summable (fun n : ℕ ↦
      (n : ℝ) ^ (ε - 1 / 4 - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp : Summable p := by
    have hs := (summable_nat_add_iff (L + 1)).2 hpAll
    simpa only [p, Nat.cast_add, Nat.cast_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hF : Summable F := by
    have hs := (summable_nat_add_iff (L + 1)).2
      (summable_norm_dfiVoronoiDualTerm qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)))
    simpa only [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hEach (j : ℕ) : F j ≤ A * p j := by
    have hn : 0 < L + (j + 1) := by omega
    have hpnt := hPoint a b q qx qy ha hb hq inferInstance inferInstance
      hqxq hqQ h branch (L + (j + 1)) hn
    simpa only [F, p, A, qx, qy, E] using hpnt
  unfold dfiVoronoiDualMassAfterEarly
  calc
    (∑' j : ℕ, F j) ≤ ∑' j : ℕ, A * p j :=
      hF.tsum_le_tsum hEach (hp.mul_left A)
    _ = A * ∑' j : ℕ, p j := by rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4)) := by
      gcongr
      simpa only [p] using
        tsum_nat_add_rpow_sub_quarter_sub_nat_le ε L k hL hk
    _ = _ := by rfl

/-- Sum the actual `x`-dual/`y`-main recurrence estimate beyond DFI's
literal equation-(29) cutoff.  The theorem is uniform in the coprime
coefficients and shift because its constants were fixed from the source
profiles before those parameters were introduced. -/
theorem exists_dfiEquation29_xSingleMainTailMass_source_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let L := dfiEquation29SourceXCutoff a X Q ε
        dfiVoronoiDualMassAfterEarly qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) L ≤
          dfiEquation29XSingleMainTailCoefficient
              C D k Q X Y a b q qx qy *
            ((L : ℝ) ^ (ε + 3 / 4 - k) /
              ((k : ℝ) - ε - 3 / 4)) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_xMain_source_power_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h branch
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  let A := dfiEquation29XSingleMainTailCoefficient
    C D k Q X Y a b q qx qy
  let F : ℕ → ℝ := fun j ↦
    ‖dfiVoronoiDualTerm qx branch
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) (L + (j + 1))‖
  let p : ℕ → ℝ := fun j ↦
    ((L + (j + 1) : ℕ) : ℝ) ^ (ε - 1 / 4 - k)
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hqxq : (qx : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hL : 0 < L := by
    simpa only [L] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) w.Q_pos ε
  have hA : 0 ≤ A := by
    dsimp only [A, qx, qy]
    exact dfiEquation29XSingleMainTailCoefficient_nonneg hC.le hD w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) ha hb (NeZero.pos q) hqx hqy
  have hpAll : Summable (fun n : ℕ ↦
      (n : ℝ) ^ (ε - 1 / 4 - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp : Summable p := by
    have hs := (summable_nat_add_iff (L + 1)).2 hpAll
    simpa only [p, Nat.cast_add, Nat.cast_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hF : Summable F := by
    have hs := (summable_nat_add_iff (L + 1)).2
      (summable_norm_dfiVoronoiDualTerm qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)))
    simpa only [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hEach (j : ℕ) : F j ≤ A * p j := by
    have hn : 0 < L + (j + 1) := by omega
    have hpnt := hPoint a b q qx qy ha hb hq inferInstance inferInstance
      hqxq hqQ h branch (L + (j + 1)) hn
    simpa only [F, p, A, qx, qy, E] using hpnt
  unfold dfiVoronoiDualMassAfterEarly
  calc
    (∑' j : ℕ, F j) ≤ ∑' j : ℕ, A * p j :=
      hF.tsum_le_tsum hEach (hp.mul_left A)
    _ = A * ∑' j : ℕ, p j := by rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4)) := by
      gcongr
      simpa only [p] using
        tsum_nat_add_rpow_sub_quarter_sub_nat_le ε L k hL hk
    _ = _ := by rfl

/-- Sum the source-sharp symmetric `x`-main/`y`-dual recurrence estimate
beyond DFI's literal equation-(29) cutoff. -/
theorem exists_dfiEquation29_ySingleMainTailMass_source_l1_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let L := dfiEquation29SourceYCutoff b Y Q ε
        dfiVoronoiDualMassAfterEarly qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L ≤
          dfiEquation29YSingleMainTailL1Coefficient
              C D k Q X Y a b qx qy *
            ((L : ℝ) ^ (ε + 3 / 4 - k) /
              ((k : ℝ) - ε - 3 / 4)) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_yMain_source_l1_power_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h branch
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  let A := dfiEquation29YSingleMainTailL1Coefficient
    C D k Q X Y a b qx qy
  let F : ℕ → ℝ := fun j ↦
    ‖dfiVoronoiDualTerm qy branch
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
        (L + (j + 1))‖
  let p : ℕ → ℝ := fun j ↦
    ((L + (j + 1) : ℕ) : ℝ) ^ (ε - 1 / 4 - k)
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hqyq : (qy : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le b q
  have hL : 0 < L := by
    simpa only [L] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 0 < Q) ε
  have hA : 0 ≤ A := by
    dsimp only [A, qx, qy]
    exact dfiEquation29YSingleMainTailL1Coefficient_nonneg
      hC.le hD hQ (zero_lt_one.trans_le hf.one_le_X)
        (zero_lt_one.trans_le hf.one_le_Y) ha hb hqx hqy
  have hpAll : Summable (fun n : ℕ ↦
      (n : ℝ) ^ (ε - 1 / 4 - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp : Summable p := by
    have hs := (summable_nat_add_iff (L + 1)).2 hpAll
    simpa only [p, Nat.cast_add, Nat.cast_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hF : Summable F := by
    have hs := (summable_nat_add_iff (L + 1)).2
      (summable_norm_dfiVoronoiDualTerm qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)))
    simpa only [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hEach (j : ℕ) : F j ≤ A * p j := by
    have hn : 0 < L + (j + 1) := by omega
    have hpnt := hPoint a b q qx qy ha hb hq inferInstance inferInstance
      hqyq hqQ h branch (L + (j + 1)) hn
    simpa only [F, p, A, qx, qy, E] using hpnt
  unfold dfiVoronoiDualMassAfterEarly
  calc
    (∑' j : ℕ, F j) ≤ ∑' j : ℕ, A * p j :=
      hF.tsum_le_tsum hEach (hp.mul_left A)
    _ = A * ∑' j : ℕ, p j := by rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4)) := by
      gcongr
      simpa only [p] using
        tsum_nat_add_rpow_sub_quarter_sub_nat_le ε L k hL hk
    _ = _ := by rfl

/-- Symmetric source-cutoff tail sum for the actual
`x`-main/`y`-dual branch. -/
theorem exists_dfiEquation29_ySingleMainTailMass_source_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ)
        (branch : DFIVoronoiDualBranch),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
        let L := dfiEquation29SourceYCutoff b Y Q ε
        dfiVoronoiDualMassAfterEarly qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L ≤
          dfiEquation29YSingleMainTailCoefficient
              C D k Q X Y a b q qx qy *
            ((L : ℝ) ^ (ε + 3 / 4 - k) /
              ((k : ℝ) - ε - 3 / 4)) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_yMain_source_power_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h branch
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  let A := dfiEquation29YSingleMainTailCoefficient
    C D k Q X Y a b q qx qy
  let F : ℕ → ℝ := fun j ↦
    ‖dfiVoronoiDualTerm qy branch
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
        (L + (j + 1))‖
  let p : ℕ → ℝ := fun j ↦
    ((L + (j + 1) : ℕ) : ℝ) ^ (ε - 1 / 4 - k)
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hqyq : (qy : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le b q
  have hL : 0 < L := by
    simpa only [L] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) w.Q_pos ε
  have hA : 0 ≤ A := by
    dsimp only [A, qx, qy]
    exact dfiEquation29YSingleMainTailCoefficient_nonneg hC.le hD w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) ha hb (NeZero.pos q) hqx hqy
  have hpAll : Summable (fun n : ℕ ↦
      (n : ℝ) ^ (ε - 1 / 4 - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp : Summable p := by
    have hs := (summable_nat_add_iff (L + 1)).2 hpAll
    simpa only [p, Nat.cast_add, Nat.cast_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hF : Summable F := by
    have hs := (summable_nat_add_iff (L + 1)).2
      (summable_norm_dfiVoronoiDualTerm qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)))
    simpa only [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hEach (j : ℕ) : F j ≤ A * p j := by
    have hn : 0 < L + (j + 1) := by omega
    have hpnt := hPoint a b q qx qy ha hb hq inferInstance inferInstance
      hqyq hqQ h branch (L + (j + 1)) hn
    simpa only [F, p, A, qx, qy, E] using hpnt
  unfold dfiVoronoiDualMassAfterEarly
  calc
    (∑' j : ℕ, F j) ≤ ∑' j : ℕ, A * p j :=
      hF.tsum_le_tsum hEach (hp.mul_left A)
    _ = A * ∑' j : ℕ, p j := by rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ (ε + 3 / 4 - k) /
        ((k : ℝ) - ε - 3 / 4)) := by
      gcongr
      simpa only [p] using
        tsum_nat_add_rpow_sub_quarter_sub_nat_le ε L k hL hk
    _ = _ := by rfl

/-- Source-sharp complete two-sign `x`-dual/`y`-main tail, including the
literal Weil--Estermann factor from equation (25). -/
theorem exists_dfiEquation29_xSingleTailWeilTotal_source_l1_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let L := dfiEquation29SourceXCutoff a X Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f ψ h) a b h ε q ≤
          W * (∑ _branch : DFIVoronoiDualBranch,
            dfiEquation29XSingleMainTailL1Coefficient
                C D k Q X Y a b qx qy *
              ((L : ℝ) ^ (ε + 3 / 4 - k) /
                ((k : ℝ) - ε - 3 / 4))) := by
  obtain ⟨C, D, hC, hD, hTail⟩ :=
    exists_dfiEquation29_xSingleMainTailMass_source_l1_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29XSingleTailWeilTotal, dif_neg (NeZero.ne q)]
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  simpa only [qx, qy, E, L] using
    hTail a b q ha hb hq hqQ h branch

/-- Source-sharp complete symmetric one-sided tail, including the literal
Weil--Estermann factor from equation (25). -/
theorem exists_dfiEquation29_ySingleTailWeilTotal_source_l1_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let L := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f ψ h) a b h ε q ≤
          W * (∑ _branch : DFIVoronoiDualBranch,
            dfiEquation29YSingleMainTailL1Coefficient
                C D k Q X Y a b qx qy *
              ((L : ℝ) ^ (ε + 3 / 4 - k) /
                ((k : ℝ) - ε - 3 / 4))) := by
  obtain ⟨C, D, hC, hD, hTail⟩ :=
    exists_dfiEquation29_ySingleMainTailMass_source_l1_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hQ hUQ ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29YSingleTailWeilTotal, dif_neg (NeZero.ne q)]
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  simpa only [qx, qy, E, L] using
    hTail a b q ha hb hq hqQ h branch

/-- Complete two-sign `x`-dual/`y`-main tail, including the literal
Weil--Estermann factor from equation (25). -/
theorem exists_dfiEquation29_xSingleTailWeilTotal_source_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let L := dfiEquation29SourceXCutoff a X Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f ψ h) a b h ε q ≤
          W * (∑ _branch : DFIVoronoiDualBranch,
            dfiEquation29XSingleMainTailCoefficient
                C D k Q X Y a b q qx qy *
              ((L : ℝ) ^ (ε + 3 / 4 - k) /
                ((k : ℝ) - ε - 3 / 4))) := by
  obtain ⟨C, D, hC, hD, hTail⟩ :=
    exists_dfiEquation29_xSingleMainTailMass_source_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceXCutoff a X Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29XSingleTailWeilTotal, dif_neg (NeZero.ne q)]
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qx branch
        (fun x ↦ dfiVoronoiMainTerm qy (E x)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  simpa only [qx, qy, E, L] using
    hTail a b q ha hb hq hqQ h branch

/-- Complete symmetric one-sided equation-(29) tail, including its literal
Weil--Estermann factor. -/
theorem exists_dfiEquation29_ySingleTailWeilTotal_source_bound_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → (_hq : NeZero q) →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ),
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let L := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f ψ h) a b h ε q ≤
          W * (∑ _branch : DFIVoronoiDualBranch,
            dfiEquation29YSingleMainTailCoefficient
                C D k Q X Y a b q qx qy *
              ((L : ℝ) ^ (ε + 3 / 4 - k) /
                ((k : ℝ) - ε - 3 / 4))) := by
  obtain ⟨C, D, hC, hD, hTail⟩ :=
    exists_dfiEquation29_ySingleMainTailMass_source_bound_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b q ha hb hq hqQ h
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f ψ h) a b h q
  let L := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29YSingleTailWeilTotal, dif_neg (NeZero.ne q)]
  change W * (∑ branch : DFIVoronoiDualBranch,
      dfiVoronoiDualMassAfterEarly qy branch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro branch _
  simpa only [qx, qy, E, L] using
    hTail a b q ha hb hq hqQ h branch

/-- Real-exponent form of the preceding tail estimate.  It is used with
`κ=k/2` after the geometric-mean argument in the double-tail corner. -/
theorem tsum_nat_add_rpow_sub_quarter_sub_real_le
    (ε : ℝ) (L : ℕ) (κ : ℝ) (hL : 0 < L)
    (hκ : ε + 3 / 4 < κ) :
    (∑' j : ℕ, ((L + (j + 1) : ℕ) : ℝ) ^
        (ε - 1 / 4 - κ)) ≤
      (L : ℝ) ^ (ε + 3 / 4 - κ) /
        (κ - ε - 3 / 4) := by
  let p : ℝ := κ + 1 / 4 - ε
  have hp : 1 < p := by dsimp [p]; linarith
  have htail := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := p) (Nat.cast_pos.mpr hL) hp
  calc
    (∑' j : ℕ, ((L + (j + 1) : ℕ) : ℝ) ^
        (ε - 1 / 4 - κ)) =
      ∑' j : ℕ, ((L : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ (-p) := by
        apply tsum_congr
        intro j
        rw [show ((L + (j + 1) : ℕ) : ℝ) =
          (L : ℝ) + ((j + 1 : ℕ) : ℝ) by push_cast; rfl]
        congr 1
        dsimp [p]
        ring
    _ ≤ (L : ℝ) ^ (1 - p) / (p - 1) := htail
    _ = (L : ℝ) ^ (ε + 3 / 4 - κ) /
        (κ - ε - 3 / 4) := by
      rw [show 1 - p = ε + 3 / 4 - κ by dsimp [p]; ring,
        show p - 1 = κ - ε - 3 / 4 by dsimp [p]; ring]

/-- Sum the shifted-contour estimate over the part of the equation-(29)
complement having retained first frequency and tail second frequency. -/
theorem dfiEquation29DoubleRetainedXTailYMass_le_of_shifted_bound
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly k : ℕ) (hLy : 0 < Ly)
    (hk : 0 < k) (A : ℝ) (hA : 0 ≤ A)
    (hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (-(1 : ℝ) - k) *
          (n : ℝ) ^ (-(1 : ℝ) - k)) :
    dfiEquation29DoubleRetainedXTailYMass
        qx xBranch qy yBranch E Lx Ly ≤
      A * (1 + 1 / (k : ℝ)) *
        ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  let p : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-(1 : ℝ) - k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : Summable p := by
    dsimp [p]
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp0 (n : ℕ) : 0 ≤ p n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTailSummable : Summable (fun j : ℕ ↦ p (Ly + (j + 1))) := by
    have hs := (summable_nat_add_iff (Ly + 1)).2 hp
    simpa [p, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hs
  have hTail := tsum_nat_add_rpow_neg_one_sub_nat_le Ly k hLy hk
  have hEach (m : ℕ) (hm : 0 < m) :
      (∑' j : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m (Ly + (j + 1))‖) ≤
        (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
    have hAmpAll := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    have hAmp : Summable (fun j : ℕ ↦
        ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m (Ly + (j + 1))‖) := by
      have hs := (summable_nat_add_iff (Ly + 1)).2 hAmpAll
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    calc
      _ ≤ ∑' j : ℕ, (A * p m) * p (Ly + (j + 1)) :=
        hAmp.tsum_le_tsum (fun j ↦ by
          have hn : 0 < Ly + (j + 1) := by omega
          simpa [p, mul_assoc] using hPoint m (Ly + (j + 1)) hm hn)
          (hTailSummable.mul_left (A * p m))
      _ = (A * p m) * ∑' j : ℕ, p (Ly + (j + 1)) := by rw [tsum_mul_left]
      _ ≤ (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
        gcongr
  unfold dfiEquation29DoubleRetainedXTailYMass
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Lx,
        (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hEach m (Finset.mem_Icc.mp hm).1
    _ = (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        ∑ m ∈ Finset.Icc 1 Lx, p m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (∑' m : ℕ, p m) := by
      gcongr
      exact hp.sum_le_tsum (Finset.Icc 1 Lx) (fun n hn ↦ hp0 n)
    _ ≤ (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (1 + 1 / (k : ℝ)) := by
      gcongr
      exact tsum_natCast_rpow_neg_one_sub_nat_le k hk
    _ = _ := by ring

/-- Source-strength retained-`x`/tail-`y` estimate with the physical
quarter exponent on the retained frequency and the recurrence exponent on
the tail frequency. -/
theorem dfiEquation29DoubleRetainedXTailYMass_le_of_source_bound
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly k : ℕ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (hLy : 0 < Ly) (hk : ε + 3 / 4 < (k : ℝ))
    (A : ℝ) (hA : 0 ≤ A)
    (hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (ε - 1 / 4) *
          (n : ℝ) ^ (ε - 1 / 4 - k)) :
    dfiEquation29DoubleRetainedXTailYMass
        qx xBranch qy yBranch E Lx Ly ≤
      A * ((3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)) *
        ((Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)) := by
  let px : ℕ → ℝ := fun m ↦ (m : ℝ) ^ (ε - 1 / 4)
  let py : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (ε - 1 / 4 - k)
  let Sx : ℝ := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
  let Ty : ℝ := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  have hpy : Summable py := by
    apply Real.summable_nat_rpow.mpr
    dsimp [py]
    linarith
  have hpyTail : Summable (fun j : ℕ ↦ py (Ly + (j + 1))) := by
    have hs := (summable_nat_add_iff (Ly + 1)).2 hpy
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hSx : ∑ m ∈ Finset.Icc 1 Lx, px m ≤ Sx := by
    simpa only [px, Sx] using
      sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε Lx
  have hTy : (∑' j : ℕ, py (Ly + (j + 1))) ≤ Ty := by
    simpa only [py, Ty] using
      tsum_nat_add_rpow_sub_quarter_sub_nat_le ε Ly k hLy hk
  have hTy₀ : 0 ≤ Ty :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hTy
  have hEach (m : ℕ) (hm : 0 < m) :
      (∑' j : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m (Ly + (j + 1))‖) ≤
        A * px m * Ty := by
    have hAmpAll := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    have hAmp : Summable (fun j : ℕ ↦
        ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m (Ly + (j + 1))‖) := by
      have hs := (summable_nat_add_iff (Ly + 1)).2 hAmpAll
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    calc
      _ ≤ ∑' j : ℕ, (A * px m) * py (Ly + (j + 1)) :=
        hAmp.tsum_le_tsum (fun j ↦ by
          have hn : 0 < Ly + (j + 1) := by omega
          simpa only [px, py, mul_assoc] using
            hPoint m (Ly + (j + 1)) hm hn)
          (hpyTail.mul_left (A * px m))
      _ = (A * px m) * ∑' j : ℕ, py (Ly + (j + 1)) := by
        rw [tsum_mul_left]
      _ ≤ A * px m * Ty := by gcongr
  unfold dfiEquation29DoubleRetainedXTailYMass
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Lx, A * px m * Ty := by
      apply Finset.sum_le_sum
      intro m hm
      exact hEach m (Finset.mem_Icc.mp hm).1
    _ = A * (∑ m ∈ Finset.Icc 1 Lx, px m) * Ty := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ A * Sx * Ty := by gcongr
    _ = _ := by rfl

/-- Sum the shifted-contour estimate over the part of the equation-(29)
complement having tail first frequency and unrestricted second frequency. -/
theorem dfiEquation29DoubleTailXAllYMass_le_of_shifted_bound
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx k : ℕ) (hLx : 0 < Lx)
    (hk : 0 < k) (A : ℝ) (hA : 0 ≤ A)
    (hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (-(1 : ℝ) - k) *
          (n : ℝ) ^ (-(1 : ℝ) - k)) :
    dfiEquation29DoubleTailXAllYMass
        qx xBranch qy yBranch E Lx ≤
      A * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
        (1 + 1 / (k : ℝ)) := by
  let p : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-(1 : ℝ) - k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : Summable p := by
    dsimp [p]
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp0 (n : ℕ) : 0 ≤ p n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTailSummable : Summable (fun i : ℕ ↦ p (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hp
    simpa [p, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hs
  have hTail := tsum_nat_add_rpow_neg_one_sub_nat_le Lx k hLx hk
  have hMass := tsum_natCast_rpow_neg_one_sub_nat_le k hk
  have hInner (m : ℕ) (hm : 0 < m) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m n‖) ≤ (A * p m) * (1 + 1 / (k : ℝ)) := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    calc
      _ ≤ ∑' n : ℕ, (A * p m) * p n :=
        hAmp.tsum_le_tsum (fun n ↦ by
          by_cases hn : n = 0
          · subst n
            have hzero : dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m 0 = 0 := by
              simp [dfiEquation24DoubleDualMellinAmplitude,
                dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]
            rw [hzero]
            simp only [norm_zero]
            exact mul_nonneg (mul_nonneg hA (hp0 m)) (hp0 0)
          · exact hPoint m n hm (Nat.pos_of_ne_zero hn))
          (hp.mul_left (A * p m))
      _ = (A * p m) * ∑' n : ℕ, p n := by rw [tsum_mul_left]
      _ ≤ (A * p m) * (1 + 1 / (k : ℝ)) := by gcongr
  unfold dfiEquation29DoubleTailXAllYMass
  have hAmpOuter := summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    (E := E) qx xBranch qy yBranch
  have hAmpTail : Summable (fun i : ℕ ↦
      ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
        (Lx + (i + 1)) n‖) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hAmpOuter
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  calc
    _ ≤ ∑' i : ℕ, (A * p (Lx + (i + 1))) *
        (1 + 1 / (k : ℝ)) :=
      hAmpTail.tsum_le_tsum (fun i ↦ hInner (Lx + (i + 1)) (by omega))
        ((hTailSummable.mul_left A).mul_right (1 + 1 / (k : ℝ)))
    _ = (A * ∑' i : ℕ, p (Lx + (i + 1))) *
        (1 + 1 / (k : ℝ)) := by
      rw [← tsum_mul_left, tsum_mul_right]
    _ ≤ (A * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (1 + 1 / (k : ℝ)) := by gcongr

/-- Refined estimate for the outer tail.  The retained part of the inner
frequency uses the one-sided `x` recurrence; the inner tail uses the
geometric-mean recurrence.  This is the summable four-region form of DFI
equation (29). -/
theorem dfiEquation29DoubleTailXAllYMass_le_of_source_split
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly k : ℕ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (hLx : 0 < Lx) (hLy : 0 < Ly)
    (hk : 2 * ε + 3 / 2 < (k : ℝ))
    (Ax Ag : ℝ) (hAx : 0 ≤ Ax) (hAg : 0 ≤ Ag)
    (hxPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Ax * (m : ℝ) ^ (ε - 1 / 4 - k) *
          (n : ℝ) ^ (ε - 1 / 4))
    (hgPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Ag * (m : ℝ) ^ (ε - 1 / 4 - (k : ℝ) / 2) *
          (n : ℝ) ^ (ε - 1 / 4 - (k : ℝ) / 2)) :
    dfiEquation29DoubleTailXAllYMass
        qx xBranch qy yBranch E Lx ≤
      Ax * ((Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)) *
        ((3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)) +
      Ag * ((Lx : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)) *
        ((Ly : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)) := by
  let e : ℝ := ε - 1 / 4
  let s : ℝ := ε - 1 / 4 - (k : ℝ) / 2
  let px : ℕ → ℝ := fun m ↦ (m : ℝ) ^ (e - k)
  let pg : ℕ → ℝ := fun m ↦ (m : ℝ) ^ s
  let Fy : ℝ := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
  let Tx : ℝ := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Gx : ℝ := (Lx : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
    ((k : ℝ) / 2 - ε - 3 / 4)
  let Gy : ℝ := (Ly : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
    ((k : ℝ) / 2 - ε - 3 / 4)
  have hkx : ε + 3 / 4 < (k : ℝ) := by linarith
  have hkg : ε + 3 / 4 < (k : ℝ) / 2 := by linarith
  have hpx : Summable px := by
    apply Real.summable_nat_rpow.mpr
    dsimp [px, e]
    linarith
  have hpg : Summable pg := by
    apply Real.summable_nat_rpow.mpr
    dsimp [pg, s]
    linarith
  have hpxTail : Summable (fun i : ℕ ↦ px (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hpx
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hpgTail : Summable (fun i : ℕ ↦ pg (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hpg
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hSumY : ∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ e ≤ Fy := by
    simpa only [e, Fy] using
      sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε Ly
  have hTx : (∑' i : ℕ, px (Lx + (i + 1))) ≤ Tx := by
    simpa only [px, e, Tx] using
      tsum_nat_add_rpow_sub_quarter_sub_nat_le ε Lx k hLx hkx
  have hGx : (∑' i : ℕ, pg (Lx + (i + 1))) ≤ Gx := by
    simpa only [pg, s, Gx] using
      tsum_nat_add_rpow_sub_quarter_sub_real_le
        ε Lx ((k : ℝ) / 2) hLx hkg
  have hGy : (∑' j : ℕ,
      ((Ly + (j + 1) : ℕ) : ℝ) ^ s) ≤ Gy := by
    simpa only [s, Gy] using
      tsum_nat_add_rpow_sub_quarter_sub_real_le
        ε Ly ((k : ℝ) / 2) hLy hkg
  have hFy₀ : 0 ≤ Fy := by dsimp [Fy]; positivity
  have hTx₀ : 0 ≤ Tx :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hTx
  have hGx₀ : 0 ≤ Gx :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hGx
  have hGy₀ : 0 ≤ Gy :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hGy
  have hpgYTail : Summable (fun j : ℕ ↦
      ((Ly + (j + 1) : ℕ) : ℝ) ^ s) := by
    have hs : Summable (fun n : ℕ ↦ (n : ℝ) ^ s) := by
      apply Real.summable_nat_rpow.mpr
      dsimp [s]
      linarith
    have ht := (summable_nat_add_iff (Ly + 1)).2 hs
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  have hRow (m : ℕ) (hm : 0 < m) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
        Ax * px m * Fy + Ag * pg m * Gy := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    have hzero : ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m 0‖ = 0 := by
      simp [dfiEquation24DoubleDualMellinAmplitude,
        dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]
    rw [Summable.tsum_eq_sum_Icc_add_tail_of_zero hAmp hzero Ly]
    apply add_le_add
    · calc
        _ ≤ ∑ n ∈ Finset.Icc 1 Ly, Ax * px m * (n : ℝ) ^ e := by
          apply Finset.sum_le_sum
          intro n hnMem
          have hn : 0 < n := (Finset.mem_Icc.mp hnMem).1
          simpa only [px, e, mul_assoc] using hxPoint m n hm hn
        _ = (Ax * px m) * ∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ e := by
          rw [Finset.mul_sum]
        _ ≤ Ax * px m * Fy := by
          gcongr
    · have hAmpTail : Summable (fun j : ℕ ↦
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m (Ly + (j + 1))‖) := by
          have hs := (summable_nat_add_iff (Ly + 1)).2 hAmp
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      calc
        _ ≤ ∑' j : ℕ, (Ag * pg m) *
            ((Ly + (j + 1) : ℕ) : ℝ) ^ s :=
          hAmpTail.tsum_le_tsum (fun j ↦ by
            have hn : 0 < Ly + (j + 1) := by omega
            simpa only [pg, s, mul_assoc] using
              hgPoint m (Ly + (j + 1)) hm hn)
            (hpgYTail.mul_left (Ag * pg m))
        _ = (Ag * pg m) * ∑' j : ℕ,
            ((Ly + (j + 1) : ℕ) : ℝ) ^ s := by rw [tsum_mul_left]
        _ ≤ Ag * pg m * Gy := by gcongr
  unfold dfiEquation29DoubleTailXAllYMass
  have hAmpOuter := summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    (E := E) qx xBranch qy yBranch
  have hAmpTail : Summable (fun i : ℕ ↦
      ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E (Lx + (i + 1)) n‖) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hAmpOuter
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hMajorant : Summable (fun i : ℕ ↦
      Ax * px (Lx + (i + 1)) * Fy +
        Ag * pg (Lx + (i + 1)) * Gy) :=
    ((hpxTail.mul_left Ax).mul_right Fy).add
      ((hpgTail.mul_left Ag).mul_right Gy)
  calc
    _ ≤ ∑' i : ℕ, (Ax * px (Lx + (i + 1)) * Fy +
          Ag * pg (Lx + (i + 1)) * Gy) :=
      hAmpTail.tsum_le_tsum
        (fun i ↦ hRow (Lx + (i + 1)) (by omega)) hMajorant
    _ = (Ax * (∑' i : ℕ, px (Lx + (i + 1))) * Fy) +
        (Ag * (∑' i : ℕ, pg (Lx + (i + 1))) * Gy) := by
      rw [Summable.tsum_add ((hpxTail.mul_left Ax).mul_right Fy)
        ((hpgTail.mul_left Ag).mul_right Gy)]
      rw [← tsum_mul_left, tsum_mul_right, ← tsum_mul_left, tsum_mul_right]
    _ ≤ Ax * Tx * Fy + Ag * Gx * Gy := by gcongr
    _ = _ := by rfl

/-- Refined outer-tail estimate when the double-tail corner is controlled
by a complete recurrence in each frequency.  In contrast with the
geometric-mean form, both tail sums use the full exponent `k`. -/
theorem dfiEquation29DoubleTailXAllYMass_le_of_source_full_recurrence
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly k : ℕ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (hLx : 0 < Lx) (hLy : 0 < Ly)
    (hk : ε + 3 / 4 < (k : ℝ))
    (Ax Axy : ℝ) (hAx : 0 ≤ Ax) (hAxy : 0 ≤ Axy)
    (hxPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Ax * (m : ℝ) ^ (ε - 1 / 4 - k) *
          (n : ℝ) ^ (ε - 1 / 4))
    (hxyPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        Axy * (m : ℝ) ^ (ε - 1 / 4 - k) *
          (n : ℝ) ^ (ε - 1 / 4 - k)) :
    dfiEquation29DoubleTailXAllYMass
        qx xBranch qy yBranch E Lx ≤
      Ax * ((Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)) *
        ((3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)) +
      Axy * ((Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)) *
        ((Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)) := by
  let e : ℝ := ε - 1 / 4
  let s : ℝ := ε - 1 / 4 - k
  let px : ℕ → ℝ := fun m ↦ (m : ℝ) ^ (e - k)
  let pxy : ℕ → ℝ := fun m ↦ (m : ℝ) ^ s
  let Fy : ℝ := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
  let Tx : ℝ := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Ty : ℝ := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  have hpx : Summable px := by
    apply Real.summable_nat_rpow.mpr
    dsimp [px, e]
    linarith
  have hpxy : Summable pxy := by
    apply Real.summable_nat_rpow.mpr
    dsimp [pxy, s]
    linarith
  have hpxTail : Summable (fun i : ℕ ↦ px (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hpx
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hpxyTail : Summable (fun i : ℕ ↦ pxy (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hpxy
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hpxyYTail : Summable (fun j : ℕ ↦
      ((Ly + (j + 1) : ℕ) : ℝ) ^ s) := by
    have hs : Summable (fun n : ℕ ↦ (n : ℝ) ^ s) := by
      apply Real.summable_nat_rpow.mpr
      dsimp [s]
      linarith
    have ht := (summable_nat_add_iff (Ly + 1)).2 hs
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  have hSumY : ∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ e ≤ Fy := by
    simpa only [e, Fy] using
      sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε Ly
  have hTx : (∑' i : ℕ, px (Lx + (i + 1))) ≤ Tx := by
    simpa only [px, e, Tx] using
      tsum_nat_add_rpow_sub_quarter_sub_nat_le ε Lx k hLx hk
  have hTy : (∑' j : ℕ,
      ((Ly + (j + 1) : ℕ) : ℝ) ^ s) ≤ Ty := by
    simpa only [s, Ty] using
      tsum_nat_add_rpow_sub_quarter_sub_nat_le ε Ly k hLy hk
  have hFy₀ : 0 ≤ Fy := by dsimp [Fy]; positivity
  have hTx₀ : 0 ≤ Tx :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hTx
  have hTy₀ : 0 ≤ Ty :=
    (tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hTy
  have hRow (m : ℕ) (hm : 0 < m) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
        Ax * px m * Fy + Axy * pxy m * Ty := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    have hzero : ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m 0‖ = 0 := by
      simp [dfiEquation24DoubleDualMellinAmplitude,
        dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]
    rw [Summable.tsum_eq_sum_Icc_add_tail_of_zero hAmp hzero Ly]
    apply add_le_add
    · calc
        _ ≤ ∑ n ∈ Finset.Icc 1 Ly, Ax * px m * (n : ℝ) ^ e := by
          apply Finset.sum_le_sum
          intro n hnMem
          have hn : 0 < n := (Finset.mem_Icc.mp hnMem).1
          simpa only [px, e, mul_assoc] using hxPoint m n hm hn
        _ = (Ax * px m) * ∑ n ∈ Finset.Icc 1 Ly, (n : ℝ) ^ e := by
          rw [Finset.mul_sum]
        _ ≤ Ax * px m * Fy := by gcongr
    · have hAmpTail : Summable (fun j : ℕ ↦
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m (Ly + (j + 1))‖) := by
          have hs := (summable_nat_add_iff (Ly + 1)).2 hAmp
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      calc
        _ ≤ ∑' j : ℕ, (Axy * pxy m) *
            ((Ly + (j + 1) : ℕ) : ℝ) ^ s :=
          hAmpTail.tsum_le_tsum (fun j ↦ by
            have hn : 0 < Ly + (j + 1) := by omega
            simpa only [pxy, s, mul_assoc] using
              hxyPoint m (Ly + (j + 1)) hm hn)
            (hpxyYTail.mul_left (Axy * pxy m))
        _ = (Axy * pxy m) * ∑' j : ℕ,
            ((Ly + (j + 1) : ℕ) : ℝ) ^ s := by rw [tsum_mul_left]
        _ ≤ Axy * pxy m * Ty := by gcongr
  unfold dfiEquation29DoubleTailXAllYMass
  have hAmpOuter := summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    (E := E) qx xBranch qy yBranch
  have hAmpTail : Summable (fun i : ℕ ↦
      ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E (Lx + (i + 1)) n‖) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hAmpOuter
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hMajorant : Summable (fun i : ℕ ↦
      Ax * px (Lx + (i + 1)) * Fy +
        Axy * pxy (Lx + (i + 1)) * Ty) :=
    ((hpxTail.mul_left Ax).mul_right Fy).add
      ((hpxyTail.mul_left Axy).mul_right Ty)
  calc
    _ ≤ ∑' i : ℕ, (Ax * px (Lx + (i + 1)) * Fy +
          Axy * pxy (Lx + (i + 1)) * Ty) :=
      hAmpTail.tsum_le_tsum
        (fun i ↦ hRow (Lx + (i + 1)) (by omega)) hMajorant
    _ = (Ax * (∑' i : ℕ, px (Lx + (i + 1))) * Fy) +
        (Axy * (∑' i : ℕ, pxy (Lx + (i + 1))) * Ty) := by
      rw [Summable.tsum_add ((hpxTail.mul_left Ax).mul_right Fy)
        ((hpxyTail.mul_left Axy).mul_right Ty)]
      rw [← tsum_mul_left, tsum_mul_right, ← tsum_mul_left, tsum_mul_right]
    _ ≤ Ax * Tx * Fy + Axy * Tx * Ty := by
      have hpxyEq : pxy = px := by
        funext r
        dsimp [pxy, px, s, e]
      rw [hpxyEq]
      gcongr
    _ = _ := by rfl

/-- Source-sharp equation-(29) estimate for one complete double-dual
branch.  The retained rectangle and all three disjoint complement pieces
are present, including the double-tail corner. -/
theorem exists_dfiEquation29_doubleDual_source_sharp_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ C Cy Dy Ky Cx Dx Kx : ℝ,
      0 ≤ C ∧ 0 < Cy ∧ 0 ≤ Dy ∧ 0 ≤ Ky ∧
      0 < Cx ∧ 0 ≤ Dx ∧ 0 ≤ Kx ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
        (xBranch yBranch : DFIVoronoiDualBranch),
      ∀ (q : ℕ) (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let Ax := dfiEquation29XTailCoefficient
          Cx Dx Kx k Q X Y a b q qx qy
        let Ay := dfiEquation29YTailCoefficient
          Cy Dy Ky k Q X Y a b q qx qy
        let Ag := Real.sqrt (Ax * Ay)
        let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
        let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
        let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Gx := (Lx : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)
        let Gy := (Ly : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)
        (∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (Lx : ℝ) ^ (3 / 4 + ε / 2) *
            (Ly : ℝ) ^ (3 / 4 + ε / 2) +
          Ay * Sx * Ty + Ax * Tx * Sy + Ag * Gx * Gy := by
  obtain ⟨C, hC, hRetained⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀
        (hε.trans (by norm_num))
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hKmass : 0 ≤ Kmass := by
    dsimp [Kmass]
    have hf0 := (hfC.finiteConstant_pos 0).le
    have hφ0 : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      simp [dfiCutoffFiniteConstant, (hφC.positive 0).le]
    have hw0 : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    positivity
  let Cret := C * Kmass
  have hCret : 0 ≤ Cret := mul_nonneg hC hKmass
  obtain ⟨Cy, Dy, Ky, hCy, hDy, hKy, hy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  obtain ⟨Cx, Dx, Kx, hCx, hDx, hKx, hx⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  refine ⟨Cret, Cy, Dy, Ky, Cx, Dx, Kx,
    hCret, hCy, hDy, hKy, hCx, hDx, hKx, ?_⟩
  intro a b ha hb h xBranch yBranch q hq hqQ
  dsimp only
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let Ax := dfiEquation29XTailCoefficient Cx Dx Kx k Q X Y a b q qx qy
  let Ay := dfiEquation29YTailCoefficient Cy Dy Ky k Q X Y a b q qx qy
  let Ag := Real.sqrt (Ax * Ay)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hAx : 0 ≤ Ax := dfiEquation29XTailCoefficient_nonneg
    hCx.le hDx hKx w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb (NeZero.pos q) hqx hqy
  have hAy : 0 ≤ Ay := dfiEquation29YTailCoefficient_nonneg
    hCy.le hDy hKy w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb (NeZero.pos q) hqx hqy
  have hAg : 0 ≤ Ag := Real.sqrt_nonneg _
  have hxPoint := hx a b q ha hb hq hqQ h xBranch yBranch
  have hyPoint := hy a b q ha hb hq hqQ h xBranch yBranch
  have hgPoint (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
    two_frequency_geometric_mean (norm_nonneg _) hAx hAy
      (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
      (by simpa only [qx, qy, E, Ax] using hxPoint m n hm hn)
      (by simpa only [qx, qy, E, Ay] using hyPoint m n hm hn)
  have hRet := hRetained a b ha hb h q hq xBranch yBranch
  have hTailY := dfiEquation29DoubleRetainedXTailYMass_le_of_source_bound
    qx xBranch qy yBranch E Lx Ly k ε hε₀ hε hLy (by linarith)
      Ay hAy (by
        intro m n hm hn
        simpa only [Ay, qx, qy, E] using hyPoint m n hm hn)
  have hTailX := dfiEquation29DoubleTailXAllYMass_le_of_source_split
    qx xBranch qy yBranch E Lx Ly k ε hε₀ hε hLx hLy hk
      Ax Ag hAx hAg
      (by
        intro m n hm hn
        simpa only [Ax, qx, qy, E] using hxPoint m n hm hn)
      (by
        intro m n hm hn
        simpa only [Ag] using hgPoint m n hm hn)
  rw [tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_eq_retained_add_tails
    qx xBranch qy yBranch E Lx Ly]
  have hRet' := hRet
  dsimp only [qx, qy, E, Lx, Ly] at hRet'
  have hAll := add_le_add (add_le_add hRet' hTailY) hTailX
  simpa only [Cret, Kmass, add_assoc, mul_assoc] using hAll

/-- Tail-only source-sharp form of DFI equation (29), after the two
Voronoi transforms and the equation-(25) Weil bound have been inserted.
The retained rectangle is deliberately absent: the right side consists
exactly of the retained-`x`/tail-`y` region, the tail-`x`/retained-`y`
region, and the double-tail corner. -/
theorem exists_dfiEquation29_doubleTail_source_sharp_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ Cy Dy Ky Cx Dx Kx : ℝ,
      0 < Cy ∧ 0 ≤ Dy ∧ 0 ≤ Ky ∧
      0 < Cx ∧ 0 ≤ Dx ∧ 0 ≤ Kx ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ),
      ∀ (q : ℕ) (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        let Ax := dfiEquation29XTailCoefficient
          Cx Dx Kx k Q X Y a b q qx qy
        let Ay := dfiEquation29YTailCoefficient
          Cy Dy Ky k Q X Y a b q qx qy
        let Ag := Real.sqrt (Ax * Ay)
        let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
        let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
        let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Gx := (Lx : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)
        let Gy := (Ly : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
          ((k : ℝ) / 2 - ε - 3 / 4)
        dfiEquation29DoubleTailWeilTotal X Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ _xb : DFIVoronoiDualBranch,
            ∑ _yb : DFIVoronoiDualBranch,
              (Ay * Sx * Ty + Ax * Tx * Sy + Ag * Gx * Gy)) := by
  obtain ⟨Cy, Dy, Ky, hCy, hDy, hKy, hy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  obtain ⟨Cx, Dx, Kx, hCx, hDx, hKx, hx⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  refine ⟨Cy, Dy, Ky, Cx, Dx, Kx,
    hCy, hDy, hKy, hCx, hDx, hKx, ?_⟩
  intro a b ha hb h q hq hqQ
  dsimp only
  letI : NeZero q := hq
  have hqpos : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let Ax := dfiEquation29XTailCoefficient Cx Dx Kx k Q X Y a b q qx qy
  let Ay := dfiEquation29YTailCoefficient Cy Dy Ky k Q X Y a b q qx qy
  let Ag := Real.sqrt (Ax * Ay)
  let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
  let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
  let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Gx := (Lx : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
    ((k : ℝ) / 2 - ε - 3 / 4)
  let Gy := (Ly : ℝ) ^ (ε + 3 / 4 - (k : ℝ) / 2) /
    ((k : ℝ) / 2 - ε - 3 / 4)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hAx : 0 ≤ Ax := dfiEquation29XTailCoefficient_nonneg
    hCx.le hDx hKx w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb hqpos (NeZero.pos qx) (NeZero.pos qy)
  have hAy : 0 ≤ Ay := dfiEquation29YTailCoefficient_nonneg
    hCy.le hDy hKy w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb hqpos (NeZero.pos qx) (NeZero.pos qy)
  have hAg : 0 ≤ Ag := Real.sqrt_nonneg _
  have hxPoint := hx a b q ha hb hq hqQ h
  have hyPoint := hy a b q ha hb hq hqQ h
  have hEach (xb yb : DFIVoronoiDualBranch) :
      dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx ≤
        Ay * Sx * Ty + Ax * Tx * Sy + Ag * Gx * Gy := by
    have hgPoint (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
      two_frequency_geometric_mean (norm_nonneg _) hAx hAy
        (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
        (by simpa only [qx, qy, E, Ax] using hxPoint xb yb m n hm hn)
        (by simpa only [qx, qy, E, Ay] using hyPoint xb yb m n hm hn)
    have hTailY := dfiEquation29DoubleRetainedXTailYMass_le_of_source_bound
      qx xb qy yb E Lx Ly k ε hε₀ hε hLy (by linarith)
        Ay hAy (by
          intro m n hm hn
          simpa only [Ay, qx, qy, E] using hyPoint xb yb m n hm hn)
    have hTailX := dfiEquation29DoubleTailXAllYMass_le_of_source_split
      qx xb qy yb E Lx Ly k ε hε₀ hε hLx hLy hk
        Ax Ag hAx hAg
        (by
          intro m n hm hn
          simpa only [Ax, qx, qy, E] using hxPoint xb yb m n hm hn)
        (by
          intro m n hm hn
          simpa only [Ag] using hgPoint m n hm hn)
    dsimp only [Sx, Sy, Tx, Ty, Gx, Gy]
    linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29DoubleTailWeilTotal, dif_neg hqpos.ne']
  change W * (∑ xb : DFIVoronoiDualBranch,
      ∑ yb : DFIVoronoiDualBranch,
        (dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx)) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro xb _
  apply Finset.sum_le_sum
  intro yb _
  exact hEach xb yb

/-- Tail-only source form of DFI equation (29) with the full mixed-derivative
recurrence in the double-tail corner.  The corner therefore has `k`
integrations by parts in each frequency, rather than the obsolete `k/2`
geometric-mean loss. -/
theorem exists_dfiEquation29_doubleTail_source_full_recurrence_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ Cy Dy Ky Cx Dx Kx K Cdiv : ℝ,
      0 < Cy ∧ 0 ≤ Dy ∧ 0 ≤ Ky ∧
      0 < Cx ∧ 0 ≤ Dx ∧ 0 ≤ Kx ∧ 0 < K ∧ 0 < Cdiv ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ),
      ∀ (q : ℕ) (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        let Ax := dfiEquation29XTailCoefficient
          Cx Dx Kx k Q X Y a b q qx qy
        let Ay := dfiEquation29YTailCoefficient
          Cy Dy Ky k Q X Y a b q qx qy
        let Axy := dfiEquation29FullRecurrenceCoefficient
          K Cdiv k Q X Y a b qx qy
        let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
        let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
        let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        dfiEquation29DoubleTailWeilTotal X Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ _xb : DFIVoronoiDualBranch,
            ∑ _yb : DFIVoronoiDualBranch,
              (Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty)) := by
  obtain ⟨Cy, Dy, Ky, hCy, hDy, hKy, hy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_yTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  obtain ⟨Cx, Dx, Kx, hCx, hDx, hKx, hx⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_xTail_power_bound
      hf hfC hbox hφ hφC hscale w hwC hU ε hε₀ k
  obtain ⟨K, Cdiv, hK, hCdiv, hxy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_full_pointwise
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ k
  refine ⟨Cy, Dy, Ky, Cx, Dx, Kx, K, Cdiv,
    hCy, hDy, hKy, hCx, hDx, hKx, hK, hCdiv, ?_⟩
  intro a b ha hb h q hq hqQ
  dsimp only
  letI : NeZero q := hq
  have hqpos : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let Ax := dfiEquation29XTailCoefficient Cx Dx Kx k Q X Y a b q qx qy
  let Ay := dfiEquation29YTailCoefficient Cy Dy Ky k Q X Y a b q qx qy
  let Axy := dfiEquation29FullRecurrenceCoefficient
    K Cdiv k Q X Y a b qx qy
  let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
  let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
  let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hAx : 0 ≤ Ax := dfiEquation29XTailCoefficient_nonneg
    hCx.le hDx hKx w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb hqpos (NeZero.pos qx) (NeZero.pos qy)
  have hAy : 0 ≤ Ay := dfiEquation29YTailCoefficient_nonneg
    hCy.le hDy hKy w.Q_pos
      (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
      ha hb hqpos (NeZero.pos qx) (NeZero.pos qy)
  have hAxy : 0 ≤ Axy := by
    dsimp only [Axy]
    exact dfiEquation29FullRecurrenceCoefficient_nonneg
      hK.le hCdiv.le (by linarith)
        (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y) ha hb
  have hxPoint := hx a b q ha hb hq hqQ h
  have hyPoint := hy a b q ha hb hq hqQ h
  have hxyPoint := hxy a b q ha hb hq hqQ h
  have hEach (xb yb : DFIVoronoiDualBranch) :
      dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx ≤
        Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty := by
    have hTailY := dfiEquation29DoubleRetainedXTailYMass_le_of_source_bound
      qx xb qy yb E Lx Ly k ε hε₀ hε hLy (by linarith)
        Ay hAy (by
          intro m n hm hn
          simpa only [Ay, qx, qy, E] using hyPoint xb yb m n hm hn)
    have hTailX := dfiEquation29DoubleTailXAllYMass_le_of_source_full_recurrence
      qx xb qy yb E Lx Ly k ε hε₀ hε hLx hLy (by linarith)
        Ax Axy hAx hAxy
        (by
          intro m n hm hn
          simpa only [Ax, qx, qy, E] using hxPoint xb yb m n hm hn)
        (by
          intro m n hm hn
          simpa only [Axy, qx, qy, E] using hxyPoint xb yb m n hm hn)
    dsimp only [Sx, Sy, Tx, Ty]
    linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29DoubleTailWeilTotal, dif_neg hqpos.ne']
  change W * (∑ xb : DFIVoronoiDualBranch,
      ∑ yb : DFIVoronoiDualBranch,
        (dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx)) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro xb _
  apply Finset.sum_le_sum
  intro yb _
  exact hEach xb yb

/-- The full-recurrence equation-(29) double complement summed over the
literal delta-method modulus set.  This is the direct modulus-sum consumer
of the preceding pointwise theorem; no tail certificate is assumed. -/
theorem exists_sum_dfiEquation29_doubleTail_source_full_recurrence_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ Cy Dy Ky Cx Dx Kx K Cdiv : ℝ,
      0 < Cy ∧ 0 ≤ Dy ∧ 0 ≤ Ky ∧
      0 < Cx ∧ 0 ≤ Dx ∧ 0 ≤ Kx ∧ 0 < K ∧ 0 < Cdiv ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ),
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
      ∑ q ∈ dfiEquation22Moduli Q,
        if hq : q = 0 then 0 else
          letI : NeZero q := ⟨hq⟩
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let Lx := dfiEquation29SourceXCutoff a X Q ε
          let Ly := dfiEquation29SourceYCutoff b Y Q ε
          let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
            (q.divisors.card : ℝ)
          let Ax := dfiEquation29XTailCoefficient
            Cx Dx Kx k Q X Y a b q qx qy
          let Ay := dfiEquation29YTailCoefficient
            Cy Dy Ky k Q X Y a b q qx qy
          let Axy := dfiEquation29FullRecurrenceCoefficient
            K Cdiv k Q X Y a b qx qy
          let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
          let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
          let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
            ((k : ℝ) - ε - 3 / 4)
          let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
            ((k : ℝ) - ε - 3 / 4)
          W * (4 * (Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty)) := by
  obtain ⟨Cy, Dy, Ky, Cx, Dx, Kx, K, Cdiv,
      hCy, hDy, hKy, hCx, hDx, hKx, hK, hCdiv, hPoint⟩ :=
    exists_dfiEquation29_doubleTail_source_full_recurrence_bound
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε k hk
  refine ⟨Cy, Dy, Ky, Cx, Dx, Kx, K, Cdiv,
    hCy, hDy, hKy, hCx, hDx, hKx, hK, hCdiv, ?_⟩
  intro a b ha hb h
  apply Finset.sum_le_sum
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  have hp := hPoint a b ha hb h q inferInstance hqQ
  rw [dif_neg hqPos.ne']
  dsimp only at hp ⊢
  have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
    Nat.cast_ofNat] at hp
  convert hp using 1
  all_goals ring

/-- Correct source form of the complement in DFI (29).  Both one-sided
regions retain the physical equation-(30) mixed-`L¹` mass; only the corner
uses recurrence in both frequencies. -/
theorem exists_dfiEquation29_doubleTail_source_mixed_recurrence_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ Ky Cdivy Kx Cdivx Kxy Cdivxy : ℝ,
      0 < Ky ∧ 0 < Cdivy ∧ 0 < Kx ∧ 0 < Cdivx ∧
      0 < Kxy ∧ 0 < Cdivxy ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ),
      ∀ (q : ℕ) (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        let Ax := dfiEquation29MixedXTailCoefficient
          Kx Cdivx k Q X Y a b qx qy
        let Ay := dfiEquation29MixedYTailCoefficient
          Ky Cdivy k Q X Y a b qx qy
        let Axy := dfiEquation29FullRecurrenceCoefficient
          Kxy Cdivxy k Q X Y a b qx qy
        let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
        let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
        let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
          ((k : ℝ) - ε - 3 / 4)
        dfiEquation29DoubleTailWeilTotal X Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ _xb : DFIVoronoiDualBranch,
            ∑ _yb : DFIVoronoiDualBranch,
              (Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty)) := by
  obtain ⟨Ky, Cdivy, hKy, hCdivy, hy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_yTail_pointwise
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ k
  obtain ⟨Kx, Cdivx, hKx, hCdivx, hx⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_mixed_xTail_pointwise
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ k
  obtain ⟨Kxy, Cdivxy, hKxy, hCdivxy, hxy⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_full_pointwise
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ k
  refine ⟨Ky, Cdivy, Kx, Cdivx, Kxy, Cdivxy,
    hKy, hCdivy, hKx, hCdivx, hKxy, hCdivxy, ?_⟩
  intro a b ha hb h q hq hqQ
  dsimp only
  letI : NeZero q := hq
  have hqpos : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let Ax := dfiEquation29MixedXTailCoefficient Kx Cdivx k Q X Y a b qx qy
  let Ay := dfiEquation29MixedYTailCoefficient Ky Cdivy k Q X Y a b qx qy
  let Axy := dfiEquation29FullRecurrenceCoefficient
    Kxy Cdivxy k Q X Y a b qx qy
  let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
  let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
  let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
    ((k : ℝ) - ε - 3 / 4)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hAx : 0 ≤ Ax := by
    dsimp only [Ax]
    exact dfiEquation29MixedXTailCoefficient_nonneg hKx.le hCdivx.le
      (by linarith) (zero_le_one.trans hf.one_le_X)
        (zero_le_one.trans hf.one_le_Y) ha hb
  have hAy : 0 ≤ Ay := by
    dsimp only [Ay]
    exact dfiEquation29MixedYTailCoefficient_nonneg hKy.le hCdivy.le
      (by linarith) (zero_le_one.trans hf.one_le_X)
        (zero_le_one.trans hf.one_le_Y) ha hb
  have hAxy : 0 ≤ Axy := by
    dsimp only [Axy]
    exact dfiEquation29FullRecurrenceCoefficient_nonneg hKxy.le hCdivxy.le
      (by linarith) (zero_le_one.trans hf.one_le_X)
        (zero_le_one.trans hf.one_le_Y) ha hb
  have hxPoint := hx a b q ha hb hq hqQ h
  have hyPoint := hy a b q ha hb hq hqQ h
  have hxyPoint := hxy a b q ha hb hq hqQ h
  have hEach (xb yb : DFIVoronoiDualBranch) :
      dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx ≤
        Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty := by
    have hTailY := dfiEquation29DoubleRetainedXTailYMass_le_of_source_bound
      qx xb qy yb E Lx Ly k ε hε₀ hε hLy (by linarith)
        Ay hAy (by
          intro m n hm hn
          simpa only [Ay, qx, qy, E] using hyPoint xb yb m n hm hn)
    have hTailX := dfiEquation29DoubleTailXAllYMass_le_of_source_full_recurrence
      qx xb qy yb E Lx Ly k ε hε₀ hε hLx hLy (by linarith)
        Ax Axy hAx hAxy
        (by
          intro m n hm hn
          simpa only [Ax, qx, qy, E] using hxPoint xb yb m n hm hn)
        (by
          intro m n hm hn
          simpa only [Axy, qx, qy, E] using hxyPoint xb yb m n hm hn)
    dsimp only [Sx, Sy, Tx, Ty]
    linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  rw [dfiEquation29DoubleTailWeilTotal, dif_neg hqpos.ne']
  change W * (∑ xb : DFIVoronoiDualBranch,
      ∑ yb : DFIVoronoiDualBranch,
        (dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx)) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro xb _
  apply Finset.sum_le_sum
  intro yb _
  exact hEach xb yb

/-- The corrected mixed-recurrence equation-(29) complement summed over the
literal delta-method modulus set. -/
theorem exists_sum_dfiEquation29_doubleTail_source_mixed_recurrence_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 2 * ε + 3 / 2 < (k : ℝ)) :
    ∃ Ky Cdivy Kx Cdivx Kxy Cdivxy : ℝ,
      0 < Ky ∧ 0 < Cdivy ∧ 0 < Kx ∧ 0 < Cdivx ∧
      0 < Kxy ∧ 0 < Cdivxy ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ),
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
      ∑ q ∈ dfiEquation22Moduli Q,
        if hq : q = 0 then 0 else
          letI : NeZero q := ⟨hq⟩
          let qx := (dfiReducedModulus a q).denominator
          let qy := (dfiReducedModulus b q).denominator
          let Lx := dfiEquation29SourceXCutoff a X Q ε
          let Ly := dfiEquation29SourceYCutoff b Y Q ε
          let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
            (q.divisors.card : ℝ)
          let Ax := dfiEquation29MixedXTailCoefficient
            Kx Cdivx k Q X Y a b qx qy
          let Ay := dfiEquation29MixedYTailCoefficient
            Ky Cdivy k Q X Y a b qx qy
          let Axy := dfiEquation29FullRecurrenceCoefficient
            Kxy Cdivxy k Q X Y a b qx qy
          let Sx := (3 / 4 + ε)⁻¹ * (Lx : ℝ) ^ (3 / 4 + ε)
          let Sy := (3 / 4 + ε)⁻¹ * (Ly : ℝ) ^ (3 / 4 + ε)
          let Tx := (Lx : ℝ) ^ (ε + 3 / 4 - k) /
            ((k : ℝ) - ε - 3 / 4)
          let Ty := (Ly : ℝ) ^ (ε + 3 / 4 - k) /
            ((k : ℝ) - ε - 3 / 4)
          W * (4 * (Ay * Sx * Ty + Ax * Tx * Sy + Axy * Tx * Ty)) := by
  obtain ⟨Ky, Cdivy, Kx, Cdivx, Kxy, Cdivxy,
      hKy, hCdivy, hKx, hCdivx, hKxy, hCdivxy, hPoint⟩ :=
    exists_dfiEquation29_doubleTail_source_mixed_recurrence_bound
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε k hk
  refine ⟨Ky, Cdivy, Kx, Cdivx, Kxy, Cdivxy,
    hKy, hCdivy, hKx, hCdivx, hKxy, hCdivxy, ?_⟩
  intro a b ha hb h
  apply Finset.sum_le_sum
  intro q hqMem
  have hqPos : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  have hqQ : (q : ℝ) ≤ 2 * Q :=
    (mem_dfiEquation22Moduli_iff q).1 hqMem |>.2.le
  letI : NeZero q := ⟨hqPos.ne'⟩
  have hp := hPoint a b ha hb h q inferInstance hqQ
  rw [dif_neg hqPos.ne']
  dsimp only at hp ⊢
  have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
    Nat.cast_ofNat] at hp
  convert hp using 1
  all_goals ring

/-- One complete double-dual branch at the literal source cutoffs: the
retained rectangle is estimated on `Re s = Re t = 3/4`, and the exact two
complement regions are estimated after an arbitrary common left shift. -/
theorem exists_dfiEquation29_doubleDual_source_full_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (k : ℕ) (hk : 0 < k)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let A := B * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
          dfiEquation28BiSeparatedNonposShiftMajorant K (2 * (k + 1) + 4)
            (-(1 / 2 : ℝ) - k) Q X Y a b q
        (∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤
          C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
            (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
            (X / a) ^ (-(1 / 4 : ℝ)) *
            (Y / b) ^ (-(1 / 4 : ℝ)) *
            (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
            (Lx : ℝ) ^ (3 / 4 + ε / 2) *
            (Ly : ℝ) ^ (3 / 4 + ε / 2) +
          A * (1 + 1 / (k : ℝ)) *
            ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) +
          A * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
            (1 + 1 / (k : ℝ)) := by
  obtain ⟨C, hC, hRetained⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound
      hf hbox hφ hscale w hQ hU a b ha hb h ε hε₀ hε
  obtain ⟨B, hB, K, hK, hShift⟩ :=
    exists_dfiEquation24DoubleDualMellinAmplitude_source_shifted_bound
      hf hbox hφ hscale w hU k xBranch yBranch
  refine ⟨C, B, hC, hB, K, hK, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let A := B * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
    (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
    dfiEquation28BiSeparatedNonposShiftMajorant K (2 * (k + 1) + 4)
      (-(1 / 2 : ℝ) - k) Q X Y a b q
  have hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (-(1 : ℝ) - k) *
          (n : ℝ) ^ (-(1 : ℝ) - k) := by
    intro m n hm hn
    simpa only [qx, qy, E, A] using
      hShift a b q hq0 ha hb hqQ h m n hm hn
  have hA : 0 ≤ A := by
    have hone := hPoint 1 1 (by norm_num) (by norm_num)
    exact (norm_nonneg _).trans (by simpa [Real.one_rpow] using hone)
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hRet := hRetained q hq0 xBranch yBranch
  have hTailY := dfiEquation29DoubleRetainedXTailYMass_le_of_shifted_bound
    qx xBranch qy yBranch E Lx Ly k hLy hk A hA hPoint
  have hTailX := dfiEquation29DoubleTailXAllYMass_le_of_shifted_bound
    qx xBranch qy yBranch E Lx k hLx hk A hA hPoint
  rw [tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_eq_retained_add_tails
    qx xBranch qy yBranch E Lx Ly]
  exact add_le_add
    (add_le_add (by simpa only [qx, qy, E, Lx, Ly] using hRet) hTailY)
    hTailX

/-- All four exact double-dual complement regions after equation (29),
with branchwise constants exposed and no omitted frequency corner. -/
theorem exists_dfiEquation29_doubleTailWeilTotal_le_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ B : DFIVoronoiDualBranch → DFIVoronoiDualBranch → ℝ,
      (∀ xb yb, 0 ≤ B xb yb) ∧
      ∃ K : DFIVoronoiDualBranch → DFIVoronoiDualBranch → ℕ → ℕ → ℝ,
      (∀ xb yb i j, 0 < K xb yb i j) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        let A := fun xb yb ↦ B xb yb *
          (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
          dfiEquation28BiSeparatedNonposShiftMajorant (K xb yb) (2 * (k + 1) + 4)
            (-(1 / 2 : ℝ) - k) Q X Y a b q
        dfiEquation29DoubleTailWeilTotal X Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ xb : DFIVoronoiDualBranch,
            ∑ yb : DFIVoronoiDualBranch,
              (A xb yb * (1 + 1 / (k : ℝ)) *
                  ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) +
                A xb yb * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
                  (1 + 1 / (k : ℝ)))) := by
  choose B hB K hK hShift using fun xb : DFIVoronoiDualBranch ↦
    fun yb : DFIVoronoiDualBranch ↦
      exists_dfiEquation24DoubleDualMellinAmplitude_source_shifted_bound_of_profiles
        hf hfC hbox hφ hφC hscale w hwC hU k xb yb
  refine ⟨B, hB, K, hK, ?_⟩
  intro q hq0 hqQ
  dsimp only
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let Lx := dfiEquation29SourceXCutoff a X Q ε
  let Ly := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let A := fun xb yb ↦ B xb yb *
    (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
    (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
    dfiEquation28BiSeparatedNonposShiftMajorant (K xb yb) (2 * (k + 1) + 4)
      (-(1 / 2 : ℝ) - k) Q X Y a b q
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hLx : 0 < Lx := by
    simpa only [Lx] using dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) hQpos ε
  have hLy : 0 < Ly := by
    simpa only [Ly] using dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) hQpos ε
  have hEach (xb yb : DFIVoronoiDualBranch) :
      dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx ≤
        A xb yb * (1 + 1 / (k : ℝ)) *
            ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) +
          A xb yb * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
            (1 + 1 / (k : ℝ)) := by
    have hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
        ‖dfiEquation24DoubleDualMellinAmplitude qx xb qy yb E m n‖ ≤
          A xb yb * (m : ℝ) ^ (-(1 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
      intro m n hm hn
      simpa only [qx, qy, E, A] using
        hShift xb yb a b q hq0 ha hb hqQ h m n hm hn
    have hA : 0 ≤ A xb yb := by
      have hone := hPoint 1 1 (by norm_num) (by norm_num)
      exact (norm_nonneg _).trans (by simpa [Real.one_rpow] using hone)
    exact add_le_add
      (dfiEquation29DoubleRetainedXTailYMass_le_of_shifted_bound
        qx xb qy yb E Lx Ly k hLy hk (A xb yb) hA hPoint)
      (dfiEquation29DoubleTailXAllYMass_le_of_shifted_bound
        qx xb qy yb E Lx k hLx hk (A xb yb) hA hPoint)
  rw [dfiEquation29DoubleTailWeilTotal, dif_neg hq.ne']
  change W * (∑ xb : DFIVoronoiDualBranch,
      ∑ yb : DFIVoronoiDualBranch,
        (dfiEquation29DoubleRetainedXTailYMass qx xb qy yb E Lx Ly +
          dfiEquation29DoubleTailXAllYMass qx xb qy yb E Lx)) ≤ _
  apply mul_le_mul_of_nonneg_left _ hW
  apply Finset.sum_le_sum
  intro xb _
  apply Finset.sum_le_sum
  intro yb _
  exact hEach xb yb

/-- Backward-compatible fixed-instance projection of the profile-uniform
double-dual equation-(29) tail estimate. -/
theorem exists_dfiEquation29_doubleTailWeilTotal_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (ε : ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ B : DFIVoronoiDualBranch → DFIVoronoiDualBranch → ℝ,
      (∀ xb yb, 0 ≤ B xb yb) ∧
      ∃ K : DFIVoronoiDualBranch → DFIVoronoiDualBranch → ℕ → ℕ → ℝ,
      (∀ xb yb i j, 0 < K xb yb i j) ∧
      ∀ (q : ℕ) (_hq0 : NeZero q), (q : ℝ) ≤ 2 * Q →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let Lx := dfiEquation29SourceXCutoff a X Q ε
        let Ly := dfiEquation29SourceYCutoff b Y Q ε
        let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        let A := fun xb yb ↦ B xb yb *
          (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
          dfiEquation28BiSeparatedNonposShiftMajorant (K xb yb) (2 * (k + 1) + 4)
            (-(1 / 2 : ℝ) - k) Q X Y a b q
        dfiEquation29DoubleTailWeilTotal X Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          W * (∑ xb : DFIVoronoiDualBranch,
            ∑ yb : DFIVoronoiDualBranch,
              (A xb yb * (1 + 1 / (k : ℝ)) *
                  ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) +
                A xb yb * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
                  (1 + 1 / (k : ℝ)))) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  obtain ⟨Cw, hwC⟩ := w.exists_profile
  exact exists_dfiEquation29_doubleTailWeilTotal_le_of_profiles
    hf hfC hbox hφ hφC hscale w hwC hQ hU a b ha hb h ε k hk

/-- Source-uniform bound for either of the two `x`-dual/`y`-main branches
in equation (24), obtained from the retained and tail contours of equation
(29).  No transformed-sum estimate is assumed. -/
theorem exists_dfiEquation24_xSingleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ C₃ Ck : ℕ → ℝ, (∀ i, 0 < C₃ i) ∧ (∀ i, 0 < Ck i) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (L : ℕ), 0 < L →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          A * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q X Y
                a b q qy a b * (L : ℝ) ^ (3 / 4 + ε) +
            D * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28NonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C₃, hC₃, hRight⟩ :=
    exists_dfiEquation28_xMellin_yMain_source_bound
      hf hbox hφ hscale w hUQ (3 / 4) 6
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_xMellin_yMain_nonpos_source_bound
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (2 * (k + 1) + 4)
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD,
    C₃, Ck, hC₃, hCk, ?_⟩
  intro a b q hq0 ha hb hqQ h L hL
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hg : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) := by
    simpa only [qx, qy, E] using dfiEquation23XMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  have hRightLine := hRight a b q qy ha hb hq hqy hqQ h
  have hLeftLine := hLeft a b q qy ha hb hq hqy hqQ h
  let B₃ := dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q X Y
    a b q qy a b
  let Bk := dfiEquation28NonposMixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b
  have hRightLine' : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (((3 / 4 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    simpa only [E, B₃] using hRightLine
  have hLeftLine' : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    simpa only [E, Bk] using hLeftLine
  have hRightComplex : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    intro u
    have hCast : (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) := by norm_num
    simpa only [hCast] using hRightLine' u
  have hB₃ : 0 ≤ B₃ := by
    have hu := hRightLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hInitial := hTransform hg hRightComplex qx inferInstance
  have hRetained := hMass qx inferInstance branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) A₁ B₃ hInitial L
  have hAfter := hTail hg hBk hLeftLine' qx L inferInstance hL
  dsimp only [qx, qy, E]
  rw [← dfiVoronoiDualMassUpTo_add_after qx branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) L]
  exact add_le_add (by simpa [B₃, mul_assoc] using hRetained)
    (by simpa [Bk, mul_assoc] using hAfter)

/-- Source-uniform bound for either symmetric `x`-main/`y`-dual branch in
equation (24). -/
theorem exists_dfiEquation24_ySingleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ C₃ Ck : ℕ → ℝ, (∀ i, 0 < C₃ i) ∧ (∀ i, 0 < Ck i) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (L : ℕ), 0 < L →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          A * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q Y X
                a b q qx b a * (L : ℝ) ^ (3 / 4 + ε) +
            D * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28NonposMixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C₃, hC₃, hRight⟩ :=
    exists_dfiEquation28_yMellin_xMain_source_bound
      hf hbox hφ hscale w hUQ (3 / 4) 6
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_yMellin_xMain_nonpos_source_bound
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k)
        (by have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (2 * (k + 1) + 4)
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD,
    C₃, Ck, hC₃, hCk, ?_⟩
  intro a b q hq0 ha hb hqQ h L hL
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hg : DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
    simpa only [qx, qy, E] using dfiEquation23YMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  have hRightLine := hRight a b q qx ha hb hq hqx hqQ h
  have hLeftLine := hLeft a b q qx ha hb hq hqx hqQ h
  let B₃ := dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q Y X
    a b q qx b a
  let Bk := dfiEquation28NonposMixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a
  have hRightLine' : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (((3 / 4 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    simpa only [E, B₃] using hRightLine
  have hLeftLine' : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    simpa only [E, Bk] using hLeftLine
  have hRightComplex : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    intro u
    have hCast : (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) := by norm_num
    simpa only [hCast] using hRightLine' u
  have hB₃ : 0 ≤ B₃ := by
    have hu := hRightLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hInitial := hTransform hg hRightComplex qy inferInstance
  have hRetained := hMass qy inferInstance branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) A₁ B₃ hInitial L
  have hAfter := hTail hg hBk hLeftLine' qy L inferInstance hL
  dsimp only [qx, qy, E]
  rw [← dfiVoronoiDualMassUpTo_add_after qy branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L]
  exact add_le_add (by simpa [B₃, mul_assoc] using hRetained)
    (by simpa [Bk, mul_assoc] using hAfter)

/-- The literal nested majorant produced by equation (28) for the
two-variable Mellin transform on `Re s = Re t = -1/2`. -/
noncomputable def dfiEquation28BiMajorant
    (K : ℕ → ℕ → ℝ) (p : ℕ) (Q X Y : ℝ)
    (a b q : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ := (q : ℝ) * Q
  let M := Csum * qQ⁻¹
  let R := ((a : ℝ) * (b : ℝ)) / qQ
  dfiMellinProfileMajorant (Y / b) (2 * Y / b) (-(1 / 2)) p
    (dfiMellinProfileMajorant (X / a) (2 * X / a) (-(1 / 2)) p M R) R

/-- Each of the four source double-dual branches is bounded uniformly by
the actual equation-(28) bivariate Mellin majorant.  All smoothness, support,
and positivity hypotheses are discharged from equations (2), (21), and (23). -/
theorem exists_dfiEquation24_doubleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ h : ℤ,
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤
          ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
            dfiDivisorThreeHalfMass ^ 2 *
            ((32 * qx * dfiArchimedeanScale qx ^ 2) *
              (32 * qy * dfiArchimedeanScale qy ^ 2) *
              dfiEquation28BiMajorant K 6 Q X Y a b q *
              dfiCauchyPlaneMass) := by
  obtain ⟨K, hK, hBound⟩ :=
    exists_dfiEquation28_biMellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2)) (-(1 / 2)) 6
  refine ⟨K, hK, ?_⟩
  intro a b q hq0 ha hb hqQ h
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let M := dfiEquation28BiMajorant K 6 Q X Y a b q
  have hLine := hBound a b q ha hb hq hqQ h
  have hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M := by
    intro u v
    simpa [E, M, dfiEquation28BiMajorant] using hLine u v
  have hM : 0 ≤ M := by
    have hZero := hBi 0 0
    exact (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (norm_nonneg _)).trans hZero
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  simpa only [qx, qy, E, M] using
    tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
      hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch M hM hBi

/-- The four double-dual signs in DFI equation (24), recombined with one
source-uniform equation-(28) constant field. -/
theorem exists_dfiEquation24_doubleDualMass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ h : ℤ,
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        dfiEquation24DoubleDualMass q a b
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) ≤
          4 * (‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
            dfiDivisorThreeHalfMass ^ 2 *
            ((32 * qx * dfiArchimedeanScale qx ^ 2) *
              (32 * qy * dfiArchimedeanScale qy ^ 2) *
              dfiEquation28BiMajorant K 6 Q X Y a b q *
              dfiCauchyPlaneMass)) := by
  obtain ⟨K, hK, hBound⟩ :=
    exists_dfiEquation28_biMellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2)) (-(1 / 2)) 6
  refine ⟨K, hK, ?_⟩
  intro a b q hq0 ha hb hqQ h
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let M := dfiEquation28BiMajorant K 6 Q X Y a b q
  let Bnd := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
    dfiDivisorThreeHalfMass ^ 2 *
      ((32 * qx * dfiArchimedeanScale qx ^ 2) *
        (32 * qy * dfiArchimedeanScale qy ^ 2) * M * dfiCauchyPlaneMass)
  have hLine := hBound a b q ha hb hq hqQ h
  have hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M := by
    intro u v
    simpa [E, M, dfiEquation28BiMajorant] using hLine u v
  have hM : 0 ≤ M := by
    have hZero := hBi 0 0
    exact (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (norm_nonneg _)).trans hZero
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hEach (xBranch yBranch : DFIVoronoiDualBranch) :
      (∑' m : ℕ, ∑' n : ℕ,
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤ Bnd := by
    simpa only [Bnd] using
      tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
        hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch M hM hBi
  dsimp only [dfiEquation24DoubleDualMass]
  change (∑ yBranch : DFIVoronoiDualBranch,
      ∑ xBranch : DFIVoronoiDualBranch,
        ∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤ 4 * Bnd
  calc
    _ ≤ ∑ _yBranch : DFIVoronoiDualBranch,
        ∑ _xBranch : DFIVoronoiDualBranch, Bnd := by
      apply Finset.sum_le_sum
      intro yBranch _hy
      apply Finset.sum_le_sum
      intro xBranch _hx
      exact hEach xBranch yBranch
    _ = 4 * Bnd := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring

/-- Totalized literal eight-branch Weil majorant for one delta modulus. -/
noncomputable def dfiEquation24WeilMassTotal
    (q a b : ℕ) (h : ℤ) (E : ℝ → ℝ → ℂ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
      (dfiEquation24XSingleDualMass q a b E +
        dfiEquation24YSingleDualMass q a b E +
        dfiEquation24DoubleDualMass q a b E)

/-- Exact equation-(29) partition of the complete equation-(24) Weil
majorant into three retained pieces and their three complementary tails. -/
theorem dfiEquation24WeilMassTotal_eq_equation29_parts
    {Q : ℝ} (X Y : ℝ) (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b q : ℕ) (h : ℤ) (ε : ℝ) :
    dfiEquation24WeilMassTotal q a b h
        (dfiEquation23Weight w F a b h q) =
      dfiEquation29XSingleRetainedWeilTotal X w F a b h ε q +
      dfiEquation29XSingleTailWeilTotal X w F a b h ε q +
      dfiEquation29YSingleRetainedWeilTotal Y w F a b h ε q +
      dfiEquation29YSingleTailWeilTotal Y w F a b h ε q +
      dfiEquation29DoubleRetainedWeilTotal X Y w F a b h ε q +
      dfiEquation29DoubleTailWeilTotal X Y w F a b h ε q := by
  by_cases hq : q = 0
  · subst q
    simp [dfiEquation24WeilMassTotal,
      dfiEquation29XSingleRetainedWeilTotal,
      dfiEquation29XSingleTailWeilTotal,
      dfiEquation29YSingleRetainedWeilTotal,
      dfiEquation29YSingleTailWeilTotal,
      dfiEquation29DoubleRetainedWeilTotal,
      dfiEquation29DoubleTailWeilTotal]
  · letI : NeZero q := ⟨hq⟩
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    have hx := dfiEquation24XSingleDualMass_weil_eq_retained_add_tail
      X w F a b q h ε
    have hy := dfiEquation24YSingleDualMass_weil_eq_retained_add_tail
      Y w F a b q h ε
    have hd := dfiEquation24DoubleDualMass_weil_eq_retained_add_tail
      X Y w F a b q h ε
    rw [dfiEquation24WeilMassTotal, dif_neg hq]
    change W * (dfiEquation24XSingleDualMass q a b
        (dfiEquation23Weight w F a b h q) +
      dfiEquation24YSingleDualMass q a b
        (dfiEquation23Weight w F a b h q) +
      dfiEquation24DoubleDualMass q a b
        (dfiEquation23Weight w F a b h q)) = _
    calc
      _ = W * dfiEquation24XSingleDualMass q a b
            (dfiEquation23Weight w F a b h q) +
          W * dfiEquation24YSingleDualMass q a b
            (dfiEquation23Weight w F a b h q) +
          W * dfiEquation24DoubleDualMass q a b
            (dfiEquation23Weight w F a b h q) := by ring
      _ = _ := by
        rw [show W * dfiEquation24XSingleDualMass q a b
              (dfiEquation23Weight w F a b h q) =
            dfiEquation29XSingleRetainedWeilTotal X w F a b h ε q +
              dfiEquation29XSingleTailWeilTotal X w F a b h ε q by
              simpa only [W] using hx,
          show W * dfiEquation24YSingleDualMass q a b
              (dfiEquation23Weight w F a b h q) =
            dfiEquation29YSingleRetainedWeilTotal Y w F a b h ε q +
              dfiEquation29YSingleTailWeilTotal Y w F a b h ε q by
              simpa only [W] using hy,
          show W * dfiEquation24DoubleDualMass q a b
              (dfiEquation23Weight w F a b h q) =
            dfiEquation29DoubleRetainedWeilTotal X Y w F a b h ε q +
              dfiEquation29DoubleTailWeilTotal X Y w F a b h ε q by
              simpa only [W] using hd]
        ring

/-- DFI equation (25) after the standard divisor bound: the complete
Kloosterman factor is `Oε(q^(1+ε))`, uniformly in the shift. -/
theorem exists_dfiEquation25_weilFactor_epsilon_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) (_hq : NeZero q) (h : ℤ),
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ) ≤
        D * (q : ℝ) ^ (1 + ε) := by
  obtain ⟨D, hD, hdiv⟩ := divisorCountBound_native ε hε
  refine ⟨D, hD, ?_⟩
  intro q hq h
  letI : NeZero q := hq
  have hqN : 0 < q := NeZero.pos q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqN
  have hgcd : Nat.gcd ((-h : ZMod q).val) q ≤ q :=
    Nat.gcd_le_right _ hqN
  have hsqrt : Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) ≤
      Real.sqrt q := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hgcd)
  have hsquare : Real.sqrt (q : ℝ) * Real.sqrt q = q := by
    rw [← pow_two, Real.sq_sqrt hqR.le]
  have hdivq := hdiv q hqN
  calc
    Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)
        ≤ (Real.sqrt q * Real.sqrt q) * (q.divisors.card : ℝ) := by
          gcongr
    _ = (q : ℝ) * (q.divisors.card : ℝ) := by rw [hsquare]
    _ ≤ (q : ℝ) * (D * (q : ℝ) ^ ε) := by gcongr
    _ = D * (q : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hqR]
      simp
      ring

/-- The modulus average that is actually used after equations (25) and
(29).  Expanding the shift gcd over sparse divisors saves the square root
of the modulus range that a pointwise `gcd ≤ q` estimate would lose. -/
theorem sum_dfiEquation22Moduli_weil_gcd_divisor_average_le
    {Q : ℝ} (h : ℤ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        ((h.natAbs.divisors.card : ℝ) * Real.sqrt L *
          Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
  dsimp only
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ) =
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ _ := sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_le
      L h.natAbs (Int.natAbs_ne_zero.mpr hh) δ hδ

/-- Reduced-modulus normalization for either single-dual branch of DFI
equation (24). -/
theorem dfiEquation25_weil_mul_single_reduced_moduli_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ ≤
      Real.sqrt a * b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsquare : Real.sqrt q * Real.sqrt q = (q : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hq.le]
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hsqrt_le_q : Real.sqrt q ≤ (q : ℝ) := by
    nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hx := dfiReducedModulus_denominator_rpow_neg_half_le a q ha
  have hy := dfiReducedModulus_denominator_inv_le b q hb
  calc
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        (Real.sqrt a / Real.sqrt q) * ((b : ℝ) / q) := by
      gcongr
    _ = Real.sqrt a * b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / q) *
          (q.divisors.card : ℝ)) := by
      field_simp
    _ ≤ _ := by
      gcongr

/-- Reduced-modulus normalization for the double-dual branch of DFI
equation (24). -/
theorem dfiEquation25_weil_mul_double_reduced_moduli_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt a * Real.sqrt b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsquare : Real.sqrt q * Real.sqrt q = (q : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hq.le]
  have hx := dfiReducedModulus_denominator_rpow_neg_half_le a q ha
  have hy := dfiReducedModulus_denominator_rpow_neg_half_le b q hb
  calc
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        (Real.sqrt a / Real.sqrt q) * (Real.sqrt b / Real.sqrt q) := by
      gcongr
    _ = _ := by
      field_simp

/-- The complete finite equation-(24) error sum over the delta moduli is
bounded by the sum of the literal eight-branch Weil majorants. -/
theorem norm_sum_dfiEquation24ErrorTotal_le_weil_masses
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    ‖∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24ErrorTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q)‖ ≤
      ∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24WeilMassTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) := by
  calc
    _ ≤ ∑ q ∈ dfiEquation22Moduli Q,
        ‖dfiEquation24ErrorTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hq : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
      letI : NeZero q := ⟨hq.ne'⟩
      rw [dfiEquation24ErrorTotal, dif_neg hq.ne',
        dfiEquation24WeilMassTotal, dif_neg hq.ne']
      exact norm_dfiEquation24_source_error_le_weil_mul_masses
        w hf hbox hφ a b ha hb h q hq

/-- Exact source decomposition of the DFI remainder: the distance from the
infinite Ramanujan main series is at most the finite main-branch discrepancy
plus the complete equation-(24) error sum. -/
theorem norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le
    {Q U P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) :
    ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ ≤
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      ‖∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24ErrorTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)‖ := by
  rw [dfiDyadicShiftedDivisorSum_eq_sum_main_add_sum_error
    w hf hbox hφ hQU a b M N ha hb hM hN (h : ℤ)]
  simp only [Int.cast_natCast]
  calc
    _ =
      ‖((∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)) +
        (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24ErrorTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q))‖ := by
        congr 1
        ring
    _ ≤ _ := norm_add_le _ _

/-- Source-facing form of the exact equation-(24) decomposition.  The
central term is now the literal DFI equation-(3) series evaluated on `f`;
the auxiliary cutoff introduced in equation (21) has been eliminated by a
proved identity. -/
theorem norm_dfiDyadicShiftedDivisorSum_sub_sourceCentralSeries_le
    {Q U P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) :
    ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
        dfiEquation27CentralSeries a b h f‖ ≤
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      ‖∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24ErrorTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)‖ := by
  rw [← dfiEquation27CentralSeries_localizedWeight_eq hφ a b h]
  exact norm_dfiDyadicShiftedDivisorSum_sub_centralSeries_le
    w hf hbox hφ hQU a b M N h ha hb hM hN

end RiemannZeta.GuthMaynard
