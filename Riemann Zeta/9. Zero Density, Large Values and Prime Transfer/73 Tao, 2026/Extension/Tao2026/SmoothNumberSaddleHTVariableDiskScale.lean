import Tao2026.SmoothNumberSaddleHTVariableDisk
import GafniTao.PintzMajorantBounds

/-!
# Polynomial-log size of the HT variable-disk majorant

At the native width `w = c / D(A)`, the Pintz power in the disk majorant is
at most a fixed power of `log A`.  Hence the logarithm of the complete
normalized majorant is bounded by a fixed multiple of `log log A`.
-/

open Filter Topology

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTVariableDiskPolynomialExponent : ℝ :=
  GafniTao.pintzZetaExponentCoefficient + 2

noncomputable def smoothSaddleHTVariableDiskPolynomialCoefficient
    (c : ℝ) : ℝ :=
  2 + (1 + 1 / c) * GafniTao.pintzZetaEnvelopeCoefficient

noncomputable def smoothSaddleHTVariableDiskLogMajorantCoefficient
    (c : ℝ) : ℝ :=
  |Real.log (smoothSaddleHTVariableDiskPolynomialCoefficient c)| +
    smoothSaddleHTVariableDiskPolynomialExponent

theorem smoothSaddleHTVariableDiskPolynomialExponent_pos :
    0 < smoothSaddleHTVariableDiskPolynomialExponent := by
  unfold smoothSaddleHTVariableDiskPolynomialExponent
  linarith [GafniTao.pintzZetaExponentCoefficient_pos]

theorem smoothSaddleHTVariableDiskPolynomialCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < smoothSaddleHTVariableDiskPolynomialCoefficient c := by
  unfold smoothSaddleHTVariableDiskPolynomialCoefficient
  have hM : 0 < 1 + 1 / c := by positivity
  have hE := GafniTao.pintzZetaEnvelopeCoefficient_pos
  positivity

theorem smoothSaddleHTVariableDiskLogMajorantCoefficient_pos
    (c : ℝ) :
    0 < smoothSaddleHTVariableDiskLogMajorantCoefficient c := by
  unfold smoothSaddleHTVariableDiskLogMajorantCoefficient
  exact add_pos_of_nonneg_of_pos (abs_nonneg _)
    smoothSaddleHTVariableDiskPolynomialExponent_pos

/-- The balanced Ford radius turns the physical power exactly into a fixed
power of `log A`. -/
theorem rpow_fordVKRadius_exponent_eq_log_rpow
    {A : ℝ} (hA : Real.exp (Real.exp 1) ≤ A) :
    A ^ (GafniTao.pintzZetaExponentCoefficient *
        GafniTao.fordVKRadius A ^ (3 / 2 : ℝ)) =
      Real.log A ^ GafniTao.pintzZetaExponentCoefficient := by
  have hAPos : 0 < A := (Real.exp_pos _).trans_le hA
  have hlogLower : Real.exp 1 ≤ Real.log A := by
    simpa using Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos _) hAPos hA
  have hlogPos : 0 < Real.log A := (Real.exp_pos 1).trans_le hlogLower
  have hbalance := GafniTao.fordVKRadius_rpow_three_halves_mul_log hA
  rw [Real.rpow_def_of_pos hAPos, Real.rpow_def_of_pos hlogPos]
  congr 1
  calc
    Real.log A * (GafniTao.pintzZetaExponentCoefficient *
        GafniTao.fordVKRadius A ^ (3 / 2 : ℝ)) =
      GafniTao.pintzZetaExponentCoefficient *
        (GafniTao.fordVKRadius A ^ (3 / 2 : ℝ) * Real.log A) := by ring
    _ = GafniTao.pintzZetaExponentCoefficient *
        GafniTao.fordVKLogLog A := by rw [hbalance]
    _ = Real.log (Real.log A) *
        GafniTao.pintzZetaExponentCoefficient := by
      unfold GafniTao.fordVKLogLog
      ring

/-- Once `log log A` dominates the fixed VK constant, half the native width
is no larger than Ford's balanced radius. -/
theorem half_nativeVKWidth_le_fordVKRadius
    {c A : ℝ} (hA : Real.exp (Real.exp 1) ≤ A)
    (hcU : c / 2 ≤ GafniTao.fordVKLogLog A) :
    (c / GafniTao.vinogradovKorobovDenominator A) / 2 ≤
      GafniTao.fordVKRadius A := by
  have hD := GafniTao.vinogradovKorobovDenominator_pos hA
  rw [show (c / GafniTao.vinogradovKorobovDenominator A) / 2 =
      (c / 2) / GafniTao.vinogradovKorobovDenominator A by ring]
  rw [div_le_iff₀ hD]
  exact hcU.trans_eq (GafniTao.fordVKRadius_mul_denominator hA).symm

/-- The complete normalized disk majorant is a fixed-coefficient fixed
power of `log A` at the native VK width. -/
theorem smoothSaddleHTVariableDiskMajorant_native_le_log_rpow
    {c A : ℝ} (hc : 0 < c)
    (hA : Real.exp (Real.exp 1) ≤ A)
    (hcU : c / 2 ≤ GafniTao.fordVKLogLog A) :
    smoothSaddleHTVariableDiskMajorant
        (c / GafniTao.vinogradovKorobovDenominator A) A ≤
      smoothSaddleHTVariableDiskPolynomialCoefficient c *
        Real.log A ^ smoothSaddleHTVariableDiskPolynomialExponent := by
  let D := GafniTao.vinogradovKorobovDenominator A
  let w := c / D
  let L := Real.log A
  let P := GafniTao.pintzZetaExponentCoefficient
  let E := GafniTao.pintzZetaEnvelopeCoefficient
  have hAPos : 0 < A := (Real.exp_pos _).trans_le hA
  have hLExp : Real.exp 1 ≤ L := by
    simpa [L] using Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos _) hAPos hA
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hLOne : 1 ≤ L :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hLExp
  have hAOne : 1 ≤ A :=
    (show (1 : ℝ) ≤ Real.exp (Real.exp 1) from
      (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).le).trans hA
  have hDPos : 0 < D := by
    exact GafniTao.vinogradovKorobovDenominator_pos hA
  have hwPos : 0 < w := div_pos hc hDPos
  have hetaNonneg : 0 ≤ w / 2 := by positivity
  have hetaRadius : w / 2 ≤ GafniTao.fordVKRadius A := by
    simpa [w, D] using half_nativeVKWidth_le_fordVKRadius hA hcU
  have hPPos : 0 < P := by
    exact GafniTao.pintzZetaExponentCoefficient_pos
  have hENonneg : 0 ≤ E :=
    GafniTao.pintzZetaEnvelopeCoefficient_pos.le
  have hRadiusPos : 0 < GafniTao.fordVKRadius A :=
    GafniTao.fordVKRadius_pos A
  have hetaPow : (w / 2) ^ (3 / 2 : ℝ) ≤
      GafniTao.fordVKRadius A ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hetaNonneg hetaRadius (by norm_num)
  have hExponent : P * (w / 2) ^ (3 / 2 : ℝ) ≤
      P * GafniTao.fordVKRadius A ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hetaPow hPPos.le
  have hPower : A ^ (P * (w / 2) ^ (3 / 2 : ℝ)) ≤ L ^ P := by
    calc
      A ^ (P * (w / 2) ^ (3 / 2 : ℝ)) ≤
          A ^ (P * GafniTao.fordVKRadius A ^ (3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le
          hAOne hExponent
      _ = L ^ P := by
        simpa [L, P] using rpow_fordVKRadius_exponent_eq_log_rpow hA
  have hPhysical := GafniTao.pintzPhysicalZetaMajorant_le_power_log
    hetaNonneg hA
  have hHorizontalNonneg : 0 ≤
      GafniTao.pintzHorizontalZetaMajorant (w / 2) A :=
    GafniTao.pintzHorizontalZetaMajorant_nonneg
      ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hAOne)
  have hHorizontalPhysical :
      GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
        GafniTao.pintzPhysicalZetaMajorant (w / 2) A := by
    unfold GafniTao.pintzPhysicalZetaMajorant
    linarith
  have hHorizontal :
      GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
        E * L ^ (P + 1) := by
    calc
      GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
          GafniTao.pintzPhysicalZetaMajorant (w / 2) A :=
        hHorizontalPhysical
      _ ≤ E * A ^ (P * (w / 2) ^ (3 / 2 : ℝ)) * L := by
        simpa [E, P, L] using hPhysical
      _ ≤ E * L ^ P * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPower hENonneg) hLPos.le
      _ = E * L ^ (P + 1) := by
        rw [Real.rpow_add hLPos, Real.rpow_one]
        ring
  have hDLe : D ≤ L := by
    simpa [D, L] using GafniTao.vinogradovKorobovDenominator_le_log hA
  have hM : 1 + 1 / w ≤ (1 + 1 / c) * L := by
    have hc0 : c ≠ 0 := hc.ne'
    have hD0 : D ≠ 0 := hDPos.ne'
    have hrecip : 1 / w = D / c := by
      dsimp [w]
      field_simp
    rw [hrecip]
    have hdiv : D / c ≤ L / c :=
      div_le_div_of_nonneg_right hDLe hc.le
    have hLone : 1 ≤ L := hLOne
    calc
      1 + D / c ≤ L + L / c := add_le_add hLone hdiv
      _ = (1 + 1 / c) * L := by ring
  have hMNonneg : 0 ≤ 1 + 1 / w := by positivity
  have hMUpperNonneg : 0 ≤ (1 + 1 / c) * L := by positivity
  have hq : 1 ≤ L ^ (P + 2) := by
    apply Real.one_le_rpow hLOne
    dsimp [P]
    linarith [GafniTao.pintzZetaExponentCoefficient_pos]
  have hLPowMul : L * L ^ (P + 1) = L ^ (P + 2) := by
    calc
      L * L ^ (P + 1) = L ^ (1 : ℝ) * L ^ (P + 1) := by
        rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + (P + 1)) :=
        (Real.rpow_add hLPos (1 : ℝ) (P + 1)).symm
      _ = L ^ (P + 2) := by ring_nf
  have hprod :
      (1 + 1 / w) *
          GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
        ((1 + 1 / c) * E) * L ^ (P + 2) := by
    calc
      (1 + 1 / w) *
          GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
        ((1 + 1 / c) * L) * (E * L ^ (P + 1)) :=
          mul_le_mul hM hHorizontal hHorizontalNonneg hMUpperNonneg
      _ = ((1 + 1 / c) * E) * (L * L ^ (P + 1)) := by ring
      _ = ((1 + 1 / c) * E) * L ^ (P + 2) := by rw [hLPowMul]
  change 2 + (1 + 1 / w) *
      GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤ _
  calc
    2 + (1 + 1 / w) *
        GafniTao.pintzHorizontalZetaMajorant (w / 2) A ≤
      2 * L ^ (P + 2) + ((1 + 1 / c) * E) * L ^ (P + 2) :=
        add_le_add (by nlinarith) hprod
    _ = smoothSaddleHTVariableDiskPolynomialCoefficient c *
        L ^ smoothSaddleHTVariableDiskPolynomialExponent := by
      unfold smoothSaddleHTVariableDiskPolynomialCoefficient
        smoothSaddleHTVariableDiskPolynomialExponent
      dsimp [P, E, L]
      ring

/-- Taking logarithms converts the polynomial-log envelope into the desired
fixed multiple of `log log A`. -/
theorem log_smoothSaddleHTVariableDiskMajorant_native_le_logLog
    {c A : ℝ} (hc : 0 < c)
    (hA : Real.exp (Real.exp 1) ≤ A)
    (hcU : c / 2 ≤ GafniTao.fordVKLogLog A)
    (hUOne : 1 ≤ GafniTao.fordVKLogLog A) :
    Real.log (smoothSaddleHTVariableDiskMajorant
        (c / GafniTao.vinogradovKorobovDenominator A) A) ≤
      smoothSaddleHTVariableDiskLogMajorantCoefficient c *
        GafniTao.fordVKLogLog A := by
  let Q := smoothSaddleHTVariableDiskPolynomialCoefficient c
  let p := smoothSaddleHTVariableDiskPolynomialExponent
  let U := GafniTao.fordVKLogLog A
  have hAPos : 0 < A := (Real.exp_pos _).trans_le hA
  have hlogPos : 0 < Real.log A := by
    exact Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
      exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hA)
  have hQPos : 0 < Q :=
    smoothSaddleHTVariableDiskPolynomialCoefficient_pos hc
  have hpPos : 0 < p := smoothSaddleHTVariableDiskPolynomialExponent_pos
  have hmajorant := smoothSaddleHTVariableDiskMajorant_native_le_log_rpow
    hc hA hcU
  have hrightPos : 0 < Q * Real.log A ^ p :=
    mul_pos hQPos (Real.rpow_pos_of_pos hlogPos p)
  have hAOne : 1 ≤ A :=
    (show (1 : ℝ) ≤ Real.exp (Real.exp 1) from
      (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).le).trans hA
  have hmajorantPos : 0 < smoothSaddleHTVariableDiskMajorant
      (c / GafniTao.vinogradovKorobovDenominator A) A := by
    exact (one_lt_smoothSaddleHTVariableDiskMajorant
      (div_pos hc (GafniTao.vinogradovKorobovDenominator_pos hA))
      ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hAOne)).trans' zero_lt_one
  have hlogMono := Real.strictMonoOn_log.monotoneOn
    hmajorantPos
    hrightPos hmajorant
  have hlogRight :
      Real.log (Q * Real.log A ^ p) = Real.log Q + p * U := by
    rw [Real.log_mul hQPos.ne' (Real.rpow_pos_of_pos hlogPos p).ne',
      Real.log_rpow hlogPos]
    rfl
  rw [hlogRight] at hlogMono
  have hlogQ : Real.log Q ≤ |Real.log Q| * U := by
    calc
      Real.log Q ≤ |Real.log Q| := le_abs_self _
      _ ≤ |Real.log Q| * U := by
        nlinarith [abs_nonneg (Real.log Q)]
  calc
    Real.log (smoothSaddleHTVariableDiskMajorant
        (c / GafniTao.vinogradovKorobovDenominator A) A) ≤
      Real.log Q + p * U := hlogMono
    _ ≤ |Real.log Q| * U + p * U := by linarith
    _ = smoothSaddleHTVariableDiskLogMajorantCoefficient c * U := by
      unfold smoothSaddleHTVariableDiskLogMajorantCoefficient
      dsimp [Q, p, U]
      ring

/-- The numerical `FinalBound` coefficient is strictly positive. -/
theorem smoothSaddleHTVariableDiskLogDerivativeConstant_pos :
    0 < smoothSaddleHTVariableDiskLogDerivativeConstant := by
  unfold smoothSaddleHTVariableDiskLogDerivativeConstant
  have hratio : (1 : ℝ) < (99 / 100 : ℝ) / (19 / 20 : ℝ) := by
    norm_num
  have hlog : 0 < Real.log ((99 / 100 : ℝ) / (19 / 20 : ℝ)) :=
    Real.log_pos hratio
  have hgap : 0 < (99 / 100 : ℝ) ^ 2 / (19 / 20 : ℝ) - 19 / 20 := by
    norm_num
  positivity

/-- Fixed physical coefficient in the native-width high-height estimate. -/
noncomputable def smoothSaddleHTVariableDiskPhysicalCoefficient
    (c : ℝ) : ℝ :=
  smoothSaddleHTVariableDiskLogDerivativeConstant *
      smoothSaddleHTVariableDiskLogMajorantCoefficient c / (2 * c)

theorem smoothSaddleHTVariableDiskPhysicalCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < smoothSaddleHTVariableDiskPhysicalCoefficient c := by
  unfold smoothSaddleHTVariableDiskPhysicalCoefficient
  exact div_pos
    (mul_pos smoothSaddleHTVariableDiskLogDerivativeConstant_pos
      (smoothSaddleHTVariableDiskLogMajorantCoefficient_pos c))
    (mul_pos two_pos hc)

/-- Final high-height local theorem: at native VK width, the physical zeta
logarithmic derivative costs only `D(A) * log log A`. -/
theorem norm_riemannZeta_logDeriv_smoothSaddleHTSourceExponent_le_vk_logLog
    {c H beta t T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hc : 0 < c) (hHeight : H ≤ |t| + T)
    (hA : Real.exp (Real.exp 1) ≤ |t| + T)
    (hWidthHalf : c / GafniTao.vinogradovKorobovDenominator (|t| + T) ≤
      1 / 2)
    (ht : 5 ≤ |t|)
    (hRadius : 2 * (c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) ≤ T)
    (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ 2 * (c /
      GafniTao.vinogradovKorobovDenominator (|t| + T)) / 3)
    (hcU : c / 2 ≤ GafniTao.fordVKLogLog (|t| + T))
    (hUOne : 1 ≤ GafniTao.fordVKLogLog (|t| + T)) :
    ‖deriv riemannZeta (smoothSaddleHTSourceExponent beta t) /
        riemannZeta (smoothSaddleHTSourceExponent beta t)‖ ≤
      smoothSaddleHTVariableDiskPhysicalCoefficient c *
        (GafniTao.vinogradovKorobovDenominator (|t| + T) *
          GafniTao.fordVKLogLog (|t| + T)) := by
  let A := |t| + T
  let D := GafniTao.vinogradovKorobovDenominator A
  let U := GafniTao.fordVKLogLog A
  let w := c / D
  let C := smoothSaddleHTVariableDiskLogDerivativeConstant
  let K := smoothSaddleHTVariableDiskLogMajorantCoefficient c
  have hDPos : 0 < D := by
    exact GafniTao.vinogradovKorobovDenominator_pos (by simpa [A] using hA)
  have hwPos : 0 < w := div_pos hc hDPos
  have hraw :=
    norm_riemannZeta_logDeriv_smoothSaddleHTSourceExponent_le_variableDisk
      hZeroFree hHeight hwPos (by simpa [w, D, A] using hWidthHalf)
      ht (by simpa [w, D, A] using hRadius)
      (by simp [w, D, A]) hbeta
      (by simpa [w, D, A] using hbetaUpper)
  have hlog := log_smoothSaddleHTVariableDiskMajorant_native_le_logLog
    hc (by simpa [A] using hA) (by simpa [A, U] using hcU)
      (by simpa [A, U] using hUOne)
  have hCNonneg : 0 ≤ C :=
    smoothSaddleHTVariableDiskLogDerivativeConstant_pos.le
  have hdenPos : 0 < 2 * w := mul_pos two_pos hwPos
  calc
    ‖deriv riemannZeta (smoothSaddleHTSourceExponent beta t) /
        riemannZeta (smoothSaddleHTSourceExponent beta t)‖ ≤
      C * Real.log (smoothSaddleHTVariableDiskMajorant w A) / (2 * w) := by
        simpa [C, w, D, A] using hraw
    _ ≤ C * (K * U) / (2 * w) := by
      apply div_le_div_of_nonneg_right _ hdenPos.le
      exact mul_le_mul_of_nonneg_left (by simpa [K, U, w, D, A] using hlog)
        hCNonneg
    _ = smoothSaddleHTVariableDiskPhysicalCoefficient c * (D * U) := by
      unfold smoothSaddleHTVariableDiskPhysicalCoefficient
      dsimp [C, K, w]
      field_simp [hc.ne', hDPos.ne']
    _ = smoothSaddleHTVariableDiskPhysicalCoefficient c *
        (GafniTao.vinogradovKorobovDenominator (|t| + T) *
          GafniTao.fordVKLogLog (|t| + T)) := by
      rfl

end

end Tao2026
