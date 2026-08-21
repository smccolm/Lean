import RiemannZeta.GuthMaynard.HughesYoungNonLargeBounds
import RiemannZeta.GuthMaynard.HughesYoungNativeCentralAssembly

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native quantitative correction assembly

This module estimates the literal correction families in
`hughesYoungNativeOffDiagonalCorrection`.  No correction is discarded and
no absolute value is taken across the cancellation-preserving complete
central source.
-/

/-- The near-shift equation-(27) estimate does not require the lower bound
`64 ≤ U` used to enter DFI's error theorem.  That lower bound belongs only
to the discrepancy estimate.  For the central series itself one may take
the literal scale `P⁻¹ min(X,Y)`, which is positive and satisfies the
consumer's scale hypothesis with equality. -/
theorem exists_uniform_norm_hughesYoungNearPointwiseSignedCentralBox_noLarge :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T X Y P : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P →
      (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X →
      (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y →
      ‖hughesYoungNearPointwiseSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8) P X Y h k M N‖ ≤
        hughesYoungPointwiseSignedCentralMajorant
          Cγ C L T P X Y h k M N := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hsource⟩ :=
    exists_uniform_norm_hughesYoungSmallContourPointwiseSignedCentral
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T X Y P h k M N hT hX hY hh hk hP haX hbY
  let U : ℝ := P⁻¹ * min X Y
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hU : 0 < U := by
    dsimp only [U]
    exact mul_pos (inv_pos.mpr hP0) (lt_min hX0 hY0)
  have hs : ∀ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P := by
    intro r hr
    obtain ⟨hr0, hrY, hrP, _hrPos, _hrNeg⟩ :=
      hughesYoungNearShifts_dfi_conditions r hr
    exact ⟨hr0, hrY, hrP⟩
  unfold hughesYoungNearPointwiseSignedCentralBox
    hughesYoungPointwiseSignedCentralMajorant
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  exact hsource hT (div_nonneg hT0.le (by norm_num))
    hX hY hh hk hP hU le_rfl haX hbY hs

theorem hughesYoungFarBoxMajorant_nonneg
    {Cw : ℕ → ℝ} {D L T X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hsmall : 0 < hughesYoungSmallContour T)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hX : 0 < X) (hY : 0 < Y)
    (hCw : ∀ i, 0 < Cw i) :
    0 ≤ hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := by
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  unfold hughesYoungFarBoxMajorant
  positivity

theorem hughesYoungBoundaryBoxMajorant_eq_fivePow_mul
    {Cw : ℕ → ℝ} {D L T X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hX : 0 < X) (hY : 0 < Y)
    (hsmall : 0 < hughesYoungSmallContour T)
    (hCw : ∀ i, 0 < Cw i) :
    hughesYoungBoundaryBoxMajorant Cw D L j T X Y ε h k M N =
      5 ^ j * hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := by
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hfar : 0 ≤ hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N :=
    hughesYoungFarBoxMajorant_nonneg hT hsmall hD hL hX hY hCw
  have hratio : T / (5 * T) = (1 / 5 : ℝ) := by field_simp
  unfold hughesYoungBoundaryBoxMajorant
  rw [hratio, zpow_neg, zpow_natCast]
  have hfive : ((1 / 5 : ℝ) ^ j)⁻¹ = 5 ^ j := by
    rw [← inv_pow]
    norm_num
  rw [hfive, max_eq_right (mul_nonneg (by positivity) hfar)]

theorem hughesYoungCancelledFarBoxMajorant_eq_mul
    {Cw : ℕ → ℝ} {D L T P X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hP : 0 < P) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hX : 0 < X) (hY : 0 < Y)
    (hsmall : 0 < hughesYoungSmallContour T)
    (hCw : ∀ i, 0 < Cw i) :
    hughesYoungCancelledFarBoxMajorant Cw D L j T P X Y ε h k M N =
      (5 * T / P) ^ j *
        hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := by
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hfar : 0 ≤ hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N :=
    hughesYoungFarBoxMajorant_nonneg hT hsmall hD hL hX hY hCw
  unfold hughesYoungCancelledFarBoxMajorant
  rw [zpow_neg, zpow_natCast]
  have hratio : ((P / (5 * T)) ^ j)⁻¹ = (5 * T / P) ^ j := by
    rw [← inv_pow]
    congr 1
    field_simp
  rw [hratio, max_eq_right (mul_nonneg (by positivity) hfar)]

theorem hughesYoungSmallBoxMajorant_eq_mul
    {Cw : ℕ → ℝ} {D L T X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hX : 0 < X)
    (hsmall : 0 < hughesYoungSmallContour T)
    (hCw : ∀ i, 0 < Cw i) :
    hughesYoungSmallBoxMajorant Cw D L j T X Y ε h k M N =
      (10 * Y) ^ j *
        hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := by
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hfar : 0 ≤ hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N :=
    hughesYoungFarBoxMajorant_nonneg hT hsmall hD hL hX hY hCw
  unfold hughesYoungSmallBoxMajorant
  rw [zpow_neg, zpow_natCast]
  have hratio : ((((T / (2 * Y)) / (5 * T)) ^ j)⁻¹) = (10 * Y) ^ j := by
    rw [← inv_pow]
    congr 1
    field_simp
    norm_num
  rw [hratio, max_eq_right (mul_nonneg (by positivity) hfar)]

theorem fivePow_mul_hughesYoungDecay_eq
    {T : ℝ} (hT : 0 < T) (j : ℕ) :
    5 ^ j * ((T / 16)⁻¹) ^ j = (80 / T) ^ j := by
  rw [← mul_pow]
  congr 1
  field_simp
  norm_num

theorem cancelledFar_mul_hughesYoungDecay_eq
    {T P : ℝ} (hT : 0 < T) (hP : 0 < P) (j : ℕ) :
    (5 * T / P) ^ j * ((T / 16)⁻¹) ^ j = (80 / P) ^ j := by
  rw [← mul_pow]
  congr 1
  field_simp
  norm_num

theorem smallBox_mul_hughesYoungDecay_eq
    {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y) (j : ℕ) :
    (10 * Y) ^ j * ((T / 16)⁻¹) ^ j = (160 * Y / T) ^ j := by
  rw [← mul_pow]
  congr 1
  field_simp
  norm_num

theorem commonSmall_mul_hughesYoungDecay_eq
    {T P : ℝ} (hT : 0 < T) (hP : 0 < P) (j : ℕ) :
    (3200 * P) ^ j * ((T / 16)⁻¹) ^ j = (51200 * P / T) ^ j := by
  rw [← mul_pow]
  congr 1
  field_simp
  norm_num

/-- A common positive envelope for an equation-(65) box after its analytic
integration-by-parts factor has been left visible. -/
noncomputable def hughesYoungFarBoxPolynomialEnvelope
    (Cw : ℕ → ℝ) (D L : ℝ) (j : ℕ)
    (T ε A ell B : ℝ) : ℝ :=
  (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
      (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
      ((T / 16)⁻¹) ^ j) * L) *
    (D * B ^ (1 + ε) * B ^ (1 + ε) * A ^ 2 *
      (2 * ell) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
      (2 * ell) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T))

theorem hughesYoungFarBoxPolynomialEnvelope_nonneg
    {Cw : ℕ → ℝ} {D L : ℝ} {j : ℕ} {T ε A ell B : ℝ}
    (hT : 0 < T) (hsmall : 0 < hughesYoungSmallContour T)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hell : 0 ≤ ell) (hB : 0 ≤ B) :
    0 ≤ hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε A ell B := by
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  unfold hughesYoungFarBoxPolynomialEnvelope
  positivity

theorem hughesYoungFarBoxMajorant_le_polynomialEnvelope
    {Cw : ℕ → ℝ} {D L : ℝ} {j : ℕ}
    {T X Y ε A ell B : ℝ} {h k M N : ℕ}
    (hT : Real.exp 1 ≤ T) (hε : 0 ≤ ε)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hA : 0 ≤ A) (hell : 0 ≤ ell) (hB : 0 ≤ B)
    (hhpos : 0 < h) (hkpos : 0 < k)
    (hh : h ≤ ell) (hk : k ≤ ell)
    (hM : (M : ℝ) ≤ B) (hN : (N : ℝ) ≤ B)
    (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y)
    (hcoeffh : ‖shortMobiusSquareCoeff T h‖ ≤ A)
    (hcoeffk : ‖shortMobiusSquareCoeff T k‖ ≤ A) :
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N ≤
      hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε A ell B := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc := hughesYoungSmallContour_spec hT
  have hp : 0 ≤ (1 / 2 : ℝ) + hughesYoungSmallContour T := by
    linarith [hc.1]
  have hX0 : 0 < X := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hX
  have hY0 : 0 < Y := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hY
  have hhReduced : (hughesYoungReducedLeft h k : ℝ) ≤ ell := by
    have hred : (hughesYoungReducedLeft h k : ℝ) ≤ (h : ℝ) := by
      exact_mod_cast hughesYoungReducedLeft_le h k
    exact hred.trans hh
  have hkReduced : (hughesYoungReducedRight h k : ℝ) ≤ ell := by
    have hred : (hughesYoungReducedRight h k : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hughesYoungReducedRight_le h k
    exact hred.trans hk
  have hratioLeft :
      (hughesYoungReducedLeft h k : ℝ) / X ≤ 2 * ell := by
    apply (div_le_iff₀ hX0).2
    calc
      (hughesYoungReducedLeft h k : ℝ) ≤ ell := hhReduced
      _ ≤ (2 * ell) * X := by nlinarith
  have hratioRight :
      (hughesYoungReducedRight h k : ℝ) / Y ≤ 2 * ell := by
    apply (div_le_iff₀ hY0).2
    calc
      (hughesYoungReducedRight h k : ℝ) ≤ ell := hkReduced
      _ ≤ (2 * ell) * Y := by nlinarith
  have hscalar := norm_hughesYoungLocalizedStaticScalar_le_coefficients
    (T := T) hhpos hkpos
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ :=
    inv_nonneg.mpr hc.1.le
  have hscaleInv : 0 ≤ (T / 16)⁻¹ :=
    inv_nonneg.mpr (by positivity)
  unfold hughesYoungFarBoxMajorant hughesYoungFarBoxPolynomialEnvelope
  have hprefix :
      0 ≤ 15 * T / 4 * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
        (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          (T / 16)⁻¹ ^ j * L := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) hsmallInv)
              (Real.exp_pos 100).le)
            (by positivity))
          hheight.le)
        (pow_nonneg hscaleInv j))
      hL
  apply mul_le_mul_of_nonneg_left ?_ hprefix
  gcongr
  · simpa [pow_two] using
      hscalar.trans (mul_le_mul hcoeffh hcoeffk (norm_nonneg _) hA)

/-- A deliberately coarse but uniform polynomial estimate for the common
far-box envelope.  The exponent `43` records every mollifier, dyadic, and
contour factor before the arbitrary-order integration-by-parts decay is
used. -/
theorem hughesYoungFarBoxPolynomialEnvelope_le_power43
    {Cw : ℕ → ℝ} {D L : ℝ} {j : ℕ} {T ε A ell B : ℝ}
    (hT : Real.exp 1 ≤ T) (hε1 : ε ≤ 1)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hA0 : 0 ≤ A) (hell0 : 0 ≤ ell) (hB1 : 1 ≤ B)
    (hA : A ≤ 9 * T ^ (2 : ℝ))
    (hell : ell ≤ 9 * T ^ (2 : ℝ))
    (hB : B ≤ 649 * T ^ (7 : ℝ)) :
    hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε A ell B ≤
      ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant Cw j * L * D *
          649 ^ 4 * 9 ^ 2 * 18 ^ 4) *
        ((T / 16)⁻¹) ^ j * T ^ (43 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hc := hughesYoungSmallContour_spec hT
  have hheight : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hlog : (hughesYoungSmallContour T)⁻¹ ≤ T := by
    rw [hc.2.2]
    exact (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
  have hBpow : B ^ (1 + ε) ≤ (649 * T ^ (7 : ℝ)) ^ (2 : ℝ) := by
    calc
      B ^ (1 + ε) ≤ B ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
      _ ≤ (649 * T ^ (7 : ℝ)) ^ (2 : ℝ) := by
        exact Real.rpow_le_rpow (by positivity) hB (by norm_num)
  have hApow : A ^ 2 ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
  have hbase : 2 * ell ≤ 18 * T ^ (2 : ℝ) := by linarith
  have hbaseOne : 1 ≤ 18 * T ^ (2 : ℝ) := by
    have hpow : 1 ≤ T ^ (2 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
    nlinarith
  have hexponent :
      (1 / 2 : ℝ) + hughesYoungSmallContour T ≤ 2 := by
    linarith [hc.2.1]
  have hEllPow :
      (2 * ell) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) ≤
        (18 * T ^ (2 : ℝ)) ^ (2 : ℝ) := by
    calc
      (2 * ell) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) ≤
          (18 * T ^ (2 : ℝ)) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) := by
              exact Real.rpow_le_rpow (by positivity) hbase (by linarith [hc.1])
      _ ≤ (18 * T ^ (2 : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne hexponent
  unfold hughesYoungFarBoxPolynomialEnvelope
  calc
    _ ≤ (((15 * T / 4) * T * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) *
        (D * (649 * T ^ (7 : ℝ)) ^ (2 : ℝ) *
          (649 * T ^ (7 : ℝ)) ^ (2 : ℝ) *
          (9 * T ^ (2 : ℝ)) ^ 2 *
          (18 * T ^ (2 : ℝ)) ^ (2 : ℝ) *
          (18 * T ^ (2 : ℝ)) ^ (2 : ℝ)) := by gcongr
    _ = ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant Cw j * L * D *
          649 ^ 4 * 9 ^ 2 * 18 ^ 4) *
        ((T / 16)⁻¹) ^ j * T ^ (43 : ℝ) := by
      simp only [Real.rpow_ofNat]
      ring

/-- Every far majorant on an actual active dyadic box is controlled by one
height-dependent envelope.  This is the finite source-entry bridge used by
all four complementary-box cases. -/
theorem hughesYoungFarBoxMajorant_le_activeEnvelope
    {Cw : ℕ → ℝ} {D L : ℝ} {j : ℕ} {T ε : ℝ} {R K h k : ℕ}
    {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T) (hε : 0 ≤ ε)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungFarBoxMajorant Cw D L j T
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ε h k
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) ≤
      hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε
        (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
        (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
        (hughesYoungActiveArithmeticCutoff T R : ℝ) := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  have hhpos : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hhle : h ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hhmem).2
  have hkle : k ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hkmem).2
  have ha : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hhle
  have hb : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hkle
  have hMraw :=
    hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left hij
  have hNraw :=
    hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right hij
  have hprod :
      hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul ha hb)
  have hMnat : hughesYoungFullDyadicBound ij.1 ≤
      hughesYoungActiveArithmeticCutoff T R := by
    unfold hughesYoungActiveArithmeticCutoff
    simpa only [ell] using hMraw.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 4 hprod) 1)
  have hNnat : hughesYoungFullDyadicBound ij.2 ≤
      hughesYoungActiveArithmeticCutoff T R := by
    unfold hughesYoungActiveArithmeticCutoff
    simpa only [ell] using hNraw.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 4 hprod) 1)
  apply hughesYoungFarBoxMajorant_le_polynomialEnvelope
    hT hε hD hL hCw (by positivity) (by positivity) (by positivity)
    hhpos hkpos
  · exact_mod_cast hhle
  · exact_mod_cast hkle
  · exact_mod_cast hMnat
  · exact_mod_cast hNnat
  · exact one_half_le_hughesYoungFullDyadicScale ij.1
  · exact one_half_le_hughesYoungFullDyadicScale ij.2
  · exact (norm_shortMobiusSquareCoeff_le_divisors T hhpos).trans <| by
      exact_mod_cast (Nat.card_divisors_le_self h).trans hhle
  · exact (norm_shortMobiusSquareCoeff_le_divisors T hkpos).trans <| by
      exact_mod_cast (Nat.card_divisors_le_self k).trans hkle

/-- One box-independent majorant for the exhaustive non-large case split.
The small-box factor uses the proved source inequality `Y < 320P`; the
other factors are the exact cancellations of equation (65). -/
noncomputable def hughesYoungNonLargeCommonEnvelope
    (CwLeft CwRight CwSmall CwFar : ℕ → ℝ)
    (DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ)
    (j : ℕ) (T P ε : ℝ) (R : ℕ) : ℝ :=
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  let B : ℝ := (hughesYoungActiveArithmeticCutoff T R : ℝ)
  5 ^ j * hughesYoungFarBoxPolynomialEnvelope
      CwLeft DLeft LLeft j T ε ell ell B +
    5 ^ j * hughesYoungFarBoxPolynomialEnvelope
      CwRight DRight LRight j T ε ell ell B +
    (3200 * P) ^ j * hughesYoungFarBoxPolynomialEnvelope
      CwSmall DSmall LSmall j T ε ell ell B +
    (5 * T / P) ^ j * hughesYoungFarBoxPolynomialEnvelope
      CwFar DFar LFar j T ε ell ell B

theorem hughesYoungNonLargeBoxCaseMajorant_le_commonEnvelope
    {CwLeft CwRight CwSmall CwFar : ℕ → ℝ}
    {DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ}
    {j : ℕ} {T P ε : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T) (hP : 0 < P) (hε : 0 ≤ ε)
    (hDLeft : 0 ≤ DLeft) (hLLeft : 0 ≤ LLeft)
    (hDRight : 0 ≤ DRight) (hLRight : 0 ≤ LRight)
    (hDSmall : 0 ≤ DSmall) (hLSmall : 0 ≤ LSmall)
    (hDFar : 0 ≤ DFar) (hLFar : 0 ≤ LFar)
    (hCwLeft : ∀ i, 0 < CwLeft i) (hCwRight : ∀ i, 0 < CwRight i)
    (hCwSmall : ∀ i, 0 < CwSmall i) (hCwFar : ∀ i, 0 < CwFar i)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungActiveNonLargeDFIBoxes P
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungNonLargeBoxCaseMajorant
        CwLeft CwRight CwSmall CwFar
        DLeft LLeft DRight LRight DSmall LSmall DFar LFar
        j T P ε (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) h k ij ≤
      hughesYoungNonLargeCommonEnvelope
        CwLeft CwRight CwSmall CwFar
        DLeft LLeft DRight LRight DSmall LSmall DFar LFar
        j T P ε R := by
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  let B : ℝ := (hughesYoungActiveArithmeticCutoff T R : ℝ)
  let EL := hughesYoungFarBoxPolynomialEnvelope
      CwLeft DLeft LLeft j T ε ell ell B
  let ER := hughesYoungFarBoxPolynomialEnvelope
      CwRight DRight LRight j T ε ell ell B
  let ES := hughesYoungFarBoxPolynomialEnvelope
      CwSmall DSmall LSmall j T ε ell ell B
  let EF := hughesYoungFarBoxPolynomialEnvelope
      CwFar DFar LFar j T ε ell ell B
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc := hughesYoungSmallContour_spec hT
  have hactive := (Finset.mem_filter.mp hij).1
  have hEL : 0 ≤ EL := by
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1
      hDLeft hLLeft hCwLeft (by positivity) (by positivity)
  have hER : 0 ≤ ER := by
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1
      hDRight hLRight hCwRight (by positivity) (by positivity)
  have hES : 0 ≤ ES := by
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1
      hDSmall hLSmall hCwSmall (by positivity) (by positivity)
  have hEF : 0 ≤ EF := by
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1
      hDFar hLFar hCwFar (by positivity) (by positivity)
  have hcommon :
      0 ≤ 5 ^ j * EL + 5 ^ j * ER + (3200 * P) ^ j * ES +
        (5 * T / P) ^ j * EF := by positivity
  have hX : 0 < hughesYoungFullDyadicScale ij.1 :=
    hughesYoungFullDyadicScale_pos ij.1
  have hY : 0 < hughesYoungFullDyadicScale ij.2 :=
    hughesYoungFullDyadicScale_pos ij.2
  have hfarLeft := hughesYoungFarBoxMajorant_le_activeEnvelope
    (j := j) hT hε hDLeft hLLeft hCwLeft hhmem hkmem hactive
  have hfarRight := hughesYoungFarBoxMajorant_le_activeEnvelope
    (j := j) hT hε hDRight hLRight hCwRight hhmem hkmem hactive
  have hfarSmall := hughesYoungFarBoxMajorant_le_activeEnvelope
    (j := j) hT hε hDSmall hLSmall hCwSmall hhmem hkmem hactive
  have hfarFar := hughesYoungFarBoxMajorant_le_activeEnvelope
    (j := j) hT hε hDFar hLFar hCwFar hhmem hkmem hactive
  have hrawSmall : 0 ≤ hughesYoungFarBoxMajorant CwSmall DSmall LSmall j T
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) ε h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2) :=
    hughesYoungFarBoxMajorant_nonneg hT0 hc.1 hDSmall hLSmall
      hX hY hCwSmall
  have hrawFar : 0 ≤ hughesYoungFarBoxMajorant CwFar DFar LFar j T
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) ε h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2) :=
    hughesYoungFarBoxMajorant_nonneg hT0 hc.1 hDFar hLFar
      hX hY hCwFar
  unfold hughesYoungNonLargeBoxCaseMajorant
  dsimp only
  by_cases hi : ij.1 = 0
  · rw [if_pos hi]
    by_cases hj : ij.2 = 0
    · rw [if_pos hj]
      simpa only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
        using hcommon
    · rw [if_neg hj]
      rw [hughesYoungBoundaryBoxMajorant_eq_fivePow_mul
        hT0 hDLeft hLLeft hX hY hc.1 hCwLeft]
      dsimp only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
      have hmain :
          5 ^ j * hughesYoungFarBoxMajorant CwLeft DLeft LLeft j T
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) ε h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2) ≤ 5 ^ j * EL :=
        mul_le_mul_of_nonneg_left hfarLeft (by positivity)
      have h₂ : 0 ≤ 5 ^ j * ER := mul_nonneg (by positivity) hER
      have h₃ : 0 ≤ (3200 * P) ^ j * ES := mul_nonneg (by positivity) hES
      have h₄ : 0 ≤ (5 * T / P) ^ j * EF := mul_nonneg (by positivity) hEF
      exact hmain.trans <| (le_add_of_nonneg_right h₂).trans <|
        (le_add_of_nonneg_right h₃).trans (le_add_of_nonneg_right h₄)
  · rw [if_neg hi]
    by_cases hj : ij.2 = 0
    · rw [if_pos hj]
      rw [hughesYoungBoundaryBoxMajorant_eq_fivePow_mul
        hT0 hDRight hLRight hX hY hc.1 hCwRight]
      dsimp only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
      have hmain :
          5 ^ j * hughesYoungFarBoxMajorant CwRight DRight LRight j T
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) ε h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2) ≤ 5 ^ j * ER :=
        mul_le_mul_of_nonneg_left hfarRight (by positivity)
      have h₁ : 0 ≤ 5 ^ j * EL := mul_nonneg (by positivity) hEL
      have h₃ : 0 ≤ (3200 * P) ^ j * ES := mul_nonneg (by positivity) hES
      have h₄ : 0 ≤ (5 * T / P) ^ j * EF := mul_nonneg (by positivity) hEF
      calc
        _ ≤ 5 ^ j * ER := hmain
        _ ≤ 5 ^ j * EL + 5 ^ j * ER := le_add_of_nonneg_left h₁
        _ ≤ _ + (3200 * P) ^ j * ES := le_add_of_nonneg_right h₃
        _ ≤ _ := le_add_of_nonneg_right h₄
    · rw [if_neg hj]
      by_cases hsupp :
          ¬ (hughesYoungReducedLeft h k : ℝ) ≤
              2 * hughesYoungFullDyadicScale ij.1 ∨
            ¬ (hughesYoungReducedRight h k : ℝ) ≤
              2 * hughesYoungFullDyadicScale ij.2
      · rw [if_pos hsupp]
        simpa only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
          using hcommon
      · rw [if_neg hsupp]
        by_cases hcomp :
            hughesYoungFullDyadicScale ij.1 ≤
                4 * hughesYoungFullDyadicScale ij.2 ∧
              hughesYoungFullDyadicScale ij.2 ≤
                4 * hughesYoungFullDyadicScale ij.1
        · rw [if_pos hcomp]
          have ha := (not_or.mp hsupp).1
          have hb := (not_or.mp hsupp).2
          have hU : hughesYoungDFIOptimalU P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) < 64 := by
            apply lt_of_not_ge
            intro hUlarge
            exact (Finset.mem_filter.mp hij).2
              ⟨Nat.pos_of_ne_zero hi, Nat.pos_of_ne_zero hj,
                not_not.mp ha, not_not.mp hb, hUlarge, hcomp.1, hcomp.2⟩
          have hYsmall :=
            hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
              hP hX hY hcomp.2 hU
          rw [hughesYoungSmallBoxMajorant_eq_mul
            hT0 hY hDSmall hLSmall hX hc.1 hCwSmall]
          have hfactor :
              (10 * hughesYoungFullDyadicScale ij.2) ^ j ≤
                (3200 * P) ^ j :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) j
          dsimp only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
          have hmain :
              (10 * hughesYoungFullDyadicScale ij.2) ^ j *
                  hughesYoungFarBoxMajorant CwSmall DSmall LSmall j T
                    (hughesYoungFullDyadicScale ij.1)
                    (hughesYoungFullDyadicScale ij.2) ε h k
                    (hughesYoungFullDyadicBound ij.1)
                    (hughesYoungFullDyadicBound ij.2) ≤
                (3200 * P) ^ j * ES :=
            mul_le_mul hfactor hfarSmall hrawSmall (by positivity)
          have h₁ : 0 ≤ 5 ^ j * EL := mul_nonneg (by positivity) hEL
          have h₂ : 0 ≤ 5 ^ j * ER := mul_nonneg (by positivity) hER
          have h₄ : 0 ≤ (5 * T / P) ^ j * EF := mul_nonneg (by positivity) hEF
          calc
            _ ≤ (3200 * P) ^ j * ES := hmain
            _ ≤ 5 ^ j * EL + 5 ^ j * ER + (3200 * P) ^ j * ES :=
              le_add_of_nonneg_left (add_nonneg h₁ h₂)
            _ ≤ _ := le_add_of_nonneg_right h₄
        · rw [if_neg hcomp]
          rw [hughesYoungCancelledFarBoxMajorant_eq_mul
            hT0 hP hDFar hLFar hX hY hc.1 hCwFar]
          dsimp only [hughesYoungNonLargeCommonEnvelope, ell, B, EL, ER, ES, EF]
          have hmain :
              (5 * T / P) ^ j *
                  hughesYoungFarBoxMajorant CwFar DFar LFar j T
                    (hughesYoungFullDyadicScale ij.1)
                    (hughesYoungFullDyadicScale ij.2) ε h k
                    (hughesYoungFullDyadicBound ij.1)
                    (hughesYoungFullDyadicBound ij.2) ≤
                (5 * T / P) ^ j * EF :=
            mul_le_mul_of_nonneg_left hfarFar (by positivity)
          have h₁ : 0 ≤ 5 ^ j * EL := mul_nonneg (by positivity) hEL
          have h₂ : 0 ≤ 5 ^ j * ER := mul_nonneg (by positivity) hER
          have h₃ : 0 ≤ (3200 * P) ^ j * ES := mul_nonneg (by positivity) hES
          calc
            _ ≤ (5 * T / P) ^ j * EF := hmain
            _ ≤ _ := le_add_of_nonneg_left (add_nonneg (add_nonneg h₁ h₂) h₃)

theorem hughesYoungActiveNonLargeDFICaseMajorant_le_commonEnvelope
    {CwLeft CwRight CwSmall CwFar : ℕ → ℝ}
    {DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ}
    {j : ℕ} {T P ε : ℝ} {R K : ℕ}
    (hT : Real.exp 1 ≤ T) (hP : 0 < P) (hε : 0 ≤ ε)
    (hDLeft : 0 ≤ DLeft) (hLLeft : 0 ≤ LLeft)
    (hDRight : 0 ≤ DRight) (hLRight : 0 ≤ LRight)
    (hDSmall : 0 ≤ DSmall) (hLSmall : 0 ≤ LSmall)
    (hDFar : 0 ≤ DFar) (hLFar : 0 ≤ LFar)
    (hCwLeft : ∀ i, 0 < CwLeft i) (hCwRight : ∀ i, 0 < CwRight i)
    (hCwSmall : ∀ i, 0 < CwSmall i) (hCwFar : ∀ i, 0 < CwFar i) :
    hughesYoungActiveNonLargeDFICaseMajorant
        CwLeft CwRight CwSmall CwFar
        DLeft LLeft DRight LRight DSmall LSmall DFar LFar
        j T P ε R K ≤
      ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
        (((K + 2 : ℕ) : ℝ) ^ 2) *
        hughesYoungNonLargeCommonEnvelope
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε R := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let E := hughesYoungNonLargeCommonEnvelope
    CwLeft CwRight CwSmall CwFar
    DLeft LLeft DRight LRight DSmall LSmall DFar LFar
    j T P ε R
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc := hughesYoungSmallContour_spec hT
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  let B : ℝ := (hughesYoungActiveArithmeticCutoff T R : ℝ)
  have henv (Cw : ℕ → ℝ) (D L : ℝ)
      (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i) :
      0 ≤ hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε ell ell B := by
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1 hD hL hCw
      (by positivity) (by positivity)
  have hE : 0 ≤ E := by
    dsimp only [E, hughesYoungNonLargeCommonEnvelope, ell, B]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (mul_nonneg (by positivity) (henv CwLeft DLeft LLeft
            hDLeft hLLeft hCwLeft))
          (mul_nonneg (by positivity) (henv CwRight DRight LRight
            hDRight hLRight hCwRight)))
        (mul_nonneg (by positivity) (henv CwSmall DSmall LSmall
          hDSmall hLSmall hCwSmall)))
      (mul_nonneg (by positivity) (henv CwFar DFar LFar
        hDFar hLFar hCwFar))
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      hughesYoungNonLargeBoxCaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) h k ij ≤ E := by
    intro h hh k hk ij hij
    exact hughesYoungNonLargeBoxCaseMajorant_le_commonEnvelope
      hT hP hε hDLeft hLLeft hDRight hLRight hDSmall hLSmall
      hDFar hLFar hCwLeft hCwRight hCwSmall hCwFar hh hk hij
  unfold hughesYoungActiveNonLargeDFICaseMajorant
  change (∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          hughesYoungNonLargeBoxCaseMajorant
            CwLeft CwRight CwSmall CwFar
            DLeft LLeft DRight LRight DSmall LSmall DFar LFar
            j T P ε (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) h k ij) ≤ _
  calc
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S, (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      calc
        (∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            hughesYoungNonLargeBoxCaseMajorant
              CwLeft CwRight CwSmall CwFar
              DLeft LLeft DRight LRight DSmall LSmall DFar LFar
              j T P ε (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) h k ij) ≤
            ∑ _ij ∈ hughesYoungActiveNonLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
              E := Finset.sum_le_sum (hbox h hh k hk)
        _ = ((hughesYoungActiveNonLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) * E := by
          simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungActiveNonLargeDFIBoxes P
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

/-- After choosing a sufficiently high integration-by-parts order, every
common complementary-box envelope has a fixed negative power of the
height.  The three displayed base inequalities are discharged eventually
for the native smoothing scale below. -/
theorem hughesYoungNonLargeCommonEnvelope_le_rpow_neg_seven
    {CwLeft CwRight CwSmall CwFar : ℕ → ℝ}
    {DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ}
    {T P ε : ℝ}
    (hT : Real.exp 1 ≤ T) (hP : 0 < P) (hε1 : ε ≤ 1)
    (hDLeft : 0 ≤ DLeft) (hLLeft : 0 ≤ LLeft)
    (hDRight : 0 ≤ DRight) (hLRight : 0 ≤ LRight)
    (hDSmall : 0 ≤ DSmall) (hLSmall : 0 ≤ LSmall)
    (hDFar : 0 ≤ DFar) (hLFar : 0 ≤ LFar)
    (hCwLeft : ∀ i, 0 < CwLeft i) (hCwRight : ∀ i, 0 < CwRight i)
    (hCwSmall : ∀ i, 0 < CwSmall i) (hCwFar : ∀ i, 0 < CwFar i)
    (hEndpoint : 80 / T ≤ T ^ (-1 / 40000 : ℝ))
    (hSmall : 51200 * P / T ≤ T ^ (-1 / 40000 : ℝ))
    (hFar : 80 / P ≤ T ^ (-1 / 40000 : ℝ)) :
    hughesYoungNonLargeCommonEnvelope
        CwLeft CwRight CwSmall CwFar
        DLeft LLeft DRight LRight DSmall LSmall DFar LFar
        2000000 T P ε (hughesYoungConductorRadius T) ≤
      (((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwLeft 2000000 *
          LLeft * DLeft * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwRight 2000000 *
          LRight * DRight * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwSmall 2000000 *
          LSmall * DSmall * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwFar 2000000 *
          LFar * DFar * 649 ^ 4 * 9 ^ 2 * 18 ^ 4)) *
        T ^ (-7 : ℝ) := by
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  let B : ℝ := (hughesYoungActiveArithmeticCutoff T
    (hughesYoungConductorRadius T) : ℝ)
  let CL : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant CwLeft 2000000 *
    LLeft * DLeft * 649 ^ 4 * 9 ^ 2 * 18 ^ 4
  let CR : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant CwRight 2000000 *
    LRight * DRight * 649 ^ 4 * 9 ^ 2 * 18 ^ 4
  let CS : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant CwSmall 2000000 *
    LSmall * DSmall * 649 ^ 4 * 9 ^ 2 * 18 ^ 4
  let CF : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant CwFar 2000000 *
    LFar * DFar * 649 ^ 4 * 9 ^ 2 * 18 ^ 4
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hellTight := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hpowTwo : T ^ (1 / 50 : ℝ) ≤ T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hell : ell ≤ 9 * T ^ (2 : ℝ) := by
    dsimp only [ell]
    exact hellTight.trans (mul_le_mul_of_nonneg_left hpowTwo (by norm_num))
  have hB : B ≤ 649 * T ^ (7 : ℝ) := by
    simpa only [B] using hughesYoungConductorArithmeticCutoff_le hT
  have hB1 : 1 ≤ B := by
    have hnat : 1 ≤ hughesYoungActiveArithmeticCutoff T
        (hughesYoungConductorRadius T) := by
      unfold hughesYoungActiveArithmeticCutoff
      omega
    dsimp only [B]
    exact_mod_cast hnat
  have hConst (H L D : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hD : 0 ≤ D) :
      0 ≤ (15 / 4) * Real.exp 100 * 6 * H * L * D *
        649 ^ 4 * 9 ^ 2 * 18 ^ 4 := by positivity
  have hCL : 0 ≤ CL := by
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCwLeft 2000000).le
      hLLeft hDLeft
  have hCR : 0 ≤ CR := by
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCwRight 2000000).le
      hLRight hDRight
  have hCS : 0 ≤ CS := by
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCwSmall 2000000).le
      hLSmall hDSmall
  have hCF : 0 ≤ CF := by
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCwFar 2000000).le
      hLFar hDFar
  have hEL := hughesYoungFarBoxPolynomialEnvelope_le_power43
    (j := 2000000) hT hε1 hDLeft hLLeft hCwLeft
      (by positivity : 0 ≤ ell) (by positivity : 0 ≤ ell) hB1 hell hell hB
  have hER := hughesYoungFarBoxPolynomialEnvelope_le_power43
    (j := 2000000) hT hε1 hDRight hLRight hCwRight
      (by positivity : 0 ≤ ell) (by positivity : 0 ≤ ell) hB1 hell hell hB
  have hES := hughesYoungFarBoxPolynomialEnvelope_le_power43
    (j := 2000000) hT hε1 hDSmall hLSmall hCwSmall
      (by positivity : 0 ≤ ell) (by positivity : 0 ≤ ell) hB1 hell hell hB
  have hEF := hughesYoungFarBoxPolynomialEnvelope_le_power43
    (j := 2000000) hT hε1 hDFar hLFar hCwFar
      (by positivity : 0 ≤ ell) (by positivity : 0 ≤ ell) hB1 hell hell hB
  have hpow (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ T ^ (-1 / 40000 : ℝ)) :
      q ^ (2000000 : ℕ) ≤ T ^ (-50 : ℝ) := by
    calc
      q ^ (2000000 : ℕ) ≤ (T ^ (-1 / 40000 : ℝ)) ^ (2000000 : ℕ) :=
        pow_le_pow_left₀ hq0 hq 2000000
      _ = T ^ (-50 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num
  have hEndpointPow := hpow (80 / T) (by positivity) hEndpoint
  have hSmallPow := hpow (51200 * P / T) (by positivity) hSmall
  have hFarPow := hpow (80 / P) (by positivity) hFar
  have hcombine (C q : ℝ) (hC : 0 ≤ C)
      (hq : q ^ (2000000 : ℕ) ≤ T ^ (-50 : ℝ)) :
      C * q ^ (2000000 : ℕ) * T ^ (43 : ℝ) ≤ C * T ^ (-7 : ℝ) := by
    calc
      C * q ^ (2000000 : ℕ) * T ^ (43 : ℝ) ≤
          C * T ^ (-50 : ℝ) * T ^ (43 : ℝ) := by gcongr
      _ = C * (T ^ (-50 : ℝ) * T ^ (43 : ℝ)) := by ac_rfl
      _ = C * T ^ (-7 : ℝ) := by
        rw [← Real.rpow_add hT0]
        norm_num
  have hLeft :
      5 ^ (2000000 : ℕ) *
          hughesYoungFarBoxPolynomialEnvelope CwLeft DLeft LLeft 2000000
            T ε ell ell B ≤ CL * T ^ (-7 : ℝ) := by
    calc
      _ ≤ 5 ^ (2000000 : ℕ) *
          (CL * ((T / 16)⁻¹) ^ (2000000 : ℕ) * T ^ (43 : ℝ)) := by gcongr
      _ = CL * (5 ^ (2000000 : ℕ) *
          ((T / 16)⁻¹) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by ac_rfl
      _ = CL * ((80 / T) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by
        rw [fivePow_mul_hughesYoungDecay_eq hT0]
      _ ≤ CL * T ^ (-7 : ℝ) := hcombine CL (80 / T) hCL hEndpointPow
  have hRight :
      5 ^ (2000000 : ℕ) *
          hughesYoungFarBoxPolynomialEnvelope CwRight DRight LRight 2000000
            T ε ell ell B ≤ CR * T ^ (-7 : ℝ) := by
    calc
      _ ≤ 5 ^ (2000000 : ℕ) *
          (CR * ((T / 16)⁻¹) ^ (2000000 : ℕ) * T ^ (43 : ℝ)) := by gcongr
      _ = CR * (5 ^ (2000000 : ℕ) *
          ((T / 16)⁻¹) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by ac_rfl
      _ = CR * ((80 / T) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by
        rw [fivePow_mul_hughesYoungDecay_eq hT0]
      _ ≤ CR * T ^ (-7 : ℝ) := hcombine CR (80 / T) hCR hEndpointPow
  have hSmallTerm :
      (3200 * P) ^ (2000000 : ℕ) *
          hughesYoungFarBoxPolynomialEnvelope CwSmall DSmall LSmall 2000000
            T ε ell ell B ≤ CS * T ^ (-7 : ℝ) := by
    calc
      _ ≤ (3200 * P) ^ (2000000 : ℕ) *
          (CS * ((T / 16)⁻¹) ^ (2000000 : ℕ) * T ^ (43 : ℝ)) := by gcongr
      _ = CS * ((3200 * P) ^ (2000000 : ℕ) *
          ((T / 16)⁻¹) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by ac_rfl
      _ = CS * ((51200 * P / T) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by
        rw [commonSmall_mul_hughesYoungDecay_eq hT0 hP]
      _ ≤ CS * T ^ (-7 : ℝ) :=
        hcombine CS (51200 * P / T) hCS hSmallPow
  have hFarTerm :
      (5 * T / P) ^ (2000000 : ℕ) *
          hughesYoungFarBoxPolynomialEnvelope CwFar DFar LFar 2000000
            T ε ell ell B ≤ CF * T ^ (-7 : ℝ) := by
    calc
      _ ≤ (5 * T / P) ^ (2000000 : ℕ) *
          (CF * ((T / 16)⁻¹) ^ (2000000 : ℕ) * T ^ (43 : ℝ)) := by gcongr
      _ = CF * ((5 * T / P) ^ (2000000 : ℕ) *
          ((T / 16)⁻¹) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by ac_rfl
      _ = CF * ((80 / P) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by
        rw [cancelledFar_mul_hughesYoungDecay_eq hT0 hP]
      _ ≤ CF * T ^ (-7 : ℝ) := hcombine CF (80 / P) hCF hFarPow
  dsimp only [hughesYoungNonLargeCommonEnvelope, ell, B]
  calc
    _ ≤ CL * T ^ (-7 : ℝ) + CR * T ^ (-7 : ℝ) +
        CS * T ^ (-7 : ℝ) + CF * T ^ (-7 : ℝ) := by gcongr
    _ = (CL + CR + CS + CF) * T ^ (-7 : ℝ) := by ring
    _ = _ := by rfl

/-- The native smoothing scale eventually satisfies all three decay bases
used in the exhaustive non-large-box estimate.  The exponents are kept
explicit: the endpoint, small-box, and complementary-box gaps are
respectively `39999/40000`, `39995/40000`, and `3/40000`. -/
theorem eventually_hughesYoungNativeNonLargeDecayBases :
    ∀ᶠ T : ℝ in atTop,
      Real.exp 1 ≤ T ∧
      80 / T ≤ T ^ (-1 / 40000 : ℝ) ∧
      51200 * hughesYoungDFISmoothingScale T / T ≤
        T ^ (-1 / 40000 : ℝ) ∧
      80 / hughesYoungDFISmoothingScale T ≤
        T ^ (-1 / 40000 : ℝ) := by
  have hEndpointGrow : Tendsto
      (fun T : ℝ => T ^ (39999 / 40000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hSmallGrow : Tendsto
      (fun T : ℝ => T ^ (39995 / 40000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hFarGrow : Tendsto
      (fun T : ℝ => T ^ (3 / 40000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
      hEndpointGrow.eventually (eventually_ge_atTop 80),
      hSmallGrow.eventually (eventually_ge_atTop 409600),
      hFarGrow.eventually (eventually_ge_atTop 10)] with
      T hT hEndpoint hSmall hFar
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hEndpointProduct :
      T ^ (-1 / 40000 : ℝ) * T = T ^ (39999 / 40000 : ℝ) := by
    calc
      T ^ (-1 / 40000 : ℝ) * T =
          T ^ (-1 / 40000 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((-1 / 40000 : ℝ) + 1) :=
        (Real.rpow_add hT0 _ _).symm
      _ = T ^ (39999 / 40000 : ℝ) := by norm_num
  have hEndpointBase : 80 / T ≤ T ^ (-1 / 40000 : ℝ) := by
    rw [div_le_iff₀ hT0]
    rw [hEndpointProduct]
    exact hEndpoint
  have hSmallProduct :
      T ^ (39995 / 40000 : ℝ) * T ^ (1 / 10000 : ℝ) =
        T ^ (39999 / 40000 : ℝ) := by
    rw [← Real.rpow_add hT0]
    congr 1
    norm_num
  have hSmallRight :
      409600 * T ^ (1 / 10000 : ℝ) ≤
        T ^ (39999 / 40000 : ℝ) := by
    calc
      _ ≤ T ^ (39995 / 40000 : ℝ) * T ^ (1 / 10000 : ℝ) := by
        gcongr
      _ = _ := hSmallProduct
  have hSmallBase :
      51200 * hughesYoungDFISmoothingScale T / T ≤
        T ^ (-1 / 40000 : ℝ) := by
    rw [div_le_iff₀ hT0, hEndpointProduct]
    unfold hughesYoungDFISmoothingScale
    convert hSmallRight using 1
    ring
  have hNativeP : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  have hFarProduct :
      T ^ (-1 / 40000 : ℝ) * hughesYoungDFISmoothingScale T =
        8 * T ^ (3 / 40000 : ℝ) := by
    unfold hughesYoungDFISmoothingScale
    calc
      T ^ (-1 / 40000 : ℝ) * (8 * T ^ (1 / 10000 : ℝ)) =
          8 * (T ^ (-1 / 40000 : ℝ) * T ^ (1 / 10000 : ℝ)) := by ring
      _ = 8 * T ^ (3 / 40000 : ℝ) := by
        rw [← Real.rpow_add hT0]
        congr 1
        norm_num
  have hFarBase :
      80 / hughesYoungDFISmoothingScale T ≤
        T ^ (-1 / 40000 : ℝ) := by
    rw [div_le_iff₀ hNativeP, hFarProduct]
    nlinarith
  exact ⟨hT, hEndpointBase, hSmallBase, hFarBase⟩

theorem eventually_four_mul_hughesYoungSmallContour_le_one
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp 1 ≤ T ∧ 4 * C * hughesYoungSmallContour T ≤ 1 := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (4 * C))
  filter_upwards [eventually_ge_atTop (Real.exp 1), hlog] with T hT hlogT
  have hlogPos : 0 < Real.log T := by
    have hlogOne : 1 ≤ Real.log T := by
      simpa using Real.log_le_log (Real.exp_pos 1) hT
    linarith
  refine ⟨hT, ?_⟩
  unfold hughesYoungSmallContour
  change (4 * C) / Real.log T ≤ 1
  exact (div_le_one hlogPos).2 hlogT

theorem eventually_hughesYoungDFISmoothingScale_native_range :
    ∀ᶠ T : ℝ in atTop,
      Real.exp 1 ≤ T ∧
      1 ≤ hughesYoungDFISmoothingScale T ∧
      hughesYoungDFISmoothingScale T ≤ T := by
  have hGrow : Tendsto
      (fun T : ℝ => T ^ (9999 / 10000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
      hGrow.eventually (eventually_ge_atTop 8)] with T hT hEight
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hPowSmall : 1 ≤ T ^ (1 / 10000 : ℝ) :=
    Real.one_le_rpow hT1 (by norm_num)
  have hFactor :
      T ^ (1 / 10000 : ℝ) * T ^ (9999 / 10000 : ℝ) = T := by
    calc
      _ = T ^ ((1 / 10000 : ℝ) + 9999 / 10000) :=
        (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 : ℝ) := by norm_num
      _ = T := Real.rpow_one T
  refine ⟨hT, ?_, ?_⟩
  · unfold hughesYoungDFISmoothingScale
    nlinarith
  · unfold hughesYoungDFISmoothingScale
    calc
      8 * T ^ (1 / 10000 : ℝ) ≤
          T ^ (9999 / 10000 : ℝ) * T ^ (1 / 10000 : ℝ) := by
        gcongr
      _ = T := by rw [mul_comm, hFactor]

/-- Equation (65), summed over the literal large-DFI family.  The decay
factor remains on the left until after all three finite sums have been
estimated, so the theorem consumes the actual global far-off-diagonal
object rather than a separately supplied family. -/
theorem exists_scaled_norm_hughesYoungActiveLargeDFIFarOffDiagonal_le
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungActiveLargeDFIFarOffDiagonal T P R K‖ ≤
        (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) *
        hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T R : ℝ) := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T P R K hT hT16 hP hPT hsmall
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (P / (5 * T)) ^ j
  let E : ℝ := hughesYoungFarBoxPolynomialEnvelope Cw D L j T ε
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T R : ℝ)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc := hughesYoungSmallContour_spec hT
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1 hD.le hL.le hCw
      (by positivity) (by positivity)
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      A * ‖hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)‖ ≤ E := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h :=
      Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k :=
      Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hlarge := (Finset.mem_filter.mp hij).2
    have hactive := (Finset.mem_filter.mp hij).1
    have hi : 0 < ij.1 := hlarge.1
    have hj : 0 < ij.2 := hlarge.2.1
    have hX : 0 < hughesYoungFullDyadicScale ij.1 :=
      hughesYoungFullDyadicScale_pos ij.1
    have hY : 0 < hughesYoungFullDyadicScale ij.2 :=
      hughesYoungFullDyadicScale_pos ij.2
    have ha : 0 < hughesYoungReducedLeft h k :=
      hughesYoungReducedLeft_pos hh
    have hb : 0 < hughesYoungReducedRight h k :=
      hughesYoungReducedRight_pos hh hk
    have hlocal := hfar
      (T := T) (c := hughesYoungSmallContour T) (H := T / 8) (P := P)
      (X := hughesYoungFullDyadicScale ij.1)
      (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
      (a := hughesYoungReducedLeft h k) (b := hughesYoungReducedRight h k)
      (M := hughesYoungFullDyadicBound ij.1)
      (N := hughesYoungFullDyadicBound ij.2)
      hT16 hc.1 hc.2.1 hsmall (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT hX hY hh hk ha hb
    have hmajor := hughesYoungFarBoxMajorant_le_activeEnvelope
      (j := j) hT hε.le hD.le hL.le hCw hhmem hkmem hactive
    have hlocal' :
        A * ‖hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)‖ ≤
        hughesYoungFarBoxMajorant Cw D L j T
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) ε h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2) := by
      simpa only [A, hughesYoungFarOffDiagonalBox,
        hughesYoungFarBoxMajorant] using hlocal
    exact hlocal'.trans hmajor
  unfold hughesYoungActiveLargeDFIFarOffDiagonal
  change A * ‖∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
            (T / 8) P (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)‖ ≤ _
  calc
    _ ≤ A * ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
            (T / 8) P (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)‖ := by
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
            norm_sum_le _ _))) hA
    _ = ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          A * ‖hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
            (T / 8) P (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)‖ := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S,
        (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      calc
        _ ≤ ∑ _ij ∈ hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            E := Finset.sum_le_sum (hbox h hhmem k hkmem)
        _ = ((hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) * E := by
          simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungActiveLargeDFIBoxes P
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

set_option maxRecDepth 10000

/-- At the native smoothing scale, cancelling the left-hand equation-(65)
factor leaves a fixed negative seventh power.  This is the large-box
counterpart of the complementary-box envelope estimate. -/
theorem hughesYoungNativeLargeFarEnvelope_le_rpow_neg_seven
    {Cw : ℕ → ℝ} {D L ε T : ℝ}
    (hT : Real.exp 1 ≤ T) (hε1 : ε ≤ 1)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hFar : 80 / hughesYoungDFISmoothingScale T ≤
      T ^ (-1 / 40000 : ℝ)) :
    (5 * T / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ) *
        hughesYoungFarBoxPolynomialEnvelope Cw D L 2000000 T ε
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T
            (hughesYoungConductorRadius T) : ℝ) ≤
      ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant Cw 2000000 * L * D *
          649 ^ 4 * 9 ^ 2 * 18 ^ 4) * T ^ (-7 : ℝ) := by
  let ell : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ)
  let B : ℝ := (hughesYoungActiveArithmeticCutoff T
    (hughesYoungConductorRadius T) : ℝ)
  let C : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 2000000 * L * D *
    649 ^ 4 * 9 ^ 2 * 18 ^ 4
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  have hellTight := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hpowTwo : T ^ (1 / 50 : ℝ) ≤ T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hell : ell ≤ 9 * T ^ (2 : ℝ) := by
    dsimp only [ell]
    exact hellTight.trans (mul_le_mul_of_nonneg_left hpowTwo (by norm_num))
  have hB : B ≤ 649 * T ^ (7 : ℝ) := by
    simpa only [B] using hughesYoungConductorArithmeticCutoff_le hT
  have hB1 : 1 ≤ B := by
    have hnat : 1 ≤ hughesYoungActiveArithmeticCutoff T
        (hughesYoungConductorRadius T) := by
      unfold hughesYoungActiveArithmeticCutoff
      omega
    dsimp only [B]
    exact_mod_cast hnat
  have hConst (H L D : ℝ) (hH : 0 ≤ H) (hL' : 0 ≤ L) (hD' : 0 ≤ D) :
      0 ≤ (15 / 4) * Real.exp 100 * 6 * H * L * D *
        649 ^ 4 * 9 ^ 2 * 18 ^ 4 := by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCw 2000000).le hL hD
  have henv := hughesYoungFarBoxPolynomialEnvelope_le_power43
    (j := 2000000) hT hε1 hD hL hCw
      (by positivity : 0 ≤ ell) (by positivity : 0 ≤ ell) hB1 hell hell hB
  have hFarPow :
      (80 / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ) ≤
        T ^ (-50 : ℝ) := by
    calc
      _ ≤ (T ^ (-1 / 40000 : ℝ)) ^ (2000000 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hFar 2000000
      _ = T ^ (-50 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num
  calc
    _ ≤ (5 * T / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ) *
        (C * ((T / 16)⁻¹) ^ (2000000 : ℕ) * T ^ (43 : ℝ)) := by
          gcongr
    _ = C * ((5 * T / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ) *
        ((T / 16)⁻¹) ^ (2000000 : ℕ)) * T ^ (43 : ℝ) := by ac_rfl
    _ = C * ((80 / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ)) *
        T ^ (43 : ℝ) := by
          rw [cancelledFar_mul_hughesYoungDecay_eq hT0 hP0]
    _ ≤ C * T ^ (-50 : ℝ) * T ^ (43 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFarPow hC) (Real.rpow_nonneg hT0.le _)
    _ = C * T ^ (-7 : ℝ) := by
      rw [show C * T ^ (-50 : ℝ) * T ^ (43 : ℝ) =
          C * (T ^ (-50 : ℝ) * T ^ (43 : ℝ)) by ring,
        ← Real.rpow_add hT0]
      norm_num
    _ = _ := by rfl

/-- The literal large-box equation-(65) remainder at the conductor radius
has the native Hughes--Young size. -/
theorem hughesYoungConductorActiveLargeDFIFarOffDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveLargeDFIFarOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let η : ℝ := min ε 1
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min hε (by norm_num)
  have hη1 : η ≤ 1 := by
    dsimp only [η]
    exact min_le_right _ _
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hscaled⟩ :=
    exists_scaled_norm_hughesYoungActiveLargeDFIFarOffDiagonal_le
      η hη 2000000
  let C : ℝ := (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 2000000 * L * D *
    649 ^ 4 * 9 ^ 2 * 18 ^ 4
  let A : ℝ := 81 * 103 ^ 2 * C
  have hConst (H L D : ℝ) (hH : 0 ≤ H) (hL' : 0 ≤ L) (hD' : 0 ≤ D) :
      0 ≤ (15 / 4) * Real.exp 100 * 6 * H * L * D *
        649 ^ 4 * 9 ^ 2 * 18 ^ 4 := by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact hConst _ _ _
      (hughesYoungHeightInputDerivativeConstant_pos hCw 2000000).le hL.le hD.le
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (by norm_num) hC
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγ,
      eventually_ge_atTop (16 : ℝ)] with T hBases hRange hContour hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  let Q : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 *
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2
  let E : ℝ := hughesYoungFarBoxPolynomialEnvelope Cw D L 2000000 T η
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ)
  let B : ℝ := (hughesYoungDFISmoothingScale T / (5 * T)) ^ (2000000 : ℕ)
  let F : ℝ := (5 * T / hughesYoungDFISmoothingScale T) ^ (2000000 : ℕ)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBF : B * F = 1 := by
    dsimp only [B, F]
    rw [← mul_pow]
    have hbase : hughesYoungDFISmoothingScale T / (5 * T) *
        (5 * T / hughesYoungDFISmoothingScale T) = 1 := by
      field_simp
    rw [hbase, one_pow]
  have hRaw := hscaled
    (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2 hContour.2
  have hUnscaled :
      ‖hughesYoungActiveLargeDFIFarOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ Q * (F * E) := by
    have hMultiplied : B * ‖hughesYoungActiveLargeDFIFarOffDiagonal T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ B * (Q * (F * E)) := by
      calc
      B * ‖hughesYoungActiveLargeDFIFarOffDiagonal T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ Q * E := by
            simpa only [B, Q, E] using hRaw
      _ = B * (Q * (F * E)) := by
        calc
          Q * E = (B * F) * (Q * E) := by rw [hBF, one_mul]
          _ = B * (Q * (F * E)) := by ac_rfl
    exact le_of_mul_le_mul_left hMultiplied hB
  have hEnvelope : F * E ≤ C * T ^ (-7 : ℝ) := by
    simpa only [F, E, C] using
      hughesYoungNativeLargeFarEnvelope_le_rpow_neg_seven
        hT hη1 hD.le hL.le hCw hBases.2.2.2
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤
      9 * T ^ (2 : ℝ) :=
    hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hCutSq : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) ≤
      81 * T ^ (4 : ℝ) := by
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (2 : ℝ)) ^ 2 = T ^ (4 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num]
        norm_num
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
        103 * T ^ (1 : ℝ) := by
      norm_num at hDepth ⊢
      exact hDepth
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by
        rw [Real.rpow_one, Real.rpow_two]
        ring
  have hQ : Q ≤ 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
    dsimp only [Q]
    calc
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) := by gcongr
      _ = 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
        rw [show T ^ (6 : ℝ) = T ^ (4 : ℝ) * T ^ (2 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0
      (hughesYoungSmallContour_spec hT).1 hD.le hL.le hCw
      (by positivity) (by positivity)
  have hFE : 0 ≤ F * E := mul_nonneg (by dsimp only [F]; positivity) hE
  have hBound :
      ‖hughesYoungActiveLargeDFIFarOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-1 : ℝ) := by
    calc
      _ ≤ Q * (F * E) := hUnscaled
      _ ≤ (81 * 103 ^ 2 * T ^ (6 : ℝ)) * (C * T ^ (-7 : ℝ)) := by
        exact mul_le_mul hQ hEnvelope hFE (by positivity)
      _ = A * T ^ (-1 : ℝ) := by
        dsimp only [A]
        rw [show T ^ (-1 : ℝ) = T ^ (6 : ℝ) * T ^ (-7 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hPow : T ^ (-1 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveLargeDFIFarOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-- The complete literal non-large DFI family at the native smoothing
scale is negligible.  This theorem consumes the exhaustive case split,
the four analytic box estimates, and the actual conductor-scale dyadic
family; it is not a bound for a separately supplied proxy. -/
theorem hughesYoungConductorActiveNonLargeDFIOffDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveNonLargeDFIOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let η : ℝ := min ε 1
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min hε (by norm_num)
  have hη1 : η ≤ 1 := by
    dsimp only [η]
    exact min_le_right _ _
  obtain ⟨CγLeft, DLeft, LLeft, CγRight, DRight, LRight,
      CγSmall, DSmall, LSmall, CγFar, DFar, LFar,
      hCγLeft, hDLeft, hLLeft, hCγRight, hDRight, hLRight,
      hCγSmall, hDSmall, hLSmall, hCγFar, hDFar, hLFar,
      CwLeft, CwRight, CwSmall, CwFar,
      hCwLeft, hCwRight, hCwSmall, hCwFar, hNonLarge⟩ :=
    exists_norm_hughesYoungActiveNonLargeDFIOffDiagonal_le_caseMajorant
      η hη 2000000
  let Csum : ℝ :=
      ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwLeft 2000000 *
          LLeft * DLeft * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwRight 2000000 *
          LRight * DRight * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwSmall 2000000 *
          LSmall * DSmall * 649 ^ 4 * 9 ^ 2 * 18 ^ 4) +
        ((15 / 4) * Real.exp 100 * 6 *
          hughesYoungHeightInputDerivativeConstant CwFar 2000000 *
          LFar * DFar * 649 ^ 4 * 9 ^ 2 * 18 ^ 4)
  let A : ℝ := 81 * 103 ^ 2 * Csum
  have hCsum : 0 ≤ Csum := by
    dsimp only [Csum]
    have hTerm (H L D : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hD : 0 ≤ D) :
        0 ≤ (15 / 4) * Real.exp 100 * 6 * H * L * D *
          649 ^ 4 * 9 ^ 2 * 18 ^ 4 := by positivity
    have hTL := hTerm _ _ _ (hughesYoungHeightInputDerivativeConstant_pos
      hCwLeft 2000000).le hLLeft.le hDLeft.le
    have hTR := hTerm _ _ _ (hughesYoungHeightInputDerivativeConstant_pos
      hCwRight 2000000).le hLRight.le hDRight.le
    have hTS := hTerm _ _ _ (hughesYoungHeightInputDerivativeConstant_pos
      hCwSmall 2000000).le hLSmall.le hDSmall.le
    have hTF := hTerm _ _ _ (hughesYoungHeightInputDerivativeConstant_pos
      hCwFar 2000000).le hLFar.le hDFar.le
    exact add_nonneg (add_nonneg (add_nonneg hTL hTR) hTS) hTF
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (by norm_num) hCsum
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγLeft,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγRight,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγSmall,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγFar,
      eventually_ge_atTop (16 : ℝ)] with
      T hBases hRange hContLeft hContRight hContSmall hContFar hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  have hRaw := hNonLarge
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2
    hContLeft.2 hContRight.2 hContSmall.2 hContFar.2
  have hSum := hughesYoungActiveNonLargeDFICaseMajorant_le_commonEnvelope
    (j := 2000000)
    (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hP0 hη.le hDLeft.le hLLeft.le hDRight.le hLRight.le
      hDSmall.le hLSmall.le hDFar.le hLFar.le
      hCwLeft hCwRight hCwSmall hCwFar
  have hEnvelope := hughesYoungNonLargeCommonEnvelope_le_rpow_neg_seven
    (T := T) (P := hughesYoungDFISmoothingScale T) (ε := η)
    hT hP0 hη1 hDLeft.le hLLeft.le hDRight.le hLRight.le
      hDSmall.le hLSmall.le hDFar.le hLFar.le
      hCwLeft hCwRight hCwSmall hCwFar
      hBases.2.1 hBases.2.2.1 hBases.2.2.2
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤
      9 * T ^ (2 : ℝ) := by
    exact hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
      103 * T ^ (1 : ℝ) := by
    norm_num at hDepth ⊢
    exact hDepth
  have hDepthLoose : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by
        rw [Real.rpow_one, Real.rpow_two]
        ring
  have hCutSq : (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2)) ≤
      81 * T ^ (4 : ℝ) := by
    have hPowerSq : (T ^ (2 : ℝ)) ^ (2 : ℕ) = T ^ (4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      norm_num
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow, hPowerSq]
        norm_num
  have hEnv0 : 0 ≤ hughesYoungNonLargeCommonEnvelope
      CwLeft CwRight CwSmall CwFar
      DLeft LLeft DRight LRight DSmall LSmall DFar LFar
      2000000 T (hughesYoungDFISmoothingScale T) η
        (hughesYoungConductorRadius T) := by
    have hc := hughesYoungSmallContour_spec hT
    have hPoly (Cw : ℕ → ℝ) (D L : ℝ)
        (hCw : ∀ i, 0 < Cw i) (hD : 0 ≤ D) (hL : 0 ≤ L) :
        0 ≤ hughesYoungFarBoxPolynomialEnvelope Cw D L 2000000 T η
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T
            (hughesYoungConductorRadius T) : ℝ) := by
      exact hughesYoungFarBoxPolynomialEnvelope_nonneg hT0 hc.1 hD hL hCw
        (by positivity) (by positivity)
    unfold hughesYoungNonLargeCommonEnvelope
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (mul_nonneg (by positivity) (hPoly _ _ _ hCwLeft hDLeft.le hLLeft.le))
          (mul_nonneg (by positivity) (hPoly _ _ _ hCwRight hDRight.le hLRight.le)))
        (mul_nonneg (by positivity) (hPoly _ _ _ hCwSmall hDSmall.le hLSmall.le)))
      (mul_nonneg (by positivity) (hPoly _ _ _ hCwFar hDFar.le hLFar.le))
  have hBound :
      ‖hughesYoungActiveNonLargeDFIOffDiagonal T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-1 : ℝ) := by
    calc
      _ ≤ hughesYoungActiveNonLargeDFICaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          2000000 T (hughesYoungDFISmoothingScale T) η
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) := hRaw
      _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          hughesYoungNonLargeCommonEnvelope
            CwLeft CwRight CwSmall CwFar
            DLeft LLeft DRight LRight DSmall LSmall DFar LFar
            2000000 T (hughesYoungDFISmoothingScale T) η
              (hughesYoungConductorRadius T)) := hSum
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) *
          (Csum * T ^ (-7 : ℝ)) := by
            gcongr
      _ = A * T ^ (-1 : ℝ) := by
        dsimp only [A]
        have hPower : T ^ (4 : ℝ) * T ^ (2 : ℝ) * T ^ (-7 : ℝ) =
            T ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
          norm_num
        rw [← hPower]
        ring
  have hPow : T ^ (-1 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveNonLargeDFIOffDiagonal T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-! ## The signed-central equation-(65) tail -/

/-- The single universal convergent series used to make the modulus-profile
constant uniform in every dyadic and mollifier parameter. -/
noncomputable def hughesYoungCentralTailSeriesConstant : ℝ :=
  ∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)

theorem hughesYoungCentralTailSeriesConstant_nonneg :
    0 ≤ hughesYoungCentralTailSeriesConstant := by
  unfold hughesYoungCentralTailSeriesConstant
  exact tsum_nonneg fun q => mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)

/-- The logarithmic modulus profile has an explicit uniform quadratic
majorant times one source-independent convergent series. -/
theorem tsum_hughesYoungCentralModulusProfile_le
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (a b : ℕ) :
    ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q ≤
      (1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
          |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| + 8) ^ 2 *
        hughesYoungCentralTailSeriesConstant := by
  let A : ℝ := 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant|
  let p : ℕ → ℝ := fun q => hughesYoungCentralModulusProfile X Y a b q
  let m : ℕ → ℝ := fun q =>
    (A + 8) ^ 2 * (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))
  have hlogX : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp : Summable p := by
    simpa only [p] using summable_hughesYoungCentralModulusProfile hX hY a b
  have hm : Summable m := by
    dsimp only [m]
    exact summable_natCast_inv_sq_mul_rpow_half.mul_left ((A + 8) ^ 2)
  have hpoint : ∀ q, p q ≤ m q := by
    intro q
    by_cases hq0 : q = 0
    · subst q
      simp [p, m, hughesYoungCentralModulusProfile]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hqQuarter : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow hqOne (by norm_num)
      have hlog := Real.log_natCast_le_rpow_div q
        (by norm_num : (0 : ℝ) < 1 / 4)
      have hlinear : A + 2 * Real.log (q : ℝ) ≤
          (A + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
        have hAq : A ≤ A * (q : ℝ) ^ (1 / 4 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hqQuarter hA]
        have hlog' : 2 * Real.log (q : ℝ) ≤
            8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
          norm_num at hlog ⊢
          linarith
        nlinarith
      have hhalf :
          (q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) =
            (q : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < q)]
        norm_num
      have hpow : ((q : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
          (q : ℝ) ^ (1 / 2 : ℝ) := by rw [pow_two, hhalf]
      dsimp only [p, m, hughesYoungCentralModulusProfile]
      calc
        ((q : ℝ) ^ 2)⁻¹ * (A + 2 * Real.log (q : ℝ)) ^ 2 ≤
            ((q : ℝ) ^ 2)⁻¹ *
              (((A + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) ^ 2) := by gcongr
        _ = (A + 8) ^ 2 *
            (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [mul_pow, hpow]
          ring
  calc
    _ = ∑' q, p q := by rfl
    _ ≤ ∑' q, m q := hp.tsum_le_tsum hpoint hm
    _ = _ := by
      simp only [m, tsum_mul_left, hughesYoungCentralTailSeriesConstant, A]

/-- A deliberately coarse uniform polynomial bound for the reduced static
scale.  It retains the genuine mollifier coefficients and derives every
ratio estimate from the source dyadic lower bounds. -/
theorem hughesYoungReducedStaticScale_le_power_six
    {T c X Y ell : ℝ} {h k : ℕ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hell1 : 1 ≤ ell) (hh : 0 < h) (hk : 0 < k)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell) :
    hughesYoungReducedStaticScale T c X Y h k ≤ ell ^ (6 : ℕ) := by
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ ell := by
    exact (by exact_mod_cast hughesYoungReducedLeft_le h k :
      (hughesYoungReducedLeft h k : ℝ) ≤ h).trans hhle
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ ell := by
    exact (by exact_mod_cast hughesYoungReducedRight_le h k :
      (hughesYoungReducedRight h k : ℝ) ≤ k).trans hkle
  have hratioA0 : 0 ≤ (hughesYoungReducedLeft h k : ℝ) / X := by positivity
  have hratioB0 : 0 ≤ (hughesYoungReducedRight h k : ℝ) / Y := by positivity
  have hratioA : (hughesYoungReducedLeft h k : ℝ) / X ≤ ell := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hX)).2
    nlinarith
  have hratioB : (hughesYoungReducedRight h k : ℝ) / Y ≤ ell := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hY)).2
    nlinarith
  have hp0 : 0 ≤ (1 / 2 : ℝ) + c := by linarith
  have hp2 : (1 / 2 : ℝ) + c ≤ 2 := by linarith
  have hleft :
      ((hughesYoungReducedLeft h k : ℝ) / X) ^ ((1 / 2 : ℝ) + c) ≤
        ell ^ (2 : ℝ) := by
    calc
      _ ≤ ell ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_le_rpow hratioA0 hratioA hp0
      _ ≤ ell ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hell1 hp2
  have hright :
      ((hughesYoungReducedRight h k : ℝ) / Y) ^ ((1 / 2 : ℝ) + c) ≤
        ell ^ (2 : ℝ) := by
    calc
      _ ≤ ell ^ ((1 / 2 : ℝ) + c) :=
        Real.rpow_le_rpow hratioB0 hratioB hp0
      _ ≤ ell ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hell1 hp2
  have hscalar := norm_hughesYoungLocalizedStaticScalar_le_coefficients
    (T := T) hh hk
  have hdivh : ((h.divisors.card : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self h
  have hdivk : ((k.divisors.card : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self k
  have hcoeffh : ‖shortMobiusSquareCoeff T h‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hh).trans (hdivh.trans hhle)
  have hcoeffk : ‖shortMobiusSquareCoeff T k‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hk).trans (hdivk.trans hkle)
  unfold hughesYoungReducedStaticScale
  calc
    _ ≤ (ell * ell) * (ell ^ (2 : ℝ)) * (ell ^ (2 : ℝ)) := by
      gcongr
      exact hscalar.trans (mul_le_mul hcoeffh hcoeffk (norm_nonneg _)
        (zero_le_one.trans hell1))
    _ = ell ^ (6 : ℕ) := by
      simp only [Real.rpow_two]
      ring

/-- Every logarithm in the central modulus profile is polynomially bounded
by one common source scale.  The fixed Euler constant remains visible in
the uniform numerical coefficient. -/
theorem hughesYoungCentralLogProfile_add_eight_le
    {X Y B : ℝ} {a b : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (ha : 0 < a) (hb : 0 < b)
    (hB : 1 ≤ B) (hXB : X ≤ B) (hYB : Y ≤ B)
    (haB : (a : ℝ) ≤ B) (hbB : (b : ℝ) ≤ B) :
    1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| + 8 ≤
      (15 + 4 * |Real.eulerMascheroniConstant|) * B := by
  have h2X : 0 < 2 * X := by positivity
  have h2Y : 0 < 2 * Y := by positivity
  have hlogX : Real.log (2 * X) ≤ 2 * X :=
    (Real.log_le_sub_one_of_pos h2X).trans (by linarith)
  have hlogY : Real.log (2 * Y) ≤ 2 * Y :=
    (Real.log_le_sub_one_of_pos h2Y).trans (by linarith)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hloga0 : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg ha1
  have hlogb0 : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
  have hloga : |Real.log (a : ℝ)| ≤ (a : ℝ) := by
    rw [abs_of_nonneg hloga0]
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hlogb : |Real.log (b : ℝ)| ≤ (b : ℝ) := by
    rw [abs_of_nonneg hlogb0]
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hgamma : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
  nlinarith

/-- One omitted signed central shift is bounded by a fixed polynomial in
the mollifier scale and the active arithmetic cutoff.  Membership in the
literal finite shift interval supplies the bound for the signed shift. -/
theorem hughesYoungSignedFarCentralStaticBound_le_polynomial
    {T c P X Y ell B : ℝ} {h k a b M N : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (haell : (a : ℝ) ≤ ell) (hbell : (b : ℝ) ≤ ell)
    (hellB : ell ≤ B) (hXB : X ≤ B) (hYB : Y ≤ B)
    (hMB : (M : ℝ) ≤ B) (hNB : (N : ℝ) ≤ B)
    (hr : r ∈ hughesYoungFarShifts T P X Y a b M N) :
    hughesYoungSignedFarCentralStaticBound T c X Y h k a b r ≤
      (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant * ell ^ (10 : ℕ) * B ^ (5 : ℕ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hscale := hughesYoungReducedStaticScale_le_power_six (T := T)
    hc0 hc1 hX hY hell hh hk hhle hkle
  have haB : (a : ℝ) ≤ B := haell.trans hellB
  have hbB : (b : ℝ) ≤ B := hbell.trans hellB
  have hprofileXY := tsum_hughesYoungCentralModulusProfile_le hX hY a b
  have hprofileYX := tsum_hughesYoungCentralModulusProfile_le hY hX b a
  have hlogXY := hughesYoungCentralLogProfile_add_eight_le
    hX hY ha hb hB hXB hYB haB hbB
  have hlogYX := hughesYoungCentralLogProfile_add_eight_le
    hY hX hb ha hB hYB hXB hbB haB
  have hbaseXY0 : 0 ≤ 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
      |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| + 8 := by
    have hxlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    have hylog : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
    positivity
  have hbaseYX0 : 0 ≤ 1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| + 8 := by
    have hxlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    have hylog : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
    positivity
  have hseries0 := hughesYoungCentralTailSeriesConstant_nonneg
  have hprofileXY' :
      ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q ≤
        ((15 + 4 * |Real.eulerMascheroniConstant|) * B) ^ 2 *
          hughesYoungCentralTailSeriesConstant :=
    hprofileXY.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbaseXY0 hlogXY 2) hseries0)
  have hprofileYX' :
      ∑' q : ℕ, hughesYoungCentralModulusProfile Y X b a q ≤
        ((15 + 4 * |Real.eulerMascheroniConstant|) * B) ^ 2 *
          hughesYoungCentralTailSeriesConstant :=
    hprofileYX.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbaseYX0 hlogYX 2) hseries0)
  have hinv : ‖(((a : ℂ) * b)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      nlinarith)
  have hinvSwap : ‖(((b : ℂ) * a)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      nlinarith)
  have hrange := Finset.mem_Icc.mp (mem_hughesYoungFarShifts_iff.mp hr).1
  have hab : ((a * b : ℕ) : ℝ) ≤ ell * ell := by
    push_cast
    exact mul_le_mul haell hbell (by positivity) (by positivity)
  have hba : ((b * a : ℕ) : ℝ) ≤ ell * ell := by
    simpa [Nat.mul_comm] using hab
  have habR : (a : ℝ) * b ≤ ell * ell := by
    simpa only [Nat.cast_mul] using hab
  have hbaR : (b : ℝ) * a ≤ ell * ell := by
    simpa only [Nat.cast_mul] using hba
  have hscaleT : (1 / T) * hughesYoungReducedStaticScale T c X Y h k ≤
      ell ^ (6 : ℕ) := by
    calc
      _ ≤ 1 * ell ^ (6 : ℕ) := by
        exact mul_le_mul ((div_le_one hT0).2 hT) hscale
          (hughesYoungReducedStaticScale_nonneg T c
            (zero_le_one.trans hX) (zero_le_one.trans hY) h k) (by norm_num)
      _ = _ := one_mul _
  unfold hughesYoungSignedFarCentralStaticBound
  split_ifs with hsign
  · have hto : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hsign
    have hrInt : ((r.toNat : ℕ) : ℤ) ≤ (a * M : ℕ) := by
      rw [hto]
      exact hrange.2
    have hrNat : r.toNat ≤ a * M := by exact_mod_cast hrInt
    have hrR : (r.toNat : ℝ) ≤ ell * B := by
      calc
        (r.toNat : ℝ) ≤ ((a * M : ℕ) : ℝ) := by exact_mod_cast hrNat
        _ = (a : ℝ) * M := by push_cast; ring
        _ ≤ ell * B := mul_le_mul haell hMB (by positivity) (by positivity)
    have hshift : ((a * b * r.toNat ^ 2 : ℕ) : ℝ) ≤
        (ell * ell) * (ell * B) ^ 2 := by
      push_cast
      exact mul_le_mul habR (pow_le_pow_left₀ (by positivity) hrR 2)
        (by positivity) (by positivity)
    have hprofile0 : 0 ≤ ∑' q : ℕ,
        hughesYoungCentralModulusProfile X Y a b q :=
      tsum_nonneg fun q => hughesYoungCentralModulusProfile_nonneg X Y a b q
    have hscaleT0 : 0 ≤ (1 / T) * hughesYoungReducedStaticScale T c X Y h k :=
      mul_nonneg (by positivity)
        (hughesYoungReducedStaticScale_nonneg T c
          (zero_le_one.trans hX) (zero_le_one.trans hY) h k)
    calc
      _ ≤ 1 * ((ell * ell) * (ell * B) ^ 2) * B *
          (ell ^ (6 : ℕ)) *
          (((15 + 4 * |Real.eulerMascheroniConstant|) * B) ^ 2 *
            hughesYoungCentralTailSeriesConstant) := by gcongr
      _ = _ := by ring

  · have hrNeg : r < 0 := lt_of_not_ge hsign
    have hneg : 0 ≤ -r := neg_nonneg.mpr (le_of_lt hrNeg)
    have hto : (((-r).toNat : ℕ) : ℤ) = -r := Int.toNat_of_nonneg hneg
    have hrInt : (((-r).toNat : ℕ) : ℤ) ≤ (b * N : ℕ) := by
      rw [hto]
      omega
    have hrNat : (-r).toNat ≤ b * N := by exact_mod_cast hrInt
    have hrR : ((-r).toNat : ℝ) ≤ ell * B := by
      calc
        ((-r).toNat : ℝ) ≤ ((b * N : ℕ) : ℝ) := by exact_mod_cast hrNat
        _ = (b : ℝ) * N := by push_cast; ring
        _ ≤ ell * B := mul_le_mul hbell hNB (by positivity) (by positivity)
    have hshift : ((b * a * (-r).toNat ^ 2 : ℕ) : ℝ) ≤
        (ell * ell) * (ell * B) ^ 2 := by
      push_cast
      exact mul_le_mul hbaR (pow_le_pow_left₀ (by positivity) hrR 2)
        (by positivity) (by positivity)
    have hprofile0 : 0 ≤ ∑' q : ℕ,
        hughesYoungCentralModulusProfile Y X b a q :=
      tsum_nonneg fun q => hughesYoungCentralModulusProfile_nonneg Y X b a q
    have hscaleT0 : 0 ≤ (1 / T) * hughesYoungReducedStaticScale T c X Y h k :=
      mul_nonneg (by positivity)
        (hughesYoungReducedStaticScale_nonneg T c
          (zero_le_one.trans hX) (zero_le_one.trans hY) h k)
    calc
      _ ≤ 1 * ((ell * ell) * (ell * B) ^ 2) * B *
          (ell ^ (6 : ℕ)) *
          (((15 + 4 * |Real.eulerMascheroniConstant|) * B) ^ 2 *
            hughesYoungCentralTailSeriesConstant) := by gcongr
      _ = _ := by ring

theorem card_hughesYoungFarShifts_le_shift_rectangle
    (T P X Y : ℝ) (a b M N : ℕ) :
    (hughesYoungFarShifts T P X Y a b M N).card ≤ a * M + b * N + 1 := by
  calc
    _ ≤ (hughesYoungShiftInterval a b M N).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = a * M + b * N + 1 := by
      unfold hughesYoungShiftInterval
      rw [Int.card_Icc]
      have haM0 : (0 : ℤ) ≤ ((a * M : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (a * M)
      have hbN0 : (0 : ℤ) ≤ ((b * N : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (b * N)
      have hnonneg : (0 : ℤ) ≤ ((a * M : ℕ) : ℤ) + 1 -
          -((b * N : ℕ) : ℤ) := by omega
      have hnonneg' : (0 : ℤ) ≤ (a : ℤ) * (M : ℤ) + 1 -
          -((b : ℤ) * (N : ℤ)) := by
        simpa only [Nat.cast_mul] using hnonneg
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hnonneg']
      push_cast
      ring

/-- The complete finite omitted-shift mass in one active dyadic box has a
uniform polynomial majorant. -/
theorem hughesYoungFarSignedCentralStaticMass_le_polynomial
    {T c P X Y ell B : ℝ} {h k a b M N : ℕ}
    (hT : 1 ≤ T) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (haell : (a : ℝ) ≤ ell) (hbell : (b : ℝ) ≤ ell)
    (hellB : ell ≤ B) (hXB : X ≤ B) (hYB : Y ≤ B)
    (hMB : (M : ℝ) ≤ B) (hNB : (N : ℝ) ≤ B) :
    hughesYoungFarSignedCentralStaticMass T c P X Y h k a b M N ≤
      3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant * ell ^ (11 : ℕ) * B ^ (6 : ℕ) := by
  let s := hughesYoungFarShifts T P X Y a b M N
  let E : ℝ := (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * ell ^ (10 : ℕ) * B ^ (5 : ℕ)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      hughesYoungCentralTailSeriesConstant_nonneg) (by positivity)) (by positivity)
  have hterm : ∀ r ∈ s,
      hughesYoungSignedFarCentralStaticBound T c X Y h k a b r ≤ E := by
    intro r hr
    simpa only [s, E] using hughesYoungSignedFarCentralStaticBound_le_polynomial
      hT hc0 hc1 hX hY hell hB hh hk ha hb hhle hkle haell hbell
      hellB hXB hYB hMB hNB hr
  have hcardNat := card_hughesYoungFarShifts_le_shift_rectangle
    T P X Y a b M N
  have haM : ((a * M : ℕ) : ℝ) ≤ ell * B := by
    push_cast
    exact mul_le_mul haell hMB (by positivity) (by positivity)
  have hbN : ((b * N : ℕ) : ℝ) ≤ ell * B := by
    push_cast
    exact mul_le_mul hbell hNB (by positivity) (by positivity)
  have hcard : (s.card : ℝ) ≤ 3 * ell * B := by
    have hcast : (s.card : ℝ) ≤ ((a * M + b * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    calc
      _ ≤ ((a * M + b * N + 1 : ℕ) : ℝ) := hcast
      _ = ((a * M : ℕ) : ℝ) + ((b * N : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ ell * B + ell * B + 1 := by gcongr
      _ ≤ 3 * ell * B := by nlinarith [mul_le_mul hell hB]
  unfold hughesYoungFarSignedCentralStaticMass
  change ∑ r ∈ s, hughesYoungSignedFarCentralStaticBound T c X Y h k a b r ≤ _
  calc
    _ ≤ ∑ _r ∈ s, E := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * E := by simp
    _ ≤ (3 * ell * B) * E := mul_le_mul_of_nonneg_right hcard hE
    _ = _ := by dsimp only [E]; ring

/-- Source-entry specialization of the static-mass bound to an actual box
of the large DFI family. -/
theorem hughesYoungFarSignedCentralStaticMass_le_activeEnvelope
    {T P : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungActiveLargeDFIBoxes P
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
        (hughesYoungFullDyadicScale ij.1) (hughesYoungFullDyadicScale ij.2)
        h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) ≤
      3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
        (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ) := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hc := hughesYoungSmallContour_spec hT
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hhle : h ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hhmem).2
  have hkle : k ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hkmem).2
  have ha : 0 < hughesYoungReducedLeft h k := hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k := hughesYoungReducedRight_pos hh hk
  have haell : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hhle
  have hbell : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hkle
  have hlarge := (Finset.mem_filter.mp hij).2
  have hactive := (Finset.mem_filter.mp hij).1
  have hi : 0 < ij.1 := hlarge.1
  have hj : 0 < ij.2 := hlarge.2.1
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ j
  have hMnat : hughesYoungFullDyadicBound ij.1 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hNnat : hughesYoungFullDyadicBound ij.2 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hXB : hughesYoungFullDyadicScale ij.1 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.1
    exact (by linarith : hughesYoungFullDyadicScale ij.1 ≤
      (hughesYoungFullDyadicBound ij.1 : ℝ)).trans (by exact_mod_cast hMnat)
  have hYB : hughesYoungFullDyadicScale ij.2 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.2
    exact (by linarith : hughesYoungFullDyadicScale ij.2 ≤
      (hughesYoungFullDyadicBound ij.2 : ℝ)).trans (by exact_mod_cast hNnat)
  have hell1 : 1 ≤ ell := by
    have hcut : 0 < detectorCutoff T := by
      unfold detectorCutoff
      omega
    simpa only [ell] using Nat.one_le_pow 2 (detectorCutoff T) hcut
  have hB1 : 1 ≤ B := by
    unfold B hughesYoungActiveArithmeticCutoff
    omega
  have hR : 0 < R := by
    have hprod := (Finset.mem_filter.mp hactive).2
    have hprodPos : 0 < hughesYoungFullDyadicScale ij.1 *
        hughesYoungFullDyadicScale ij.2 := mul_pos
      (hughesYoungFullDyadicScale_pos ij.1) (hughesYoungFullDyadicScale_pos ij.2)
    have hcastPos : 0 < ((hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R : ℕ) : ℝ) := hprodPos.trans_le hprod
    have hnatPos : 0 < hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R := by exact_mod_cast hcastPos
    exact pos_of_mul_pos_right hnatPos (Nat.zero_le _)
  have hellB : ell ≤ B := by
    unfold B hughesYoungActiveArithmeticCutoff
    change ell ≤ 4 * (ell * ell * R) + 1
    have hsquare : ell ≤ ell * ell := Nat.le_mul_of_pos_right ell hell1
    have hRmul : ell * ell ≤ ell * ell * R :=
      Nat.le_mul_of_pos_right (ell * ell) hR
    exact hsquare.trans (hRmul.trans (by omega))
  simpa only [ell, B] using hughesYoungFarSignedCentralStaticMass_le_polynomial
    hT1 hc.1.le hc.2.1 hX hY (by exact_mod_cast hell1) (by exact_mod_cast hB1)
    hh hk ha hb (by exact_mod_cast hhle) (by exact_mod_cast hkle)
    (by exact_mod_cast haell) (by exact_mod_cast hbell) (by exact_mod_cast hellB)
    hXB hYB (by exact_mod_cast hMnat) (by exact_mod_cast hNnat)

/-- The common analytic-polynomial envelope for one integrated omitted
signed-central box. -/
noncomputable def hughesYoungCentralTailPolynomialEnvelope
    (Cw : ℕ → ℝ) (L : ℝ) (j : ℕ) (T ell B : ℝ) : ℝ :=
  T * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * ell ^ (11 : ℕ) * B ^ (6 : ℕ)) *
    (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
      (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
      ((T / 16)⁻¹) ^ j) * L)

theorem hughesYoungCentralTailNumericalConstant_nonneg :
    0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
      (15 / 4) * Real.exp 100 * 6 := by
  have h1 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant :=
    mul_nonneg h1 hughesYoungCentralTailSeriesConstant_nonneg
  have h3 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * 9 ^ 11 :=
    mul_nonneg h2 (by norm_num)
  have h4 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 :=
    mul_nonneg h3 (by norm_num)
  have h5 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 * (15 / 4) :=
    mul_nonneg h4 (by norm_num)
  have h6 : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 * (15 / 4) *
      Real.exp 100 := mul_nonneg h5 (Real.exp_pos 100).le
  exact mul_nonneg h6 (by norm_num)

theorem hughesYoungCentralTailPolynomialEnvelope_nonneg
    {Cw : ℕ → ℝ} {L : ℝ} {j : ℕ} {T ell B : ℝ}
    (hT : Real.exp 1 ≤ T) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hell : 0 ≤ ell) (hB : 0 ≤ B) :
    0 ≤ hughesYoungCentralTailPolynomialEnvelope Cw L j T ell B := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc := (hughesYoungSmallContour_spec hT).1
  have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hseries := hughesYoungCentralTailSeriesConstant_nonneg
  have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.le
  have hdecay : 0 ≤ ((T / 16)⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr (by positivity)) j
  have hstatic : 0 ≤ 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungCentralTailSeriesConstant * ell ^ (11 : ℕ) * B ^ (6 : ℕ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hseries)
      (pow_nonneg hell 11)) (pow_nonneg hB 6)
  unfold hughesYoungCentralTailPolynomialEnvelope
  exact mul_nonneg (mul_nonneg hT0.le hstatic) (by positivity)

/-- Before equation-(65) decay, the whole signed-central tail envelope is
polynomial of degree 68 in the height. -/
theorem hughesYoungCentralTailPolynomialEnvelope_le_power68
    {Cw : ℕ → ℝ} {L : ℝ} {j : ℕ} {T ell B : ℝ}
    (hT : Real.exp 1 ≤ T) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hell0 : 0 ≤ ell) (hB0 : 0 ≤ B)
    (hell : ell ≤ 9 * T ^ (2 : ℝ))
    (hB : B ≤ 649 * T ^ (7 : ℝ)) :
    hughesYoungCentralTailPolynomialEnvelope Cw L j T ell B ≤
      (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
        (15 / 4) * Real.exp 100 * 6 *
        hughesYoungHeightInputDerivativeConstant Cw j * L) *
      ((T / 16)⁻¹) ^ j * T ^ (68 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hc := hughesYoungSmallContour_spec hT
  have hcinv : (hughesYoungSmallContour T)⁻¹ ≤ T := by
    rw [hc.2.2]
    exact (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
  have hellPow : ell ^ (11 : ℕ) ≤ (9 * T ^ (2 : ℝ)) ^ (11 : ℕ) :=
    pow_le_pow_left₀ hell0 hell 11
  have hBPow : B ^ (6 : ℕ) ≤ (649 * T ^ (7 : ℝ)) ^ (6 : ℕ) :=
    pow_le_pow_left₀ hB0 hB 6
  have hseries := hughesYoungCentralTailSeriesConstant_nonneg
  have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
  have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.1.le
  have hdecay : 0 ≤ ((T / 16)⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr (by positivity)) j
  have hanalytic : 0 ≤
      15 * T / 4 * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j * L := by
    positivity
  unfold hughesYoungCentralTailPolynomialEnvelope
  calc
    _ ≤ T * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant *
        (9 * T ^ (2 : ℝ)) ^ (11 : ℕ) *
        (649 * T ^ (7 : ℝ)) ^ (6 : ℕ)) *
      (((15 * T / 4) * T * Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j *
        ((T / 16)⁻¹) ^ j) * L) := by gcongr
    _ = _ := by
      simp only [mul_pow, Real.rpow_ofNat]
      ring

/-- Equation (65), summed over the literal large-DFI signed-central tail.
The left-hand smoothing factor is retained until the actual finite source
family has been consumed. -/
theorem exists_scaled_norm_hughesYoungActiveLargeDFIIntegratedCentralTail_le
    (j : ℕ) :
    ∃ Cγ L : ℝ, 0 < Cγ ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungActiveLargeDFIIntegratedCentralTail T P R K‖ ≤
        (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) *
        hughesYoungCentralTailPolynomialEnvelope Cw L j T
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T R : ℝ) := by
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hlocal⟩ :=
    exists_norm_hughesYoungIntegratedFarSignedCentral_full_bound j
  refine ⟨Cγ, L, hCγ, hL, Cw, hCw, ?_⟩
  intro T P R K hT hT16 hP hPT hsmall
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (P / (5 * T)) ^ j
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L j T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T R : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hc := hughesYoungSmallContour_spec hT
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      A * ‖hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ E := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hlarge := (Finset.mem_filter.mp hij).2
    have hi : 0 < ij.1 := hlarge.1
    have hj : 0 < ij.2 := hlarge.2.1
    have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
    have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using one_le_hughesYoungFullDyadicScale_succ i
    have hraw := hlocal (T := T) (c := hughesYoungSmallContour T)
      (H := T / 8) (P := P)
      (X := hughesYoungFullDyadicScale ij.1)
      (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
      (M := hughesYoungFullDyadicBound ij.1)
      (N := hughesYoungFullDyadicBound ij.2)
      hT16 hc.1 hc.2.1 hsmall (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT hX hY hh hk
    have hmass := hughesYoungFarSignedCentralStaticMass_le_activeEnvelope
      hT hhmem hkmem hij
    have hfactor : 0 ≤ T *
        hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) :=
      mul_nonneg (by positivity) (hughesYoungFarSignedCentralStaticMass_nonneg
        (by positivity) (zero_le_one.trans hX) (zero_le_one.trans hY) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2))
    have hanalytic : 0 ≤ (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
        Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j) * L) := by
      have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
      have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.1.le
      positivity
    calc
      _ ≤ T * hughesYoungFarSignedCentralStaticMass T
          (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by simpa only [A] using hraw
      _ ≤ T * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungCentralTailSeriesConstant *
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
          (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ)) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by gcongr
      _ = E := by rfl
  unfold hughesYoungActiveLargeDFIIntegratedCentralTail
  change A * ‖∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ _
  calc
    _ ≤ A * ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
            norm_sum_le _ _))) hA
    _ = ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          A * ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S, (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      calc
        _ ≤ ∑ _ij ∈ hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            E := Finset.sum_le_sum (hbox h hhmem k hkmem)
        _ = ((hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) * E := by simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungActiveLargeDFIBoxes P
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

/-- Native equation-(65) cancellation for the complete signed-central
tail envelope. -/
theorem hughesYoungNativeCentralTailEnvelope_le_rpow_neg_thirty_two
    {Cw : ℕ → ℝ} {L T : ℝ}
    (hT : Real.exp 1 ≤ T) (hL : 0 ≤ L) (hCw : ∀ i, 0 < Cw i)
    (hFar : 80 / hughesYoungDFISmoothingScale T ≤
      T ^ (-1 / 40000 : ℝ)) :
    (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ) *
        hughesYoungCentralTailPolynomialEnvelope Cw L 4000000 T
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T
            (hughesYoungConductorRadius T) : ℝ) ≤
      (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
        (15 / 4) * Real.exp 100 * 6 *
        hughesYoungHeightInputDerivativeConstant Cw 4000000 * L) *
      T ^ (-32 : ℝ) := by
  let C : ℝ := 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
    (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 4000000 * L
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  have hellTight := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hpowTwo : T ^ (1 / 50 : ℝ) ≤ T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hell : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ≤ 9 * T ^ (2 : ℝ) :=
    hellTight.trans (mul_le_mul_of_nonneg_left hpowTwo (by norm_num))
  have hB := hughesYoungConductorArithmeticCutoff_le hT
  have henv := hughesYoungCentralTailPolynomialEnvelope_le_power68 (j := 4000000)
    hT hL hCw (by positivity) (by positivity) hell hB
  have hFarPow :
      (80 / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ) ≤
        T ^ (-100 : ℝ) := by
    calc
      _ ≤ (T ^ (-1 / 40000 : ℝ)) ^ (4000000 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hFar 4000000
      _ = T ^ (-100 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw 4000000
    exact mul_nonneg
      (mul_nonneg hughesYoungCentralTailNumericalConstant_nonneg hheight.le) hL
  calc
    _ ≤ (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ) *
        (C * ((T / 16)⁻¹) ^ (4000000 : ℕ) * T ^ (68 : ℝ)) := by gcongr
    _ = C * ((5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ) *
        ((T / 16)⁻¹) ^ (4000000 : ℕ)) * T ^ (68 : ℝ) := by ac_rfl
    _ = C * (80 / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ) *
        T ^ (68 : ℝ) := by
      rw [cancelledFar_mul_hughesYoungDecay_eq hT0 hP0]
    _ ≤ C * T ^ (-100 : ℝ) * T ^ (68 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFarPow hC) (Real.rpow_nonneg hT0.le _)
    _ = C * T ^ (-32 : ℝ) := by
      rw [show C * T ^ (-100 : ℝ) * T ^ (68 : ℝ) =
          C * (T ^ (-100 : ℝ) * T ^ (68 : ℝ)) by ring,
        ← Real.rpow_add hT0]
      norm_num
    _ = _ := by rfl

/-- The literal large-DFI signed-central extension tail at the conductor
radius is negligible at the native Hughes--Young scale. -/
theorem hughesYoungConductorActiveLargeDFIIntegratedCentralTail_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveLargeDFIIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hscaled⟩ :=
    exists_scaled_norm_hughesYoungActiveLargeDFIIntegratedCentralTail_le 4000000
  let C : ℝ := 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
    (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 4000000 * L
  let A : ℝ := 81 * 103 ^ 2 * C
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw 4000000
    exact mul_nonneg
      (mul_nonneg hughesYoungCentralTailNumericalConstant_nonneg hheight.le) hL.le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) hC
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγ,
      eventually_ge_atTop (16 : ℝ)] with T hBases hRange hContour hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  let Q : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 *
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L 4000000 T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ)
  let B : ℝ := (hughesYoungDFISmoothingScale T / (5 * T)) ^ (4000000 : ℕ)
  let F : ℝ := (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ)
  have hB : 0 < B := by dsimp only [B]; exact pow_pos (div_pos hP0 (by positivity)) _
  have hBF : B * F = 1 := by
    dsimp only [B, F]
    rw [← mul_pow]
    have hbase : hughesYoungDFISmoothingScale T / (5 * T) *
        (5 * T / hughesYoungDFISmoothingScale T) = 1 := by
      field_simp [ne_of_gt hP0, ne_of_gt hT0]
    rw [hbase, one_pow]
  have hRaw := hscaled (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2 hContour.2
  have hUnscaled :
      ‖hughesYoungActiveLargeDFIIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ Q * (F * E) := by
    have hMultiplied : B * ‖hughesYoungActiveLargeDFIIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ B * (Q * (F * E)) := by
      calc
        _ ≤ Q * E := by simpa only [B, Q, E] using hRaw
        _ = B * (Q * (F * E)) := by
          calc
            Q * E = (B * F) * (Q * E) := by rw [hBF, one_mul]
            _ = B * (Q * (F * E)) := by ac_rfl
    exact le_of_mul_le_mul_left hMultiplied hB
  have hEnvelope : F * E ≤ C * T ^ (-32 : ℝ) := by
    simpa only [F, E, C] using
      hughesYoungNativeCentralTailEnvelope_le_rpow_neg_thirty_two
        hT hL.le hCw hBases.2.2.2
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) :=
    hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hCutSq : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) ≤
      81 * T ^ (4 : ℝ) := by
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (2 : ℝ)) ^ 2 = T ^ (4 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num]
        norm_num
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
        103 * T ^ (1 : ℝ) := by
      norm_num at hDepth ⊢
      exact hDepth
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by rw [Real.rpow_one, Real.rpow_two]; ring
  have hQ : Q ≤ 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
    dsimp only [Q]
    calc
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) := by gcongr
      _ = 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
        rw [show T ^ (6 : ℝ) = T ^ (4 : ℝ) * T ^ (2 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hFE0 : 0 ≤ F * E := mul_nonneg
    (by dsimp only [F]; exact pow_nonneg (div_nonneg (by positivity) hP0.le) _) hE0
  have hBound :
      ‖hughesYoungActiveLargeDFIIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-26 : ℝ) := by
    calc
      _ ≤ Q * (F * E) := hUnscaled
      _ ≤ (81 * 103 ^ 2 * T ^ (6 : ℝ)) * (C * T ^ (-32 : ℝ)) :=
        mul_le_mul hQ hEnvelope hFE0 (by positivity)
      _ = A * T ^ (-26 : ℝ) := by
        dsimp only [A]
        rw [show T ^ (-26 : ℝ) = T ^ (6 : ℝ) * T ^ (-32 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hPow : T ^ (-26 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveLargeDFIIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-- The four genuinely error-sized DFI contributions in the native
off-diagonal assembly have total `T^(1+ε)` size.  This keeps the two
complete-central complementary families out of the estimate: those are
source main terms whose cancellation must be handled before taking norms. -/
theorem hughesYoungNativeDFIErrorNormSum_epsilonPowerBound :
    EpsilonPowerBound
      (fun T =>
        ‖hughesYoungActiveNonLargeDFIOffDiagonal T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖ +
          ‖hughesYoungActiveLargeDFIIntegratedCentralTail T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖ +
          ‖hughesYoungActiveLargeDFIPointwiseDiscrepancy T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖ +
          ‖hughesYoungActiveLargeDFIFarOffDiagonal T
            (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  exact
    ((hughesYoungConductorActiveNonLargeDFIOffDiagonal_epsilonPowerBound.add
      hughesYoungConductorActiveLargeDFIIntegratedCentralTail_epsilonPowerBound).add
      hughesYoungConductorLargeDFIPointwiseDiscrepancy_epsilonPowerBound).add
      hughesYoungConductorActiveLargeDFIFarOffDiagonal_epsilonPowerBound

end RiemannZeta.GuthMaynard
