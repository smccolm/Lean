import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannZeta.GuthMaynard.DFIEquation12

open Set Filter Function MeasureTheory
open scoped BigOperators ContDiff FourierTransform Interval Topology

namespace RiemannZeta.GuthMaynard

/-!
# DFI equations (13)--(20): quantitative delta estimates

This module derives the scale-sensitive estimates following the exact delta
identity.  Constants are kept explicit and are never represented by an
assumed big-O proposition.
-/

/-- DFI equation (13) is exactly the scale-uniform derivative field carried
by the chosen delta weight. -/
theorem dfiEquation13 {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖iteratedDeriv j w.toFun u‖ ≤ C * (Q ^ (j + 1))⁻¹ :=
  w.derivativeBound j

/-- The normalized positive lattice sum is the finite sum used by the
Euler--Maclaurin formula. -/
theorem sum_Ioc_dfiWeight_eq_one {Q : ℝ} (w : DFIDeltaWeight Q) :
    ∑ r ∈ Finset.Ioc 0 (dfiDeltaRadius Q 0), w r = 1 := by
  let R := dfiDeltaRadius Q 0
  have hR : 0 < R := by
    dsimp [R, dfiDeltaRadius]
    omega
  have hRzero : w (R : ℝ) = 0 :=
    (dfiDeltaWeight_pair_eq_zero_of_radius_le w R hR le_rfl).1
  have hset : Finset.Ioc 0 R = Finset.Icc 1 R := by
    ext r
    simp
    omega
  rw [hset, ← Finset.Ico_insert_right (Nat.one_le_iff_ne_zero.mpr hR.ne')]
  rw [Finset.sum_insert]
  · rw [hRzero, zero_add]
    exact w.sum_Ico_radius_zero
  · simp

/-- The delta weight vanishes locally at the two endpoints used for the
positive Euler--Maclaurin expansion. -/
theorem dfiWeight_eventually_zero_endpoints {Q : ℝ}
    (w : DFIDeltaWeight Q) :
    w.toFun =ᶠ[𝓝 (0 : ℝ)] 0 ∧
      w.toFun =ᶠ[𝓝 (dfiDeltaRadius Q 0 : ℝ)] 0 := by
  constructor
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) w.Q_pos] with x hx
    apply w.eq_zero_of_abs_lt
    simpa [Real.dist_eq] using hx
  · have hR : 2 * Q < (dfiDeltaRadius Q 0 : ℝ) := by
      simpa using dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
    have hopen : IsOpen {x : ℝ | 2 * Q < x} := isOpen_lt continuous_const continuous_id
    filter_upwards [hopen.mem_nhds hR] with x hx
    apply w.eq_zero_of_two_mul_lt_abs
    have hxpos : 0 < x := (mul_pos two_pos w.Q_pos).trans hx
    simpa [abs_of_pos hxpos] using hx

/-- Exact normalized Euler--Maclaurin identity used to estimate the first
term on the right of DFI (12). -/
theorem dfiWeight_integral_eq_one_sub_remainder
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) (hj : 1 ≤ j) :
    (∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0), w r) =
      1 - (-1 : ℝ) ^ (j + 1) *
        ∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0),
          dfiPsi j r * iteratedDeriv j w.toFun r := by
  obtain ⟨hzero, hR⟩ := dfiWeight_eventually_zero_endpoints w
  have hEM := dfi_high_order_euler_maclaurin_of_eventually_zero
    w.toFun w.smooth (dfiDeltaRadius Q 0) j hj hzero hR
  rw [sum_Ioc_dfiWeight_eq_one w] at hEM
  linarith

/-- A continuous function supported in a real interval has `L¹` norm at
most the interval length times a pointwise bound.  This is the elementary
measure estimate used repeatedly in DFI (14)--(16). -/
theorem integral_abs_le_interval_length_mul
    (g : ℝ → ℝ) (hg : Continuous g) {a b B : ℝ}
    (hab : a ≤ b)
    (hsupp : Function.support g ⊆ Set.Icc a b)
    (hbound : ∀ x : ℝ, |g x| ≤ B) :
    (∫ x : ℝ, |g x|) ≤ (b - a) * B := by
  have hcomp : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact hsupp
  have hint : Integrable (fun x : ℝ => |g x|) :=
    hg.abs.integrable_of_hasCompactSupport (by
      change HasCompactSupport (abs ∘ g)
      exact hcomp.comp_left (by simp))
  have hzero : ∀ x ∉ Set.Icc a b, |g x| = 0 := by
    intro x hx
    have hgzero : g x = 0 := by
      by_contra hne
      exact hx (hsupp hne)
    simp [hgzero]
  have hrestrict :
      (∫ x in Set.Icc a b, |g x|) = ∫ x : ℝ, |g x| :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [← hrestrict]
  calc
    (∫ x in Set.Icc a b, |g x|) ≤
        ∫ _x in Set.Icc a b, B := by
      apply MeasureTheory.integral_mono hint.integrableOn
        (MeasureTheory.integrable_const B)
      intro x
      exact hbound x
    _ = (b - a) * B := by
      rw [MeasureTheory.setIntegral_const, measureReal_def,
        Real.volume_Icc]
      simp [hab, ENNReal.toReal_ofReal, smul_eq_mul]

/-- The order-`j` derivative of the DFI cutoff retains the original annular
support. -/
theorem support_iteratedDeriv_dfiWeight_subset
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    Function.support (iteratedDeriv j w.toFun) ⊆
      Set.Icc (-(2 * Q)) (2 * Q) := by
  intro x hx
  have hxt : x ∈ tsupport (iteratedDeriv j w.toFun) :=
    subset_tsupport _ hx
  have hxw : x ∈ tsupport w.toFun :=
    tsupport_iteratedDeriv_subset w.toFun j hxt
  have hclosed : IsClosed (Set.Icc (-(2 * Q)) (2 * Q)) := isClosed_Icc
  apply hclosed.closure_subset_iff.mpr ?_ hxw
  intro y hy
  have hann := w.support_annulus hy
  exact abs_le.mp hann.2

/-- Integrated form of DFI equation (13).  The factor `4Q` is the length of
the symmetric interval containing the annular support. -/
theorem integral_abs_iteratedDeriv_dfiWeight_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∫ u : ℝ, |iteratedDeriv j w.toFun u|) ≤
        4 * C * Q * (Q ^ (j + 1))⁻¹ := by
  obtain ⟨C, hC, hderiv⟩ := w.derivativeBound j
  refine ⟨C, hC, ?_⟩
  have hcont : Continuous (iteratedDeriv j w.toFun) :=
    w.smooth.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hbound : ∀ u : ℝ,
      |iteratedDeriv j w.toFun u| ≤ C * (Q ^ (j + 1))⁻¹ := by
    intro u
    simpa [Real.norm_eq_abs] using hderiv u
  have h := integral_abs_le_interval_length_mul
    (iteratedDeriv j w.toFun) hcont
    (show -(2 * Q) ≤ 2 * Q by nlinarith [w.Q_pos.le])
    (support_iteratedDeriv_dfiWeight_subset w j) hbound
  calc
    (∫ u : ℝ, |iteratedDeriv j w.toFun u|) ≤
        (2 * Q - -(2 * Q)) * (C * (Q ^ (j + 1))⁻¹) := h
    _ = 4 * C * Q * (Q ^ (j + 1))⁻¹ := by ring

/-- Every derivative of the removable quotient `w(r)/r` is supported in
the same symmetric cutoff interval. -/
theorem support_iteratedDeriv_dfiWeightQuotient_subset
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    Function.support (iteratedDeriv j (dfiWeightQuotient w)) ⊆
      Set.Icc (-(2 * Q)) (2 * Q) := by
  intro x hx
  have hxt : x ∈ tsupport
      (iteratedDeriv j (dfiWeightQuotient w)) := subset_tsupport _ hx
  have hxq : x ∈ tsupport (dfiWeightQuotient w) :=
    tsupport_iteratedDeriv_subset (dfiWeightQuotient w) j hxt
  have hclosed : IsClosed (Set.Icc (-(2 * Q)) (2 * Q)) := isClosed_Icc
  apply hclosed.closure_subset_iff.mpr ?_ hxq
  intro y hy
  have hwy : w y ≠ 0 := by
    intro hzero
    exact hy (by simp [dfiWeightQuotient, hzero])
  exact abs_le.mp (w.support_annulus hwy).2

/-- The scale bound for the derivatives of `w(r)/r`.  The constant is an
explicit supremum on the compact support; the power `Q^(-j-2)` records the
source homogeneity used in DFI (15). -/
theorem exists_dfiWeightQuotient_derivative_bound
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ,
      |iteratedDeriv j (dfiWeightQuotient w) r| ≤
        C * (Q ^ (j + 2))⁻¹ := by
  let F : ℝ → ℝ := fun r =>
    |iteratedDeriv j (dfiWeightQuotient w) r|
  have hFcont : Continuous F := by
    dsimp [F]
    exact ((contDiff_dfiWeightQuotient w).continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))).abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn
  let C : ℝ := max 1 (B * Q ^ (j + 2))
  have hC : 0 < C := lt_max_of_lt_left zero_lt_one
  refine ⟨C, hC, fun r => ?_⟩
  have hQpow : 0 < Q ^ (j + 2) := pow_pos w.Q_pos _
  by_cases hr : r ∈ Set.Icc (-(2 * Q)) (2 * Q)
  · have hFB : F r ≤ B := hB ⟨r, hr, rfl⟩
    have hBC : B * Q ^ (j + 2) ≤ C := le_max_right _ _
    dsimp [F] at hFB
    change |iteratedDeriv j (dfiWeightQuotient w) r| ≤
      C * (Q ^ (j + 2))⁻¹
    apply (le_mul_inv_iff₀ hQpow).2
    exact (mul_le_mul_of_nonneg_right hFB hQpow.le).trans hBC
  · have hzero : iteratedDeriv j (dfiWeightQuotient w) r = 0 := by
      by_contra hne
      exact hr (support_iteratedDeriv_dfiWeightQuotient_subset w j hne)
    rw [hzero, abs_zero]
    positivity

/-- Integrated quotient-derivative estimate underlying DFI (15). -/
theorem integral_abs_dfiWeightQuotient_derivative_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∫ r : ℝ, |iteratedDeriv j (dfiWeightQuotient w) r|) ≤
        4 * C * Q * (Q ^ (j + 2))⁻¹ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiWeightQuotient_derivative_bound w j
  refine ⟨C, hC, ?_⟩
  have hcont : Continuous
      (iteratedDeriv j (dfiWeightQuotient w)) :=
    (contDiff_dfiWeightQuotient w).continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have h := integral_abs_le_interval_length_mul
    (iteratedDeriv j (dfiWeightQuotient w)) hcont
    (show -(2 * Q) ≤ 2 * Q by nlinarith [w.Q_pos.le])
    (support_iteratedDeriv_dfiWeightQuotient_subset w j) hbound
  calc
    (∫ r : ℝ, |iteratedDeriv j (dfiWeightQuotient w) r|) ≤
        (2 * Q - -(2 * Q)) * (C * (Q ^ (j + 2))⁻¹) := h
    _ = 4 * C * Q * (Q ^ (j + 2))⁻¹ := by ring

/-- Restricting the domain can only decrease the integral of a nonnegative
integrable real function. -/
theorem setIntegral_le_integral_of_nonneg
    (g : ℝ → ℝ) (hg : Integrable g) (hgnonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) :
    (∫ x in s, g x) ≤ ∫ x : ℝ, g x := by
  exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall hgnonneg) hg

/-- A bounded periodic Euler factor can be discarded at the cost of its
uniform bound.  Compact support supplies the global integrability needed to
compare the interval integral with the whole-line `L¹` norm. -/
theorem abs_intervalIntegral_dfiPsi_mul_le
    (j : ℕ) (h : ℝ → ℝ) (hh : Continuous h)
    (hhc : HasCompactSupport h) {a b C : ℝ} (hab : a ≤ b)
    (hC : 0 ≤ C) (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ C) :
    |∫ x in a..b, dfiPsi j x * h x| ≤
      C * ∫ x : ℝ, |h x| := by
  have habsint : Integrable (fun x : ℝ => |h x|) :=
    hh.abs.integrable_of_hasCompactSupport (by
      change HasCompactSupport (abs ∘ h)
      exact hhc.comp_left (by simp))
  have hmajor : IntervalIntegrable (fun x : ℝ => C * |h x|)
      MeasureTheory.volume a b :=
    (habsint.const_mul C).intervalIntegrable
  have hpoint : ∀ᵐ x : ℝ, x ∈ Set.Ioc a b →
      ‖dfiPsi j x * h x‖ ≤ C * |h x| := by
    filter_upwards [] with x
    intro _hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hpsi x) (abs_nonneg _)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    hab hpoint hmajor
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hnorm
  refine hnorm.trans ?_
  exact mul_le_mul_of_nonneg_left
    (by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral_of_nonneg _ habsint
        (fun x => abs_nonneg _) _)
    hC

/-- DFI equation (14): the positive mass of the normalized cutoff equals
`1` up to an explicit constant times `Q⁻(j+1)`. -/
theorem dfiEquation14
    {Q : ℝ} (w : DFIDeltaWeight Q) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      |(∫ r in Set.Ioi (0 : ℝ), w r) - 1| ≤
        C * (Q ^ (j + 1))⁻¹ := by
  obtain ⟨Cpsi, hCpsi, hpsi⟩ := exists_bound_dfiPsi (j + 1)
  obtain ⟨Cw, hCw, hwderiv⟩ :=
    integral_abs_iteratedDeriv_dfiWeight_le w (j + 1)
  let C : ℝ := 4 * Cpsi * Cw
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  have hRnonneg : (0 : ℝ) ≤ dfiDeltaRadius Q 0 := Nat.cast_nonneg _
  have htruncate :
      (∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0), w r) =
        ∫ r in Set.Ioi (0 : ℝ), w r := by
    apply intervalIntegral_eq_integral_Ioi_of_eq_zero_above _ hRnonneg
    intro r hr
    apply w.eq_zero_of_two_mul_lt_abs
    have hR : 2 * Q < (dfiDeltaRadius Q 0 : ℝ) := by
      simpa using dfiDeltaRadius_spec (Q := Q) (u := (0 : ℝ))
    have hrpos : 0 < r := (mul_pos two_pos w.Q_pos).trans (hR.trans hr)
    simpa [abs_of_pos hrpos] using hR.trans hr
  have hidentity := dfiWeight_integral_eq_one_sub_remainder w (j + 1)
    (Nat.succ_le_succ (Nat.zero_le j))
  rw [htruncate] at hidentity
  have hcont : Continuous (iteratedDeriv (j + 1) w.toFun) :=
    w.smooth.continuous_iteratedDeriv (j + 1)
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top (j + 1))))
  have hcomp : HasCompactSupport (iteratedDeriv (j + 1) w.toFun) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k w.toFun) := by
      intro k
      induction k with
      | zero => simpa using w.hasCompactSupport
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux (j + 1)
  have hrem := abs_intervalIntegral_dfiPsi_mul_le
    (j + 1) (iteratedDeriv (j + 1) w.toFun) hcont hcomp
    hRnonneg hCpsi.le hpsi
  have hdiff :
      |(∫ r in Set.Ioi (0 : ℝ), w r) - 1| =
        |∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0),
          dfiPsi (j + 1) r * iteratedDeriv (j + 1) w.toFun r| := by
    rw [hidentity]
    simp only [sub_eq_add_neg]
    rw [show 1 + -((-1 : ℝ) ^ (j + 1 + 1) *
        ∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0),
          dfiPsi (j + 1) r * iteratedDeriv (j + 1) w.toFun r) + -1 =
        -((-1 : ℝ) ^ (j + 2) *
          ∫ r in (0 : ℝ)..(dfiDeltaRadius Q 0),
            dfiPsi (j + 1) r * iteratedDeriv (j + 1) w.toFun r) by ring]
    rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hdiff]
  calc
    _ ≤ Cpsi *
        ∫ r : ℝ, |iteratedDeriv (j + 1) w.toFun r| := hrem
    _ ≤ Cpsi * (4 * Cw * Q * (Q ^ (j + 1 + 1))⁻¹) :=
      mul_le_mul_of_nonneg_left hwderiv hCpsi.le
    _ = C * (Q ^ (j + 1))⁻¹ := by
      dsimp [C]
      have hQ : Q ≠ 0 := w.Q_pos.ne'
      rw [show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
      field_simp

/-- The first Euler--Maclaurin remainder in DFI (12), before multiplication
by the test-function mass, is controlled by the quotient-derivative `L¹`
norm. -/
theorem abs_dfi_first_remainder_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (q j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          iteratedDeriv j (dfiWeightQuotient w) r| ≤
        C * Q * (Q ^ (j + 2))⁻¹ := by
  obtain ⟨Cpsi, hCpsi, hpsi⟩ := exists_bound_dfiPsi j
  obtain ⟨Cw, hCw, hw⟩ :=
    integral_abs_dfiWeightQuotient_derivative_le w j
  let C : ℝ := 4 * Cpsi * Cw
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  have hrem := integrableOn_dfi_first_remainder w q j hj
  have hderivcont : Continuous
      (iteratedDeriv j (dfiWeightQuotient w)) :=
    (contDiff_dfiWeightQuotient w).continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hderivcomp : HasCompactSupport
      (iteratedDeriv j (dfiWeightQuotient w)) := by
    have haux : ∀ k : ℕ, HasCompactSupport
        (iteratedDeriv k (dfiWeightQuotient w)) := by
      intro k
      induction k with
      | zero => simpa using dfiWeightQuotient_hasCompactSupport w
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have habsint : Integrable (fun r : ℝ =>
      |iteratedDeriv j (dfiWeightQuotient w) r|) :=
    hderivcont.abs.integrable_of_hasCompactSupport (by
      change HasCompactSupport
        (abs ∘ iteratedDeriv j (dfiWeightQuotient w))
      exact hderivcomp.comp_left (by simp))
  have hmajor : IntegrableOn (fun r : ℝ => Cpsi *
      |iteratedDeriv j (dfiWeightQuotient w) r|) (Set.Ioi 0) :=
    (habsint.const_mul Cpsi).integrableOn
  calc
    |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          iteratedDeriv j (dfiWeightQuotient w) r| ≤
        ∫ r in Set.Ioi (0 : ℝ),
          |dfiPsi j (r / q) *
            iteratedDeriv j (dfiWeightQuotient w) r| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), Cpsi *
          |iteratedDeriv j (dfiWeightQuotient w) r| := by
      apply MeasureTheory.setIntegral_mono_on hrem.norm hmajor measurableSet_Ioi
      intro r _hr
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hpsi (r / q)) (abs_nonneg _)
    _ ≤ ∫ r : ℝ, Cpsi *
          |iteratedDeriv j (dfiWeightQuotient w) r| :=
      setIntegral_le_integral_of_nonneg _ (habsint.const_mul Cpsi)
        (fun r => mul_nonneg hCpsi.le (abs_nonneg _)) _
    _ = Cpsi * ∫ r : ℝ,
          |iteratedDeriv j (dfiWeightQuotient w) r| := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ Cpsi * (4 * Cw * Q * (Q ^ (j + 2))⁻¹) :=
      mul_le_mul_of_nonneg_left hw hCpsi.le
    _ = C * Q * (Q ^ (j + 2))⁻¹ := by
      dsimp [C]
      ring

/-- DFI equation (15).  The exact identity supplies `q^(j-1)`; since
`q ≥ 1`, this implies the paper's displayed (slightly weaker) `q^j` bound. -/
theorem dfiEquation15
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (j : ℕ) (hj : 2 ≤ j) (f : ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      |(q : ℝ) ^ (j - 1) * (∫ u : ℝ, f u) *
          (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            iteratedDeriv j (dfiWeightQuotient w) r)| ≤
        C * (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
          |∫ u : ℝ, f u| := by
  obtain ⟨C, hC, hrem⟩ := abs_dfi_first_remainder_le w q j hj
  refine ⟨C, hC, ?_⟩
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : (q : ℝ) ^ (j - 1) ≤ (q : ℝ) ^ j := by
    rw [show j = (j - 1) + 1 by omega, pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg q) _) hqreal
  have hQ : Q ≠ 0 := w.Q_pos.ne'
  rw [abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q) _)]
  calc
    (q : ℝ) ^ (j - 1) * |∫ u : ℝ, f u| *
        |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          iteratedDeriv j (dfiWeightQuotient w) r| ≤
      (q : ℝ) ^ (j - 1) * |∫ u : ℝ, f u| *
        (C * Q * (Q ^ (j + 2))⁻¹) := by
      gcongr
    _ = C * (q : ℝ) ^ (j - 1) * (Q ^ (j + 1))⁻¹ *
        |∫ u : ℝ, f u| := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      field_simp
    _ ≤ C * (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
        |∫ u : ℝ, f u| := by
      have hfactor : 0 ≤ C * (Q ^ (j + 1))⁻¹ *
          |∫ u : ℝ, f u| :=
        mul_nonneg
          (mul_nonneg hC.le
            (inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)))
          (abs_nonneg _)
      calc
        C * (q : ℝ) ^ (j - 1) * (Q ^ (j + 1))⁻¹ *
            |∫ u : ℝ, f u| =
          (q : ℝ) ^ (j - 1) *
            (C * (Q ^ (j + 1))⁻¹ * |∫ u : ℝ, f u|) := by ring
        _ ≤ (q : ℝ) ^ j *
            (C * (Q ^ (j + 1))⁻¹ * |∫ u : ℝ, f u|) :=
          mul_le_mul_of_nonneg_right hqpow hfactor
        _ = _ := by ring

/-- Integrability of the nonnegative two-variable kernel governing DFI
equation (16). -/
theorem integrable_dfi_abs_scaled_derivative_kernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (U j : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    Integrable (fun p : ℝ × ℝ =>
      |w p.1| * (|p.1| ^ j *
        |iteratedDeriv j f (p.2 * p.1)|)) := by
  let K : ℝ × ℝ → ℝ := fun p =>
    |w p.1| * (|p.1| ^ j *
      |iteratedDeriv j f (p.2 * p.1)|)
  have hfd : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hKcont : Continuous K := by
    dsimp [K]
    exact (w.smooth.continuous.comp continuous_fst).abs.mul
      ((continuous_fst.abs.pow j).mul
        ((hfd.comp (continuous_snd.mul continuous_fst)).abs))
  have hKcomp : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ) (2 * Q)).prod
        (isCompact_closedBall (0 : ℝ) (U : ℝ)))
    intro p hp
    have hKne : K p ≠ 0 := hp
    have hwne : w p.1 ≠ 0 := by
      intro hw
      exact hKne (by simp [K, hw])
    have hdne : iteratedDeriv j f (p.2 * p.1) ≠ 0 := by
      intro hd
      exact hKne (by simp [K, hd])
    have huann := w.support_annulus hwne
    have hderivmem : p.2 * p.1 ∈ tsupport (iteratedDeriv j f) :=
      subset_tsupport _ hdne
    have hfrange := hsupp
      (tsupport_iteratedDeriv_subset f j hderivmem)
    have hulow : 1 ≤ |p.1| := w.one_le_Q.trans huann.1
    have hprod : |p.1| * |p.2| ≤ U := by
      rw [← abs_mul]
      simpa [mul_comm] using (abs_le.mpr hfrange)
    have hrhigh : |p.2| ≤ U := by
      nlinarith [abs_nonneg p.2]
    constructor
    · simpa [Metric.mem_closedBall, Real.dist_eq] using huann.2
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hrhigh
  exact hKcont.integrable_of_hasCompactSupport hKcomp

/-- Fubini for the nonnegative kernel governing DFI equation (16).  The
annular support of `w` prevents the hyperbolic support condition `ru ∈
tsupport (f^(j))` from escaping to infinity. -/
theorem dfi_abs_scaled_derivative_swap
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (U j : ℕ)
    (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    (∫ r : ℝ, ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) =
      ∫ u : ℝ, ∫ r : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|) := by
  let K : ℝ → ℝ → ℝ := fun u r =>
    |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)
  have hfd : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hKcont : Continuous K.uncurry := by
    dsimp [K, Function.uncurry]
    exact (w.smooth.continuous.comp continuous_fst).abs.mul
      ((continuous_fst.abs.pow j).mul
        ((hfd.comp (continuous_snd.mul continuous_fst)).abs))
  have hKcomp : HasCompactSupport K.uncurry := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ) (2 * Q)).prod
        (isCompact_closedBall (0 : ℝ) (U : ℝ)))
    intro p hp
    have hKne : K p.1 p.2 ≠ 0 := hp
    have hwne : w p.1 ≠ 0 := by
      intro hw
      exact hKne (by simp [K, hw])
    have hdne : iteratedDeriv j f (p.2 * p.1) ≠ 0 := by
      intro hd
      exact hKne (by simp [K, hd])
    have huann := w.support_annulus hwne
    have hderivmem : p.2 * p.1 ∈ tsupport (iteratedDeriv j f) :=
      subset_tsupport _ hdne
    have hfrange := hsupp
      (tsupport_iteratedDeriv_subset f j hderivmem)
    have hulow : 1 ≤ |p.1| := w.one_le_Q.trans huann.1
    have hprod : |p.1| * |p.2| ≤ U := by
      rw [← abs_mul]
      simpa [mul_comm] using (abs_le.mpr hfrange)
    have hrhigh : |p.2| ≤ U := by
      nlinarith [abs_nonneg p.2]
    constructor
    · simpa [Metric.mem_closedBall, Real.dist_eq] using huann.2
    · simpa [Metric.mem_closedBall, Real.dist_eq] using hrhigh
  exact (integral_integral_swap_of_hasCompactSupport
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    hKcont hKcomp).symm

/-- Exact whole-line rescaling of the inner nonnegative derivative kernel
in equation (16). -/
theorem integral_abs_iteratedDeriv_mul_right
    (f : ℝ → ℝ) (j : ℕ) (u : ℝ) :
    (∫ r : ℝ, |iteratedDeriv j f (r * u)|) =
      |u⁻¹| * ∫ v : ℝ, |iteratedDeriv j f v| := by
  simpa [smul_eq_mul] using
    (Measure.integral_comp_mul_right
      (fun v : ℝ => |iteratedDeriv j f v|) u)

/-- The absolute double integral in DFI equation (16) has the required
`Q^(j-1)` scale.  This is where the annular lower bound on `|u|` and the
Jacobian from `r ↦ ru` are both used. -/
theorem integral_Ioi_abs_weight_scaled_deriv_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U j : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      (∫ r in Set.Ioi (0 : ℝ), ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
        C * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v| := by
  obtain ⟨Cw, hCw, hwL1⟩ :=
    integral_abs_iteratedDeriv_dfiWeight_le w 0
  let C : ℝ := 4 * Cw * 2 ^ j
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  let D : ℝ := ∫ v : ℝ, |iteratedDeriv j f v|
  have hfdcont : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hfdcomp : HasCompactSupport (iteratedDeriv j f) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
      intro k
      induction k with
      | zero => simpa using hfc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have hfdint : Integrable (fun v : ℝ => |iteratedDeriv j f v|) :=
    hfdcont.abs.integrable_of_hasCompactSupport (by
      change HasCompactSupport (abs ∘ iteratedDeriv j f)
      exact hfdcomp.comp_left (by simp))
  have hDnonneg : 0 ≤ D := integral_nonneg fun _ => abs_nonneg _
  have hwcont : Continuous (fun u : ℝ => |w u|) := w.smooth.continuous.abs
  have hwint : Integrable (fun u : ℝ => |w u|) :=
    hwcont.integrable_of_hasCompactSupport (by
      change HasCompactSupport (abs ∘ w.toFun)
      exact w.hasCompactSupport.comp_left (by simp))
  have hKint := integrable_dfi_abs_scaled_derivative_kernel
    w f hf U j hsupp
  have houterInt : Integrable (fun r : ℝ => ∫ u : ℝ,
      |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) :=
    hKint.integral_prod_right
  have houterNonneg : ∀ r : ℝ, 0 ≤ ∫ u : ℝ,
      |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|) := by
    intro r
    apply integral_nonneg
    intro u
    positivity
  have hrestrict :
      (∫ r in Set.Ioi (0 : ℝ), ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
      ∫ r : ℝ, ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|) :=
    setIntegral_le_integral_of_nonneg _ houterInt houterNonneg _
  have hpoint : ∀ u : ℝ,
      (∫ r : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
      |w u| * ((2 * Q) ^ j * Q⁻¹ * D) := by
    intro u
    by_cases hwu : w u = 0
    · simp [hwu]
    · have huann := w.support_annulus hwu
      have huPos : 0 < |u| := w.Q_pos.trans_le huann.1
      have huPow : |u| ^ j ≤ (2 * Q) ^ j :=
        pow_le_pow_left₀ (abs_nonneg u) huann.2 j
      have huInv : |u⁻¹| ≤ Q⁻¹ := by
        rw [abs_inv]
        exact (inv_le_inv₀ huPos w.Q_pos).2 huann.1
      calc
        (∫ r : ℝ,
            |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) =
          ∫ r : ℝ, (|w u| * |u| ^ j) *
            |iteratedDeriv j f (r * u)| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with r
          ring
        _ = (|w u| * |u| ^ j) *
            (∫ r : ℝ, |iteratedDeriv j f (r * u)|) := by
          rw [MeasureTheory.integral_const_mul]
        _ = |w u| * |u| ^ j * (|u⁻¹| * D) := by
          rw [integral_abs_iteratedDeriv_mul_right]
        _ ≤ |w u| * ((2 * Q) ^ j * Q⁻¹ * D) := by
          have hwuNonneg : 0 ≤ |w u| := abs_nonneg _
          have hQinv : 0 ≤ Q⁻¹ := inv_nonneg.mpr w.Q_pos.le
          calc
            |w u| * |u| ^ j * (|u⁻¹| * D) =
                |w u| * (|u| ^ j * |u⁻¹| * D) := by ring
            _ ≤ |w u| * ((2 * Q) ^ j * Q⁻¹ * D) := by
              apply mul_le_mul_of_nonneg_left _ hwuNonneg
              apply mul_le_mul_of_nonneg_right _ hDnonneg
              exact mul_le_mul huPow huInv (abs_nonneg _)
                (pow_nonneg (mul_nonneg zero_le_two w.Q_pos.le) _)
  have hinnerInt : Integrable (fun u : ℝ => ∫ r : ℝ,
      |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) :=
    hKint.integral_prod_left
  have hA : 0 ≤ (2 * Q) ^ j * Q⁻¹ * D :=
    mul_nonneg
      (mul_nonneg (pow_nonneg (mul_nonneg zero_le_two w.Q_pos.le) _)
        (inv_nonneg.mpr w.Q_pos.le))
      hDnonneg
  have hmajorInt : Integrable (fun u : ℝ =>
      |w u| * ((2 * Q) ^ j * Q⁻¹ * D)) :=
    hwint.mul_const _
  have hwhole :
      (∫ r : ℝ, ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
      (∫ u : ℝ, |w u|) * ((2 * Q) ^ j * Q⁻¹ * D) := by
    rw [dfi_abs_scaled_derivative_swap w f hf U j hsupp]
    calc
      (∫ u : ℝ, ∫ r : ℝ,
          |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
        ∫ u : ℝ, |w u| * ((2 * Q) ^ j * Q⁻¹ * D) := by
          exact MeasureTheory.integral_mono hinnerInt hmajorInt hpoint
      _ = _ := by rw [MeasureTheory.integral_mul_const]
  have hwL1' : (∫ u : ℝ, |w u|) ≤ 4 * Cw := by
    calc
      (∫ u : ℝ, |w u|) ≤
          4 * Cw * Q * (Q ^ (0 + 1))⁻¹ := hwL1
      _ = 4 * Cw := by
        simp only [zero_add, pow_one]
        field_simp [w.Q_pos.ne']
  calc
    (∫ r in Set.Ioi (0 : ℝ), ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)) ≤
      ∫ r : ℝ, ∫ u : ℝ,
        |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|) := hrestrict
    _ ≤ (∫ u : ℝ, |w u|) * ((2 * Q) ^ j * Q⁻¹ * D) := hwhole
    _ ≤ (4 * Cw) * ((2 * Q) ^ j * Q⁻¹ * D) :=
      mul_le_mul_of_nonneg_right hwL1' hA
    _ = C * Q ^ (j - 1) * D := by
      dsimp [C]
      let k := j - 1
      have hjk : j = k + 1 := by dsimp [k]; omega
      rw [hjk]
      simp only [Nat.add_sub_cancel]
      rw [pow_succ, mul_pow]
      field_simp [w.Q_pos.ne']
      ring

/-- The second Euler--Maclaurin remainder in DFI (12), before its exterior
power of `q`, is bounded by the scale-sensitive absolute kernel. -/
theorem abs_dfi_second_remainder_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U j : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          ∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| ≤
        C * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v| := by
  obtain ⟨Cpsi, hCpsi, hpsi⟩ := exists_bound_dfiPsi j
  obtain ⟨Ckernel, hCkernel, hkernel⟩ :=
    integral_Ioi_abs_weight_scaled_deriv_le
      w f hf hfc U j hsupp (by omega)
  let C : ℝ := Cpsi * Ckernel
  have hC : 0 < C := mul_pos hCpsi hCkernel
  refine ⟨C, hC, ?_⟩
  let Kouter : ℝ → ℝ := fun r => ∫ u : ℝ,
    |w u| * (|u| ^ j * |iteratedDeriv j f (r * u)|)
  have hKint := integrable_dfi_abs_scaled_derivative_kernel
    w f hf U j hsupp
  have hKouterInt : Integrable Kouter := by
    simpa [Kouter] using hKint.integral_prod_right
  have hmajor : IntegrableOn (fun r : ℝ => Cpsi * Kouter r)
      (Set.Ioi 0) := (hKouterInt.const_mul Cpsi).integrableOn
  have hrem := integrableOn_dfi_second_remainder
    w f hf U hsupp q j hj
  have hpoint : ∀ r : ℝ,
      |dfiPsi j (r / q) *
          (∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u)))| ≤
        Cpsi * Kouter r := by
    intro r
    have hinner :
        |∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| ≤ Kouter r := by
      calc
        |∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| ≤
          ∫ u : ℝ, |w u *
            (u ^ j * iteratedDeriv j f (r * u))| :=
          MeasureTheory.abs_integral_le_integral_abs
        _ = Kouter r := by
          dsimp [Kouter]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with u
          rw [abs_mul, abs_mul, abs_pow]
    rw [abs_mul]
    exact mul_le_mul (hpsi (r / q)) hinner (abs_nonneg _) hCpsi.le
  calc
    |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          ∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| ≤
      ∫ r in Set.Ioi (0 : ℝ),
        |dfiPsi j (r / q) *
          ∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), Cpsi * Kouter r := by
      apply MeasureTheory.setIntegral_mono_on hrem.norm hmajor measurableSet_Ioi
      intro r _hr
      exact hpoint r
    _ = Cpsi * ∫ r in Set.Ioi (0 : ℝ), Kouter r := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ Cpsi * (Ckernel * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v|) :=
      mul_le_mul_of_nonneg_left hkernel hCpsi.le
    _ = C * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v| := by
      dsimp [C]
      ring

/-- DFI equation (16), with the paper's `q^j` exterior factor.  As in
equation (15), it follows by weakening the corrected identity's stronger
`q^(j-1)` coefficient. -/
theorem dfiEquation16
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U j : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      |(q : ℝ) ^ (j - 1) *
          (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            ∫ u : ℝ, w u *
              (u ^ j * iteratedDeriv j f (r * u)))| ≤
        C * (q : ℝ) ^ j * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v| := by
  obtain ⟨C, hC, hrem⟩ :=
    abs_dfi_second_remainder_le w q f hf hfc U j hsupp hj
  refine ⟨C, hC, ?_⟩
  have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : (q : ℝ) ^ (j - 1) ≤ (q : ℝ) ^ j := by
    rw [show j = (j - 1) + 1 by omega, pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg q) _) hqreal
  rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q) _)]
  calc
    (q : ℝ) ^ (j - 1) *
        |∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          ∫ u : ℝ, w u *
            (u ^ j * iteratedDeriv j f (r * u))| ≤
      (q : ℝ) ^ (j - 1) *
        (C * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v|) :=
      mul_le_mul_of_nonneg_left hrem
        (pow_nonneg (Nat.cast_nonneg q) _)
    _ ≤ (q : ℝ) ^ j *
        (C * Q ^ (j - 1) *
          ∫ v : ℝ, |iteratedDeriv j f v|) := by
      apply mul_le_mul_of_nonneg_right hqpow
      exact mul_nonneg
        (mul_nonneg hC.le (pow_nonneg w.Q_pos.le _))
        (integral_nonneg fun _ => abs_nonneg _)
    _ = C * (q : ℝ) ^ j * Q ^ (j - 1) *
        ∫ v : ℝ, |iteratedDeriv j f v| := by ring

/-- Real iterated derivatives commute with the canonical embedding into
`ℂ`.  This bridge lets the Fourier argument for DFI (17) use Mathlib's
complex-valued Fourier transform without changing the source test function. -/
theorem iteratedDeriv_ofReal_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => (f x : ℂ)) =
      fun x : ℝ => ((iteratedDeriv j f x : ℝ) : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show j + 1 = Nat.succ j by omega,
        iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hjtop : (j : WithTop ℕ∞) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.coe_lt_top j)
      have hreal : HasDerivAt (iteratedDeriv j f)
          (deriv (iteratedDeriv j f) x) x :=
        (hf.differentiable_iteratedDeriv j hjtop).differentiableAt.hasDerivAt
      exact hreal.ofReal_comp.deriv

/-- The Fourier transform of a smooth compactly supported real function,
viewed in `ℂ`, is integrable. -/
theorem integrable_fourier_ofReal_of_contDiff_hasCompactSupport
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable (𝓕 (fun x : ℝ => (f x : ℂ))) := by
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  have hfcSmooth : ContDiff ℝ ∞ fc :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfcComp : HasCompactSupport fc := by
    change HasCompactSupport (Complex.ofReal ∘ f)
    exact hfc.comp_left rfl
  let F : SchwartzMap ℝ ℂ := hfcComp.toSchwartzMap hfcSmooth
  have hcoe : (F : ℝ → ℂ) = fc := rfl
  rw [show (fun x : ℝ => (f x : ℂ)) = fc by rfl, ← hcoe,
    ← SchwartzMap.fourier_coe]
  exact (𝓕 F).integrable

/-- Fourier inversion at the origin, followed by the triangle inequality. -/
theorem abs_apply_le_integral_norm_fourier_ofReal
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    |f 0| ≤ ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ := by
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  have hfcSmooth : ContDiff ℝ ∞ fc :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfcComp : HasCompactSupport fc := by
    change HasCompactSupport (Complex.ofReal ∘ f)
    exact hfc.comp_left rfl
  have hfcInt : Integrable fc :=
    hfcSmooth.continuous.integrable_of_hasCompactSupport hfcComp
  have hhatInt : Integrable (𝓕 fc) := by
    simpa [fc] using
      integrable_fourier_ofReal_of_contDiff_hasCompactSupport f hf hfc
  have hinv := hfcSmooth.continuous.fourierInv_fourier_eq hfcInt hhatInt
  have hzero := congrFun hinv (0 : ℝ)
  calc
    |f 0| = ‖fc 0‖ := by simp [fc]
    _ = ‖𝓕⁻ (𝓕 fc) 0‖ := by rw [hzero]
    _ ≤ ∫ ξ : ℝ, ‖𝓕 fc ξ‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 MeasureTheory.volume (-innerₗ ℝ) (𝓕 fc) 0
    _ = ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ := by rfl

/-- The elementary `L¹ → L∞` Fourier estimate for a real-valued test
function embedded in `ℂ`. -/
theorem norm_fourier_ofReal_le_integral_abs
    (f : ℝ → ℝ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤ ∫ x : ℝ, |f x| := by
  calc
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
        ∫ x : ℝ, ‖(f x : ℂ)‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 MeasureTheory.volume (innerₗ ℝ)
        (fun x : ℝ => (f x : ℂ)) ξ
    _ = ∫ x : ℝ, |f x| := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp

/-- Every derivative of the complexification of a smooth compactly
supported real function is integrable. -/
theorem integrable_iteratedDeriv_ofReal
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) :
    Integrable (iteratedDeriv j (fun x : ℝ => (f x : ℂ))) := by
  rw [iteratedDeriv_ofReal_comp f hf j]
  have hcont : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hcomp : HasCompactSupport (iteratedDeriv j f) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
      intro k
      induction k with
      | zero => simpa using hfc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have hreal : Integrable (iteratedDeriv j f) :=
    hcont.integrable_of_hasCompactSupport hcomp
  exact Complex.ofRealCLM.integrable_comp hreal

/-- Fourier integration by parts: the `j`-th derivative controls the
Fourier transform after multiplication by `|ξ|^j`.  The harmless factor
`(2π)^j ≥ 1` from Mathlib's Fourier convention is discarded. -/
theorem abs_pow_mul_norm_fourier_ofReal_le
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
      ∫ x : ℝ, |iteratedDeriv j f x| := by
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  have hfcSmooth : ContDiff ℝ ∞ fc :=
    Complex.ofRealCLM.contDiff.comp hf
  have hall : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv n fc) := by
    intro n _hn
    simpa [fc] using integrable_iteratedDeriv_ofReal f hf hfc n
  have hjtop : j ≤ (⊤ : ℕ∞) := le_of_lt (ENat.coe_lt_top j)
  have hFourier := Real.fourier_iteratedDeriv hfcSmooth hall hjtop
  have hpoint := congrFun hFourier ξ
  rw [iteratedDeriv_ofReal_comp f hf j] at hpoint
  have hpoint' :
      𝓕 (fun x : ℝ => ((iteratedDeriv j f x : ℝ) : ℂ)) ξ =
        (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j • (𝓕 fc ξ) := by
    simpa [fc] using hpoint
  have hfactor :
      ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ =
        (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow, norm_mul, norm_mul]
    simp [abs_of_nonneg Real.pi_pos.le]
  have hnormeq := congrArg norm hpoint'
  rw [norm_smul, hfactor] at hnormeq
  have hbase : |ξ| ≤ 2 * Real.pi * |ξ| := by
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hpow : |ξ| ^ j ≤ (2 * Real.pi * |ξ|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg ξ) hbase j
  calc
    |ξ| ^ j * ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
        (2 * Real.pi * |ξ|) ^ j * ‖𝓕 fc ξ‖ := by
      simpa [fc] using mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = ‖𝓕 (fun x : ℝ =>
          ((iteratedDeriv j f x : ℝ) : ℂ)) ξ‖ := hnormeq.symm
    _ ≤ ∫ x : ℝ, |iteratedDeriv j f x| :=
      norm_fourier_ofReal_le_integral_abs (iteratedDeriv j f) ξ

/-- On `|ξ| ≥ 1`, every inverse power of order at least two is dominated
by the integrable Cauchy kernel used in the Fourier split. -/
theorem inv_abs_pow_le_two_mul_inv_one_add_sq
    {ξ : ℝ} (hξ : 1 ≤ |ξ|) {j : ℕ} (hj : 2 ≤ j) :
    (|ξ| ^ j)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
  have hξpos : 0 < |ξ| := zero_lt_one.trans_le hξ
  have hpow : |ξ| ^ 2 ≤ |ξ| ^ j :=
    pow_le_pow_right₀ hξ hj
  have hinvPow : (|ξ| ^ j)⁻¹ ≤ (|ξ| ^ 2)⁻¹ :=
    (inv_le_inv₀ (pow_pos hξpos j) (pow_pos hξpos 2)).2 hpow
  have hξsq : (1 : ℝ) ≤ ξ ^ 2 := by
    nlinarith [sq_abs ξ, sq_nonneg (|ξ| - 1)]
  have hkernel : (|ξ| ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
    rw [sq_abs]
    have hξne : ξ ≠ 0 := by
      intro hzero
      subst ξ
      norm_num at hξ
    have hsqpos : 0 < ξ ^ 2 := by positivity
    have htwosqpos : 0 < 2 * ξ ^ 2 := mul_pos (by norm_num) hsqpos
    have hden : 0 < 1 + ξ ^ 2 := by positivity
    have hdenle : 1 + ξ ^ 2 ≤ 2 * ξ ^ 2 := by nlinarith
    have hinv : (2 * ξ ^ 2)⁻¹ ≤ (1 + ξ ^ 2)⁻¹ :=
      (inv_le_inv₀ htwosqpos hden).2 hdenle
    calc
      (ξ ^ 2)⁻¹ = 2 * (2 * ξ ^ 2)⁻¹ := by field_simp [hξne]
      _ ≤ 2 * (1 + ξ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
  exact hinvPow.trans hkernel

/-- Pointwise high-frequency estimate used in DFI equation (17). -/
theorem norm_fourier_ofReal_high_frequency_le
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {j : ℕ} (hj : 2 ≤ j) {ξ : ℝ} (hξ : 1 ≤ |ξ|) :
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
      (2 * (1 + ξ ^ 2)⁻¹) *
        ∫ x : ℝ, |iteratedDeriv j f x| := by
  let B : ℝ := ∫ x : ℝ, |iteratedDeriv j f x|
  have hB : 0 ≤ B := integral_nonneg fun _ => abs_nonneg _
  have hweighted := abs_pow_mul_norm_fourier_ofReal_le f hf hfc j ξ
  have hpowPos : 0 < |ξ| ^ j := pow_pos (zero_lt_one.trans_le hξ) j
  have hdivide : ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
      B * (|ξ| ^ j)⁻¹ := by
    apply (le_mul_inv_iff₀ hpowPos).2
    simpa [B, mul_comm] using hweighted
  calc
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤
        (|ξ| ^ j)⁻¹ * B := by simpa [mul_comm] using hdivide
    _ ≤ (2 * (1 + ξ ^ 2)⁻¹) * B :=
      mul_le_mul_of_nonneg_right
        (inv_abs_pow_le_two_mul_inv_one_add_sq hξ hj) hB
    _ = _ := rfl

/-- The order-one endpoint estimate used to cover the case not handled by
the integrable high-frequency Fourier majorant. -/
theorem dfiEquation17_order_one
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    |f 0| ≤ (∫ u : ℝ, |f u|) + ∫ u : ℝ, |iteratedDeriv 1 f u| := by
  let B : ℝ := U + 1
  have hBpos : 0 ≤ B := by positivity
  have hfB : f B = 0 := by
    by_contra hne
    have hmem : B ∈ tsupport f := subset_tsupport _ hne
    have hrange := hsupp hmem
    dsimp [B] at hrange
    exact (not_le_of_gt (by norm_num : (U : ℝ) < U + 1)) hrange.2
  have hderiv : deriv f = iteratedDeriv 1 f := by
    funext x
    simp [iteratedDeriv_succ]
  have hftc : (∫ u in (0 : ℝ)..B, iteratedDeriv 1 f u) = -f 0 := by
    have h := intervalIntegral.integral_deriv_eq_sub' f hderiv
      (fun _x _ => (hf.differentiable (by simp)).differentiableAt)
      ((hf.continuous_iteratedDeriv 1
        (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top 1)))).continuousOn)
      (a := (0 : ℝ)) (b := B)
    simpa [hfB] using h
  have hfdcont : Continuous (iteratedDeriv 1 f) :=
    hf.continuous_iteratedDeriv 1
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top 1)))
  have hfdcomp : HasCompactSupport (iteratedDeriv 1 f) := by
    have hone : iteratedDeriv 1 f = deriv f := by
      funext x
      simp [iteratedDeriv_succ]
    rw [hone]
    exact hfc.deriv
  have hfdint : Integrable (fun u : ℝ => |iteratedDeriv 1 f u|) :=
    hfdcont.abs.integrable_of_hasCompactSupport (by
      change HasCompactSupport (abs ∘ iteratedDeriv 1 f)
      exact hfdcomp.comp_left (by simp))
  have hinterval :
      (∫ u in (0 : ℝ)..B, |iteratedDeriv 1 f u|) ≤
        ∫ u : ℝ, |iteratedDeriv 1 f u| := by
    rw [intervalIntegral.integral_of_le hBpos]
    exact setIntegral_le_integral_of_nonneg _ hfdint (fun x => abs_nonneg _) _
  have hbasic : |f 0| ≤ ∫ u : ℝ, |iteratedDeriv 1 f u| := by
    rw [← neg_neg (f 0), ← hftc, abs_neg]
    exact (intervalIntegral.abs_integral_le_integral_abs hBpos).trans hinterval
  exact hbasic.trans (le_add_of_nonneg_left (integral_nonneg fun x => abs_nonneg _))

/-- DFI equation (17), with an explicit absolute constant.  For derivative
order at least two this is Fourier inversion split at unit frequency; order
one is the sharper fundamental-theorem-of-calculus estimate above. -/
theorem dfiEquation17
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    {j : ℕ} (hj : 1 ≤ j) :
    |f 0| ≤ (2 + 2 * Real.pi) *
      ((∫ u : ℝ, |f u|) + ∫ u : ℝ, |iteratedDeriv j f u|) := by
  rcases Nat.eq_or_lt_of_le hj with rfl | hjTwo
  · have horder := dfiEquation17_order_one f hf hfc U hsupp
    have hsum : 0 ≤
        (∫ u : ℝ, |f u|) + ∫ u : ℝ, |iteratedDeriv 1 f u| :=
      add_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (integral_nonneg fun _ => abs_nonneg _)
    have hconstant : 1 ≤ 2 + 2 * Real.pi := by
      nlinarith [Real.pi_pos]
    exact horder.trans (by nlinarith)
  · let A : ℝ := ∫ u : ℝ, |f u|
    let B : ℝ := ∫ u : ℝ, |iteratedDeriv j f u|
    let low : ℝ → ℝ := Set.Icc (-1 : ℝ) 1 |>.indicator (fun _ => A)
    let high : ℝ → ℝ := fun ξ => (2 * (1 + ξ ^ 2)⁻¹) * B
    have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
    have hB : 0 ≤ B := integral_nonneg fun _ => abs_nonneg _
    have hhatInt : Integrable
        (fun ξ : ℝ => ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖) :=
      (integrable_fourier_ofReal_of_contDiff_hasCompactSupport f hf hfc).norm
    have hlowInt : Integrable low := by
      dsimp only [low]
      exact (MeasureTheory.integrableOn_const
        (μ := MeasureTheory.volume) (s := Set.Icc (-1 : ℝ) 1) (C := A)
        (by rw [Real.volume_Icc]; norm_num) (by finiteness)).integrable_indicator
          measurableSet_Icc
    have hkernelInt : Integrable (fun ξ : ℝ => (1 + ξ ^ 2)⁻¹) :=
      integrable_inv_one_add_sq
    have hhighInt : Integrable high := by
      simpa [high, mul_assoc] using (hkernelInt.const_mul 2).mul_const B
    have hpoint : ∀ ξ : ℝ,
        ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤ low ξ + high ξ := by
      intro ξ
      by_cases hξmem : ξ ∈ Set.Icc (-1 : ℝ) 1
      · have hbase := norm_fourier_ofReal_le_integral_abs f ξ
        have hhighNonneg : 0 ≤ high ξ := by
          dsimp [high]
          positivity
        simpa [low, Set.indicator_of_mem hξmem, A] using
          hbase.trans (le_add_of_nonneg_right hhighNonneg)
      · have hout : ξ < -1 ∨ 1 < ξ := by
          by_cases hleft : ξ < -1
          · exact Or.inl hleft
          · exact Or.inr (lt_of_not_ge fun hright =>
              hξmem ⟨le_of_not_gt hleft, hright⟩)
        have habs : 1 ≤ |ξ| := by
          rcases hout with hleft | hright
          · rw [abs_of_neg (by linarith)]
            linarith
          · rw [abs_of_pos (by linarith)]
            linarith
        have hbase := norm_fourier_ofReal_high_frequency_le f hf hfc hjTwo habs
        simpa [low, high, hξmem, B] using hbase
    have hintegral :
        (∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖) ≤
          ∫ ξ : ℝ, low ξ + high ξ :=
      MeasureTheory.integral_mono hhatInt (hlowInt.add hhighInt) hpoint
    have hlowIntegral : (∫ ξ : ℝ, low ξ) = 2 * A := by
      simp only [low]
      rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.setIntegral_const]
      have hvol : MeasureTheory.volume (Set.Icc (-1 : ℝ) 1) = 2 := by
        rw [Real.volume_Icc]
        norm_num
      change (MeasureTheory.volume (Set.Icc (-1 : ℝ) 1)).toReal * A = 2 * A
      rw [hvol]
      norm_num
    have hhighIntegral : (∫ ξ : ℝ, high ξ) = (2 * Real.pi) * B := by
      simp only [high]
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul,
        integral_univ_inv_one_add_sq]
    have hfourier : |f 0| ≤ 2 * A + (2 * Real.pi) * B := by
      calc
        |f 0| ≤ ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ :=
          abs_apply_le_integral_norm_fourier_ofReal f hf hfc
        _ ≤ ∫ ξ : ℝ, low ξ + high ξ := hintegral
        _ = (∫ ξ : ℝ, low ξ) + ∫ ξ : ℝ, high ξ :=
          MeasureTheory.integral_add hlowInt hhighInt
        _ = 2 * A + (2 * Real.pi) * B := by rw [hlowIntegral, hhighIntegral]
    change |f 0| ≤ (2 + 2 * Real.pi) * (A + B)
    nlinarith [Real.pi_pos]

/-- DFI equation (18), with all implicit constants made explicit by an
existential absolute constant.  This is the quantitative delta-symbol
approximation obtained by assembling equations (12)--(17). -/
theorem dfiEquation18
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (U j : ℕ) (hsupp : tsupport f ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      |dfiEquation12Left w q f - f 0| ≤
        C * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |f u|) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ, |iteratedDeriv j f u|) := by
  obtain ⟨Cmass, hCmass, hmass⟩ := dfiEquation14 w j
  obtain ⟨Cfirst, hCfirst, hfirst⟩ := dfiEquation15 w q hq j hj f
  obtain ⟨Csecond, hCsecond, hsecond⟩ :=
    dfiEquation16 w q hq f hf hfc U j hsupp hj
  let Cpoint : ℝ := 2 + 2 * Real.pi
  let C : ℝ := Cmass * Cpoint + Cfirst + Csecond
  refine ⟨C, by positivity, ?_⟩
  let A : ℝ := ∫ u : ℝ, |f u|
  let B : ℝ := ∫ u : ℝ, |iteratedDeriv j f u|
  let p : ℝ := (q : ℝ) ^ j
  let x : ℝ := (Q ^ (j + 1))⁻¹
  let y : ℝ := Q ^ (j - 1)
  let mass : ℝ := ∫ r in Set.Ioi (0 : ℝ), w r
  let R₁ : ℝ := (q : ℝ) ^ (j - 1) * (∫ u : ℝ, f u) *
    (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
      iteratedDeriv j (dfiWeightQuotient w) r)
  let R₂ : ℝ := (q : ℝ) ^ (j - 1) *
    (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
      ∫ u : ℝ, w u * (u ^ j * iteratedDeriv j f (r * u)))
  let E : ℝ := p * x * A + p * y * B
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => abs_nonneg _
  have hp : 0 ≤ p := pow_nonneg (Nat.cast_nonneg q) _
  have hx : 0 ≤ x := inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)
  have hy : 0 ≤ y := pow_nonneg w.Q_pos.le _
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpone : (1 : ℝ) ≤ p := by
    dsimp [p]
    exact one_le_pow₀ hqone
  have hxleone : x ≤ 1 := by
    dsimp [x]
    exact (inv_le_one₀ (pow_pos w.Q_pos _)).2 (one_le_pow₀ w.one_le_Q)
  have honeley : (1 : ℝ) ≤ y := by
    dsimp [y]
    exact one_le_pow₀ w.one_le_Q
  have hxley : x ≤ y := hxleone.trans honeley
  have hxlepx : x ≤ p * x := le_mul_of_one_le_left hx hpone
  have hxlepy : x ≤ p * y :=
    hxley.trans (le_mul_of_one_le_left hy hpone)
  have hmassScale : x * (A + B) ≤ E := by
    calc
      x * (A + B) = x * A + x * B := by ring
      _ ≤ (p * x) * A + (p * y) * B :=
        add_le_add (mul_le_mul_of_nonneg_right hxlepx hA)
          (mul_le_mul_of_nonneg_right hxlepy hB)
      _ = E := by rfl
  have hpoint := dfiEquation17 f hf hfc U hsupp (show 1 ≤ j by omega)
  have hpoint' : |f 0| ≤ Cpoint * (A + B) := by
    simpa [Cpoint, A, B] using hpoint
  have hmass' : |mass - 1| ≤ Cmass * x := by
    simpa [mass, x] using hmass
  have hmassTerm : |f 0 * (mass - 1)| ≤ (Cmass * Cpoint) * E := by
    rw [abs_mul]
    calc
      |f 0| * |mass - 1| ≤ (Cpoint * (A + B)) * (Cmass * x) :=
        mul_le_mul hpoint' hmass' (abs_nonneg _) (by positivity)
      _ = (Cmass * Cpoint) * (x * (A + B)) := by ring
      _ ≤ (Cmass * Cpoint) * E :=
        mul_le_mul_of_nonneg_left hmassScale (by positivity)
  have habsInt : |∫ u : ℝ, f u| ≤ A := by
    dsimp [A]
    exact MeasureTheory.abs_integral_le_integral_abs
  have hfirst' : |R₁| ≤ Cfirst * (p * x * A) := by
    calc
      |R₁| ≤ Cfirst * p * x * |∫ u : ℝ, f u| := by
        simpa [R₁, p, x] using hfirst
      _ ≤ Cfirst * p * x * A :=
        mul_le_mul_of_nonneg_left habsInt (by positivity)
      _ = Cfirst * (p * x * A) := by ring
  have hsecond' : |R₂| ≤ Csecond * (p * y * B) := by
    calc
      |R₂| ≤ Csecond * p * y * B := by
        simpa [R₂, p, y, B] using hsecond
      _ = Csecond * (p * y * B) := by ring
  have hfirstE : |R₁| ≤ Cfirst * E := by
    exact hfirst'.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (by positivity)) hCfirst.le)
  have hsecondE : |R₂| ≤ Csecond * E := by
    exact hsecond'.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (by positivity)) hCsecond.le)
  have houter := dfiEquation12_outer w q hq f hf hfc U hsupp j hj
  have hfirstInt := (integrableOn_dfi_first_remainder w q j hj).const_mul
    (∫ u : ℝ, f u)
  have hsecondInt := integrableOn_dfi_second_remainder
    w f hf U hsupp q j hj
  have hpack :
      (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
          ((∫ u : ℝ, f u) * iteratedDeriv j (dfiWeightQuotient w) r -
            ∫ u : ℝ, w u * (u ^ j * iteratedDeriv j f (r * u)))) =
        (∫ u : ℝ, f u) *
            (∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
              iteratedDeriv j (dfiWeightQuotient w) r) -
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            ∫ u : ℝ, w u * (u ^ j * iteratedDeriv j f (r * u)) := by
    calc
      _ = ∫ r in Set.Ioi (0 : ℝ),
          (∫ u : ℝ, f u) *
              (dfiPsi j (r / q) *
                iteratedDeriv j (dfiWeightQuotient w) r) -
            dfiPsi j (r / q) *
              (∫ u : ℝ, w u *
                (u ^ j * iteratedDeriv j f (r * u))) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro r _
          ring
      _ = (∫ r in Set.Ioi (0 : ℝ),
            (∫ u : ℝ, f u) *
              (dfiPsi j (r / q) *
                iteratedDeriv j (dfiWeightQuotient w) r)) -
          ∫ r in Set.Ioi (0 : ℝ), dfiPsi j (r / q) *
            (∫ u : ℝ, w u *
              (u ^ j * iteratedDeriv j f (r * u))) := by
          exact MeasureTheory.integral_sub hfirstInt hsecondInt
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hdecomp :
      dfiEquation12Left w q f - f 0 =
        f 0 * (mass - 1) + (-1 : ℝ) ^ (j + 1) * R₁ -
          (-1 : ℝ) ^ (j + 1) * R₂ := by
    rw [houter, hpack]
    dsimp [mass, R₁, R₂]
    ring
  rw [hdecomp]
  have htriangle :
      |f 0 * (mass - 1) + (-1 : ℝ) ^ (j + 1) * R₁ -
          (-1 : ℝ) ^ (j + 1) * R₂| ≤
        |f 0 * (mass - 1)| + |R₁| + |R₂| := by
    calc
      _ ≤ |f 0 * (mass - 1) + (-1 : ℝ) ^ (j + 1) * R₁| +
          |-((-1 : ℝ) ^ (j + 1) * R₂)| := by
        simpa [sub_eq_add_neg] using abs_add_le
          (f 0 * (mass - 1) + (-1 : ℝ) ^ (j + 1) * R₁)
          (-((-1 : ℝ) ^ (j + 1) * R₂))
      _ ≤ (|f 0 * (mass - 1)| +
          |(-1 : ℝ) ^ (j + 1) * R₁|) +
          |-((-1 : ℝ) ^ (j + 1) * R₂)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = |f 0 * (mass - 1)| + |R₁| + |R₂| := by simp
  calc
    _ ≤ |f 0 * (mass - 1)| + |R₁| + |R₂| := htriangle
    _ ≤ (Cmass * Cpoint) * E + Cfirst * E + Csecond * E :=
      add_le_add (add_le_add hmassTerm hfirstE) hsecondE
    _ = C * E := by dsimp [C]; ring
    _ = C * (p * x * A + p * y * B) := rfl
    _ = _ := by rfl

end RiemannZeta.GuthMaynard
