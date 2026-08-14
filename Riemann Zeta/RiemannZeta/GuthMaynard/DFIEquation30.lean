import RiemannZeta.GuthMaynard.DFIEquation27
import RiemannZeta.GuthMaynard.DFIEquation28
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DFI equation (30): absolute kernel integrals

This file proves the logarithmic `L¹` estimate used twice in the DFI
argument: first to control the tail of the main series in equation (27), and
then to estimate the four dual Voronoi branches after equation (29).
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-- Exact elementary integral behind DFI equation (30). -/
theorem intervalIntegral_inv_add_eq_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in 0..U, (A + u)⁻¹) = Real.log ((A + U) / A) := by
  have hadd : (fun u : ℝ => (A + u)⁻¹) = fun u => (u + A)⁻¹ := by
    funext u
    rw [add_comm A u]
  rw [hadd]
  rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹) A]
  simpa [add_comm] using
    (integral_inv_of_pos hA (by positivity : 0 < U + A))

/-- The even reciprocal majorant has the exact logarithmic integral on a
symmetric interval. -/
theorem intervalIntegral_inv_add_abs_eq_two_mul_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in -U..U, (A + |u|)⁻¹) =
      2 * Real.log ((A + U) / A) := by
  have hcont : Continuous (fun u : ℝ => (A + |u|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg hA (abs_nonneg u)))
  have hleftInt : IntervalIntegrable (fun u : ℝ => (A + |u|)⁻¹)
      volume (-U) 0 := hcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable (fun u : ℝ => (A + |u|)⁻¹)
      volume 0 U := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
  have hneg : (∫ u : ℝ in -U..0, (A + |u|)⁻¹) =
      ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
    calc
      (∫ u : ℝ in -U..0, (A + |u|)⁻¹) =
          ∫ u : ℝ in 0..U, (A + |-u|)⁻¹ := by
        simpa using (intervalIntegral.integral_comp_neg
          (f := fun u : ℝ => (A + |u|)⁻¹) (a := 0) (b := U)).symm
      _ = ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp only [abs_neg]
        rw [abs_of_nonneg]
        exact (Set.uIcc_of_le hU ▸ hu).1
  rw [hneg]
  have hpos : (∫ u : ℝ in 0..U, (A + |u|)⁻¹) =
      ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only
    rw [abs_of_nonneg]
    exact (Set.uIcc_of_le hU ▸ hu).1
  rw [hpos, intervalIntegral_inv_add_eq_log_div hA hU]
  ring

/-- Set-integral form of the exact symmetric logarithmic integral. -/
theorem setIntegral_Icc_inv_add_abs_eq_two_mul_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in Set.Icc (-U) U, (A + |u|)⁻¹) =
      2 * Real.log ((A + U) / A) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  exact intervalIntegral_inv_add_abs_eq_two_mul_log_div hA hU

/-- Integrated form of the pointwise DFI equation-(19) estimate. -/
theorem integral_abs_dfiDeltaKernel_Icc_le
    {Q U : ℝ} (w : DFIDeltaWeight Q) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        K * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
  obtain ⟨K, hK, hpoint⟩ := dfiEquation19 w
  refine ⟨K, hK, ?_⟩
  intro q hq
  have hqQ : 0 < (q : ℝ) * Q := mul_pos (by exact_mod_cast hq) w.Q_pos
  have hconst : IntegrableOn (fun _ : ℝ =>
      (((q : ℝ) * Q + Q ^ 2)⁻¹)) (Set.Icc (-U) U) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hinv : Continuous (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) :=
    (continuous_const.add continuous_abs).inv₀
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg hqQ (abs_nonneg u)))
  have hinvInt : IntegrableOn (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) (Set.Icc (-U) U) :=
    hinv.continuousOn.integrableOn_compact isCompact_Icc
  have hkernel : IntegrableOn (fun u : ℝ => |dfiDeltaKernel w q u|)
      (Set.Icc (-U) U) :=
    (contDiff_dfiDeltaKernel w q hq).continuous.abs.continuousOn
      |>.integrableOn_compact isCompact_Icc
  calc
    (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        ∫ u : ℝ in Set.Icc (-U) U,
          K * ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
            (((q : ℝ) * Q + |u|)⁻¹)) := by
      apply integral_mono hkernel ((hconst.add hinvInt).const_mul K)
      intro u
      exact hpoint q hq u
    _ = K * ((∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) +
        ∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + |u|)⁻¹)) := by
      rw [← integral_add hconst hinvInt, integral_const_mul]
    _ = K * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
      rw [setIntegral_Icc_inv_add_abs_eq_two_mul_log_div hqQ hU]
      have hconstEval : (∫ _u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) =
          2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ U - -U)]
        ring
      rw [hconstEval]

/-- With the source choice `U = Q²`, equation (19) integrates to the
logarithmic kernel bound used in DFI equation (30). -/
theorem integral_abs_dfiDeltaKernel_Icc_le_log
    {Q U : ℝ} (w : DFIDeltaWeight Q)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        K * Real.log Q := by
  have hUnonneg : 0 ≤ U := by rw [hU]; positivity
  obtain ⟨K₀, hK₀, hraw⟩ :=
    integral_abs_dfiDeltaKernel_Icc_le w hUnonneg
  let A : ℝ := 2 / Real.log 2 + 4
  have hA : 0 < A := by dsimp [A]; positivity
  let K := K₀ * A
  have hK : 0 < K := mul_pos hK₀ hA
  refine ⟨K, hK, ?_⟩
  intro q hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hqpos hQpos
  have hQsq : 0 < Q ^ 2 := by positivity
  have hfirst : 2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ 2 := by
    rw [hU]
    have hinv : (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (Q ^ 2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) hQsq).2
      nlinarith [hqQ]
    calc
      2 * Q ^ 2 * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤
          2 * Q ^ 2 * (Q ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 := by field_simp [ne_of_gt hQsq]
  have hratioEq : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) =
      1 + Q / (q : ℝ) := by
    rw [hU]
    field_simp [ne_of_gt hqQ, show (q : ℝ) ≠ 0 by positivity]
  have hQdiv : Q / (q : ℝ) ≤ Q :=
    div_le_self (by positivity) hqR
  have hratioPos : 0 < (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) := by
    rw [hratioEq]
    positivity
  have hratio : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤ Q ^ 2 := by
    rw [hratioEq]
    nlinarith
  have hlogratio : Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
      2 * Real.log Q := by
    calc
      Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
          Real.log (Q ^ 2) := Real.log_le_log hratioPos hratio
      _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num
  have hexpr :
      2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q))) ≤
        2 + 4 * Real.log Q := by nlinarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log Q :=
    Real.log_le_log (by norm_num) hQ
  have htwo : 2 ≤ (2 / Real.log 2) * Real.log Q := by
    calc
      2 = (2 / Real.log 2) * Real.log 2 := by field_simp [hlogTwo.ne']
      _ ≤ (2 / Real.log 2) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlogMono (by positivity)
  have habsorb : 2 + 4 * Real.log Q ≤ A * Real.log Q := by
    dsimp [A]
    nlinarith
  exact (hraw q hq).trans (by
    calc
      K₀ * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) ≤
          K₀ * (2 + 4 * Real.log Q) :=
        mul_le_mul_of_nonneg_left hexpr hK₀.le
      _ ≤ K₀ * (A * Real.log Q) :=
        mul_le_mul_of_nonneg_left habsorb hK₀.le
      _ = K * Real.log Q := by simp [K]; ring)

/-- The equation-(30) kernel after restriction to the displacement interval
forced by the redundant cutoff. -/
noncomputable def dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U u : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-U) U) (fun v => |dfiDeltaKernel w q v|) u

theorem integrable_dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (U : ℝ) :
    Integrable (dfiEquation30TruncatedKernel w q U) := by
  unfold dfiEquation30TruncatedKernel
  exact ((contDiff_dfiDeltaKernel w q hq).continuous.abs.continuousOn
    |>.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc

theorem integral_dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U : ℝ) :
    (∫ u : ℝ, dfiEquation30TruncatedKernel w q U u) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  change (∫ u : ℝ, Set.indicator (Set.Icc (-U) U)
    (fun v => |dfiDeltaKernel w q v|) u) = _
  exact integral_indicator measurableSet_Icc

/-- Translation and reflection preserve the truncated kernel integral.  This
is the exact affine change `u = x-y-h` used in DFI equation (30). -/
theorem integral_dfiEquation30TruncatedKernel_affine
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U x h : ℝ) :
    (∫ y : ℝ, dfiEquation30TruncatedKernel w q U (x - y - h)) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  let G := dfiEquation30TruncatedKernel w q U
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := volume) (fun y : ℝ => G (-y)) (h - x)
  have hneg := MeasureTheory.integral_neg_eq_self G volume
  calc
    (∫ y : ℝ, G (x - y - h)) =
        ∫ y : ℝ, G (-(y + (h - x))) := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 1
      ring
    _ = ∫ y : ℝ, G (-y) := hshift
    _ = ∫ y : ℝ, G y := hneg
    _ = ∫ u : ℝ in Set.Icc (-U) U,
        |dfiDeltaKernel w q u| := integral_dfiEquation30TruncatedKernel w q U

theorem integrable_dfiEquation30TruncatedKernel_affine
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U x h : ℝ) :
    Integrable (fun y : ℝ =>
      dfiEquation30TruncatedKernel w q U (x - y - h)) := by
  let G := dfiEquation30TruncatedKernel w q U
  have hG : Integrable G := integrable_dfiEquation30TruncatedKernel w q hq U
  have hcomp : Integrable (fun y : ℝ => G (-(y + (h - x)))) :=
    hG.comp_neg.comp_add_right (h - x)
  simpa only [G, show ∀ y : ℝ, -(y + (h - x)) = x - y - h by
    intro y
    ring] using hcomp

theorem integral_dfiEquation30TruncatedKernel_translate
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U y h : ℝ) :
    (∫ x : ℝ, dfiEquation30TruncatedKernel w q U (x - y - h)) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  let G := dfiEquation30TruncatedKernel w q U
  calc
    (∫ x : ℝ, G (x - y - h)) = ∫ x : ℝ, G (x + (-y - h)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      ring
    _ = ∫ x : ℝ, G x :=
      MeasureTheory.integral_add_right_eq_self (μ := volume) G (-y - h)
    _ = ∫ u : ℝ in Set.Icc (-U) U,
        |dfiDeltaKernel w q u| := integral_dfiEquation30TruncatedKernel w q U

theorem integrable_dfiEquation30TruncatedKernel_translate
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U y h : ℝ) :
    Integrable (fun x : ℝ =>
      dfiEquation30TruncatedKernel w q U (x - y - h)) := by
  let G := dfiEquation30TruncatedKernel w q U
  have hG : Integrable G := integrable_dfiEquation30TruncatedKernel w q hq U
  have hcomp : Integrable (fun x : ℝ => G (x + (-y - h))) :=
    hG.comp_add_right (-y - h)
  simpa only [G, show ∀ x : ℝ, x + (-y - h) = x - y - h by
    intro x
    ring] using hcomp

/-- The nonnegative physical-variable double integral denoted `||I||` in
DFI equation (30), before the two divisor-variable Jacobians are restored. -/
noncomputable def dfiEquation30PhysicalAbsoluteIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (F : ℝ → ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ x : ℝ, ∫ y : ℝ,
    ‖F x y‖ * |dfiDeltaKernel w q (x - y - h)|

/-- The `X`-length half of the source estimate in DFI equation (30).  All
smoothness, support and size hypotheses are discharged from equations (2)
and (21); the only constant is the legitimate order-zero source constant. -/
theorem dfiEquation30_physical_le_X
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        X * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨C, hC, hbound⟩ := dfiEquation21 hf hbox hφ hscale h 0 0
  refine ⟨C, hC, ?_⟩
  intro q hq
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖dfiLocalizedWeight f φ h p.1 p.2‖ *
      |dfiDeltaKernel w q (p.1 - p.2 - h)|
  have hHcont : Continuous H := by
    dsimp [H]
    exact (contDiff_uncurry_dfiLocalizedWeight (h := h) hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
  have hHcompact : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hHint : Integrable H (volume.prod volume) :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have houter : Integrable (fun x : ℝ => ∫ y : ℝ, H (x, y)) :=
    hHint.integral_prod_left
  let D : ℝ := ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|
  let R : ℝ → ℝ := Set.indicator (Set.Icc X (2 * X)) (fun _ => C * D)
  have hRint : Integrable R := by
    dsimp [R]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hinner (x : ℝ) : (∫ y : ℝ, H (x, y)) ≤ R x := by
    change (∫ y : ℝ, H (x, y)) ≤ R x
    by_cases hx : x ∈ Set.Icc X (2 * X)
    · simp only [R, Set.indicator_of_mem hx]
      have hsliceCont : Continuous (fun y : ℝ => H (x, y)) :=
        hHcont.comp (by fun_prop)
      have hsliceSupport : Function.support (fun y : ℝ => H (x, y)) ⊆
          Set.Icc Y (2 * Y) := by
        intro y hy
        exact (hHsupport hy).2
      have hsliceInt : Integrable (fun y : ℝ => H (x, y)) :=
        hsliceCont.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact
            isCompact_Icc hsliceSupport)
      have hmajorInt : Integrable (fun y : ℝ =>
          C * dfiEquation30TruncatedKernel w q U (x - y - h)) :=
        (integrable_dfiEquation30TruncatedKernel_affine w q hq U x h).const_mul C
      calc
        (∫ y : ℝ, H (x, y)) ≤
            ∫ y : ℝ, C * dfiEquation30TruncatedKernel w q U (x - y - h) := by
          apply integral_mono hsliceInt hmajorInt
          intro y
          change H (x, y) ≤
            C * dfiEquation30TruncatedKernel w q U (x - y - h)
          by_cases hlocal : dfiLocalizedWeight f φ h x y = 0
          · have hHxy : H (x, y) = 0 := by simp [H, hlocal]
            rw [hHxy]
            exact mul_nonneg hC.le (by
              unfold dfiEquation30TruncatedKernel
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hφne : φ (x - y - h) ≠ 0 := by
              intro hz
              exact hlocal (by simp only [dfiLocalizedWeight, hz, mul_zero])
            have hu : x - y - h ∈ Set.Icc (-U) U :=
              Set.Ioo_subset_Icc_self (hφ.support_subset hφne)
            change ‖dfiLocalizedWeight f φ h x y‖ *
                |dfiDeltaKernel w q (x - y - h)| ≤
              C * Set.indicator (Set.Icc (-U) U)
                (fun v => |dfiDeltaKernel w q v|) (x - y - h)
            rw [Set.indicator_of_mem hu]
            have hb := (hbound x y).1
            simp only [dfiMixedDeriv_zero_zero, pow_zero, mul_one] at hb
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = C * D := by
          rw [integral_const_mul,
            integral_dfiEquation30TruncatedKernel_affine w q U x h]
    · have hRx : R x = 0 := by simp [R, hx]
      rw [hRx]
      have hzero : (fun y : ℝ => H (x, y)) = 0 := by
        funext y
        have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support
              (Function.uncurry (dfiLocalizedWeight f φ h)) := hne
          exact hx (support_uncurry_dfiLocalizedWeight_subset hbox hp).1
        simp [H, hlocal]
      rw [hzero]
      simp
  change (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ X * C * D
  calc
    (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ ∫ x : ℝ, R x :=
      integral_mono houter hRint hinner
    _ = X * C * D := by
      dsimp [R]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        smul_eq_mul, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal]
      · ring
      · nlinarith [hf.one_le_X]

/-- The symmetric `Y`-length half of DFI equation (30). -/
theorem dfiEquation30_physical_le_Y
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨C, hC, hbound⟩ := dfiEquation21 hf hbox hφ hscale h 0 0
  refine ⟨C, hC, ?_⟩
  intro q hq
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖dfiLocalizedWeight f φ h p.1 p.2‖ *
      |dfiDeltaKernel w q (p.1 - p.2 - h)|
  have hHcont : Continuous H := by
    dsimp [H]
    exact (contDiff_uncurry_dfiLocalizedWeight (h := h) hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
  have hHcompact : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hHint : Integrable H (volume.prod volume) :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have houter : Integrable (fun y : ℝ => ∫ x : ℝ, H (x, y)) :=
    hHint.integral_prod_right
  let D : ℝ := ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|
  let R : ℝ → ℝ := Set.indicator (Set.Icc Y (2 * Y)) (fun _ => C * D)
  have hRint : Integrable R := by
    dsimp [R]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hinner (y : ℝ) : (∫ x : ℝ, H (x, y)) ≤ R y := by
    by_cases hy : y ∈ Set.Icc Y (2 * Y)
    · simp only [R, Set.indicator_of_mem hy]
      have hsliceCont : Continuous (fun x : ℝ => H (x, y)) :=
        hHcont.comp (by fun_prop)
      have hsliceSupport : Function.support (fun x : ℝ => H (x, y)) ⊆
          Set.Icc X (2 * X) := by
        intro x hx
        exact (hHsupport hx).1
      have hsliceInt : Integrable (fun x : ℝ => H (x, y)) :=
        hsliceCont.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact
            isCompact_Icc hsliceSupport)
      have hmajorInt : Integrable (fun x : ℝ =>
          C * dfiEquation30TruncatedKernel w q U (x - y - h)) :=
        (integrable_dfiEquation30TruncatedKernel_translate w q hq U y h).const_mul C
      calc
        (∫ x : ℝ, H (x, y)) ≤
            ∫ x : ℝ, C * dfiEquation30TruncatedKernel w q U (x - y - h) := by
          apply integral_mono hsliceInt hmajorInt
          intro x
          change H (x, y) ≤
            C * dfiEquation30TruncatedKernel w q U (x - y - h)
          by_cases hlocal : dfiLocalizedWeight f φ h x y = 0
          · have hHxy : H (x, y) = 0 := by simp [H, hlocal]
            rw [hHxy]
            exact mul_nonneg hC.le (by
              unfold dfiEquation30TruncatedKernel
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hφne : φ (x - y - h) ≠ 0 := by
              intro hz
              exact hlocal (by simp only [dfiLocalizedWeight, hz, mul_zero])
            have hu : x - y - h ∈ Set.Icc (-U) U :=
              Set.Ioo_subset_Icc_self (hφ.support_subset hφne)
            change ‖dfiLocalizedWeight f φ h x y‖ *
                |dfiDeltaKernel w q (x - y - h)| ≤
              C * Set.indicator (Set.Icc (-U) U)
                (fun v => |dfiDeltaKernel w q v|) (x - y - h)
            rw [Set.indicator_of_mem hu]
            have hb := (hbound x y).1
            simp only [dfiMixedDeriv_zero_zero, pow_zero, mul_one] at hb
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = C * D := by
          rw [integral_const_mul,
            integral_dfiEquation30TruncatedKernel_translate w q U y h]
    · have hRy : R y = 0 := by simp [R, hy]
      rw [hRy]
      have hzero : (fun x : ℝ => H (x, y)) = 0 := by
        funext x
        have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support
              (Function.uncurry (dfiLocalizedWeight f φ h)) := hne
          exact hy (support_uncurry_dfiLocalizedWeight_subset hbox hp).2
        simp [H, hlocal]
      rw [hzero]
      simp
  change (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ Y * C * D
  rw [integral_integral_swap hHint]
  calc
    (∫ y : ℝ, ∫ x : ℝ, H (x, y)) ≤ ∫ y : ℝ, R y :=
      integral_mono houter hRint hinner
    _ = Y * C * D := by
      dsimp [R]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        smul_eq_mul, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal]
      · ring
      · nlinarith [hf.one_le_Y]

/-- The literal `min(X,Y)` physical estimate displayed in DFI equation
(30), still retaining the exact truncated delta-kernel integral. -/
theorem dfiEquation30_physical_le_min
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        min X Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨CX, hCX, hXbound⟩ :=
    dfiEquation30_physical_le_X w hf hbox hφ hscale
  obtain ⟨CY, hCY, hYbound⟩ :=
    dfiEquation30_physical_le_Y w hf hbox hφ hscale
  let C := max CX CY
  have hC : 0 < C := hCX.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hXbound := hXbound q hq
  have hYbound := hYbound q hq
  have hD : 0 ≤ (∫ u : ℝ in Set.Icc (-U) U,
      |dfiDeltaKernel w q u|) := integral_nonneg (fun _ => abs_nonneg _)
  rcases le_total X Y with hXY | hYX
  · rw [min_eq_left hXY]
    exact hXbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left CX CY)
        (zero_le_one.trans hf.one_le_X)) hD)
  · rw [min_eq_right hYX]
    exact hYbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right CX CY)
        (zero_le_one.trans hf.one_le_Y)) hD)

/-- DFI equation (30) in its published logarithmic physical-variable form,
for the source choice `U = Q²`. -/
theorem dfiEquation30_physical_log_bound
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        K * min X Y * Real.log Q := by
  obtain ⟨C, hC, hphysical⟩ :=
    dfiEquation30_physical_le_min w hf hbox hφ hscale
  obtain ⟨K₀, hK₀, hkernelAll⟩ :=
    integral_abs_dfiDeltaKernel_Icc_le_log w hQ hU
  let K := C * K₀
  have hK : 0 < K := mul_pos hC hK₀
  refine ⟨K, hK, ?_⟩
  intro q hq
  have hkernel := hkernelAll q hq
  exact (hphysical q hq).trans (by
    have hmin : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    calc
      min X Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) ≤
          min X Y * C * (K₀ * Real.log Q) :=
        mul_le_mul_of_nonneg_left hkernel (mul_nonneg hmin hC.le)
      _ = K * min X Y * Real.log Q := by simp [K]; ring)

/-- The divisor-variable integral `||I||` of DFI equation (30), including
the two positive scaling Jacobians. -/
noncomputable def dfiEquation30DivisorAbsoluteIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q a b : ℕ)
    (F : ℝ → ℝ → ℂ) (h : ℝ) : ℝ :=
  ((a : ℝ) * b)⁻¹ * dfiEquation30PhysicalAbsoluteIntegral w q F h

/-- Literal source equation (30):
`||I|| ≪ (ab)⁻¹ min(X,Y) log Q`. -/
theorem dfiEquation30
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
  obtain ⟨K, hK, hphysical⟩ :=
    dfiEquation30_physical_log_bound w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro q hq
  unfold dfiEquation30DivisorAbsoluteIntegral
  have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
  calc
    ((a : ℝ) * b)⁻¹ *
        dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
      ((a : ℝ) * b)⁻¹ * (K * min X Y * Real.log Q) :=
        mul_le_mul_of_nonneg_left (hphysical q hq) hab
    _ = K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by ring

end RiemannZeta.GuthMaynard
