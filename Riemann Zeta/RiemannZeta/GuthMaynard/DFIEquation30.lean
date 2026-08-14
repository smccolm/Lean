import RiemannZeta.GuthMaynard.DFIEquation27
import RiemannZeta.GuthMaynard.DFIEquation22Source
import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.DFIEquation29
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

/-- The logarithmic double-main integral occurring in DFI equation (27) is
bounded by the equation-(30) physical mass.  This is the missing norm bridge
between the raw localized weight and the actual two Voronoi main terms. -/
theorem exists_norm_dfiEquation27PhysicalMainIntegral_le
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b q : ℕ), 0 < q → ∀ qx qy : ℕ,
      ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          min X Y * Real.log Q := by
  obtain ⟨K₀, hK₀, hphysical⟩ :=
    dfiEquation30_physical_log_bound w hf hbox hφ hscale hQ hU
  refine ⟨K₀, hK₀, ?_⟩
  intro a b q hq qx qy
  let F : ℝ → ℝ → ℂ := dfiLocalizedWeight f φ h
  let G : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy F p.1 p.2 *
      (dfiDeltaKernel w q (p.1 - p.2 - h) : ℂ)
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖F p.1 p.2‖ * |dfiDeltaKernel w q (p.1 - p.2 - h)|
  let LX : ℝ := Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  let LY : ℝ := Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  let B : ℝ := LX * LY
  have hLX : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hB : 0 ≤ B := mul_nonneg hLX hLY
  have hGsmooth : Continuous G := by
    dsimp [G, F]
    exact (contDiff_uncurry_dfiEquation27C_source hf hbox hφ a b qx qy).continuous.mul
      (Complex.ofRealCLM.continuous.comp
        ((contDiff_dfiDeltaKernel w q hq).continuous.comp (by fun_prop)))
  have hGsupport : Function.support G ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFne : F p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [G, dfiEquation27C, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hFne
  have hGint : Integrable G (volume.prod volume) :=
    hGsmooth.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) hGsupport)
  have hHsmooth : Continuous H := by
    dsimp [H, F]
    exact (contDiff_uncurry_dfiLocalizedWeight hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFne : F p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hFne
  have hHint : Integrable H (volume.prod volume) :=
    hHsmooth.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) hHsupport)
  have hpoint (p : ℝ × ℝ) : ‖G p‖ ≤ B * H p := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hFzero : F p.1 p.2 = 0
    · simp [H, dfiEquation27C, hFzero]
    · have hxy : (p.1, p.2) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        support_uncurry_dfiLocalizedWeight_subset hbox hFzero
      have hxlog :=
        abs_log_le_log_two_mul_of_mem_Icc hf.one_le_X hxy.1
      have hylog :=
        abs_log_le_log_two_mul_of_mem_Icc hf.one_le_Y hxy.2
      have hcb := norm_dfiEquation27C_le a b qx qy F p.1 p.2
      have hCtoB :
          ‖dfiEquation27C a b qx qy F p.1 p.2‖ ≤
            B * ‖F p.1 p.2‖ := by
        dsimp [B, LX, LY]
        calc
          ‖dfiEquation27C a b qx qy F p.1 p.2‖ ≤
              (|Real.log p.1| + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (|Real.log p.2| + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                ‖F p.1 p.2‖ := hcb
          _ ≤ (Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                ‖F p.1 p.2‖ := by gcongr
      simpa [H, mul_assoc] using
        mul_le_mul_of_nonneg_right hCtoB
          (abs_nonneg (dfiDeltaKernel w q (p.1 - p.2 - h)))
  have hproduct :
      ‖∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
          ∂(volume.prod volume)‖ ≤
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume) := by
    exact MeasureTheory.norm_integral_le_of_norm_le
      ((hHint.const_mul B).integrableOn)
      (Filter.Eventually.of_forall hpoint)
  have hnonneg (p : ℝ × ℝ) : 0 ≤ B * H p := by
    exact mul_nonneg hB (mul_nonneg (norm_nonneg _) (abs_nonneg _))
  have hwhole :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume)) ≤
        ∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume) :=
    MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hnonneg) (hHint.const_mul B)
  have hmainRewrite :
      dfiEquation27PhysicalMainIntegral w q a b qx qy F h =
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
          ∂(volume.prod volume) := by
    unfold dfiEquation27PhysicalMainIntegral
    exact (MeasureTheory.setIntegral_prod G hGint.integrableOn).symm
  have hmassRewrite :
      (∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume)) =
        B * dfiEquation30PhysicalAbsoluteIntegral w q F h := by
    rw [MeasureTheory.integral_const_mul]
    unfold dfiEquation30PhysicalAbsoluteIntegral
    rw [MeasureTheory.integral_prod H hHint]
  rw [hmainRewrite]
  calc
    ‖∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
        ∂(volume.prod volume)‖ ≤
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume) := hproduct
    _ ≤ ∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume) := hwhole
    _ = B * dfiEquation30PhysicalAbsoluteIntegral w q F h := hmassRewrite
    _ ≤ B * (K₀ * min X Y * Real.log Q) :=
      mul_le_mul_of_nonneg_left (hphysical q hq) hB
    _ = K₀ * LX * LY * min X Y * Real.log Q := by
      dsimp [B]
      ring

/-- Uniform equation-(27) physical-main bound after substituting the two
reduced Voronoi denominators.  For every retained delta modulus `q ≤ 2Q`,
both reduced logarithms are absorbed into `log (2Q)`. -/
theorem exists_norm_dfiEquation27PhysicalMainIntegral_reduced_le
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b q : ℕ), 0 < q → (q : ℝ) ≤ 2 * Q →
      ‖dfiEquation27PhysicalMainIntegral w q a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          min X Y * Real.log Q := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_norm_dfiEquation27PhysicalMainIntegral_le
      w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro a b q hq hqQ
  have hqlog : Real.log (q : ℝ) ≤ Real.log (2 * Q) := by
    exact Real.log_le_log (by exact_mod_cast hq) hqQ
  have hqa := abs_log_dfiReducedDenominator_le a q hq
  have hqb := abs_log_dfiReducedDenominator_le b q hq
  have hlogQ : 0 ≤ Real.log Q :=
    Real.log_nonneg (by linarith)
  have hmin : 0 ≤ min X Y := by
    exact le_min (zero_le_one.trans hf.one_le_X)
      (zero_le_one.trans hf.one_le_Y)
  have hLX : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator b q : ℝ)| := by
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  refine (hmain a b q hq
    (dfiReducedDenominator a q) (dfiReducedDenominator b q)).trans ?_
  have hqaQ :
      |Real.log (dfiReducedDenominator a q : ℝ)| ≤ Real.log (2 * Q) :=
    hqa.trans hqlog
  have hqbQ :
      |Real.log (dfiReducedDenominator b q : ℝ)| ≤ Real.log (2 * Q) :=
    hqb.trans hqlog
  have hlog2Q : 0 ≤ Real.log (2 * Q) :=
    Real.log_nonneg (by nlinarith)
  have hLXQ : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLYQ : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  gcongr

/-- The central integral in equation (27), with the reduced Voronoi
denominators substituted, has the same logarithmic envelope as the physical
main integral but no delta-kernel loss.  Both dyadic support projections are
used, giving the sharp factor `min X Y`. -/
theorem exists_norm_dfiEquation27CentralIntegral_reduced_le
    {P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          min X Y := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
      hf hbox hφ hscale 0
  let K : ℝ := C * dfiEquation27LogLeibnizConstant 0
  have hK : 0 < K :=
    mul_pos hC (dfiEquation27LogLeibnizConstant_pos 0)
  refine ⟨K, hK, ?_⟩
  intro a b q hq
  let g : ℝ → ℂ := fun x =>
    dfiEquation27SourceSliceFamily a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) h x 0
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log q
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log q
  let B : ℝ := K * LX * LY
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hLX : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hB : 0 ≤ B := by positivity
  have hgInt : Integrable g := by
    simpa only [g] using integrable_dfiEquation27_source_center
      hf hbox hφ a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)
  have hgContinuous : Continuous g := by
    have hcenterCD := (contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h)
      hf hbox hφ a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)).comp (contDiff_prodMk_left (0 : ℝ))
    simpa only [g, Function.comp_apply, Function.uncurry_apply_pair] using
      hcenterCD.continuous
  have hgCont : Continuous (fun x => ‖g x‖) := hgContinuous.norm
  have hgBound (x : ℝ) : |‖g x‖| ≤ B := by
    rw [abs_of_nonneg (norm_nonneg _)]
    have hp := hpoint h a b (dfiReducedDenominator a q)
      (dfiReducedDenominator b q) x 0
    have hqa := abs_log_dfiReducedDenominator_le a q hq
    have hqb := abs_log_dfiReducedDenominator_le b q hq
    have hLXred : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
      have : 0 ≤ Real.log (2 * X) :=
        Real.log_nonneg (by nlinarith [hf.one_le_X])
      positivity
    have hLYred : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator b q : ℝ)| := by
      have : 0 ≤ Real.log (2 * Y) :=
        Real.log_nonneg (by nlinarith [hf.one_le_Y])
      positivity
    dsimp [g, B, K, LX, LY]
    simp only [iteratedDeriv_zero, pow_zero, mul_one] at hp
    calc
      ‖dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x 0‖ ≤
          (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| +
                2 * |Real.log (dfiReducedDenominator a q : ℝ)|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| +
                2 * |Real.log (dfiReducedDenominator b q : ℝ)|) *
            C * dfiEquation27LogLeibnizConstant 0 := hp
      _ ≤ (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            C * dfiEquation27LogLeibnizConstant 0 := by
          gcongr
          exact (dfiEquation27LogLeibnizConstant_pos 0).le
      _ = (C * dfiEquation27LogLeibnizConstant 0) *
            (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) := by ring
  have hsuppX : Function.support (fun x => ‖g x‖) ⊆ Set.Icc X (2 * X) := by
    intro x hx
    exact support_dfiEquation27_source_center_subset
      (h := h) hbox a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q) (by simpa using hx)
  have hsuppY : Function.support (fun x => ‖g x‖) ⊆
      Set.Icc (Y + h) (2 * Y + h) := by
    intro x hx
    have hgx : g x ≠ 0 := by simpa using hx
    have hlocal : dfiLocalizedWeight f φ h x (x - h) ≠ 0 := by
      intro hz
      exact hgx (by simp [g, dfiEquation27SourceSliceFamily,
        dfiEquation27Slice, dfiEquation27C, hz])
    have hpMem : (x, x - h) ∈ Function.support
        (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
    have hp := support_uncurry_dfiLocalizedWeight_subset hbox hpMem
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hXbound : (∫ x : ℝ, ‖g x‖) ≤ X * B := by
    have h := integral_abs_le_interval_length_mul
      (fun x => ‖g x‖) hgCont
      (show X ≤ 2 * X by linarith [hf.one_le_X]) hsuppX hgBound
    calc
      (∫ x : ℝ, ‖g x‖) ≤ (2 * X - X) * B := by
        simpa [abs_of_nonneg, norm_nonneg] using h
      _ = X * B := by ring
  have hYbound : (∫ x : ℝ, ‖g x‖) ≤ Y * B := by
    have hraw := integral_abs_le_interval_length_mul
      (fun x => ‖g x‖) hgCont
      (show Y + h ≤ 2 * Y + h by linarith [hf.one_le_Y]) hsuppY hgBound
    calc
      (∫ x : ℝ, ‖g x‖) ≤ (2 * Y + h - (Y + h)) * B := by
        simpa [abs_of_nonneg, norm_nonneg] using hraw
      _ = Y * B := by ring
  have hnorm : ‖∫ x : ℝ, g x‖ ≤ ∫ x : ℝ, ‖g x‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  unfold dfiEquation27CentralIntegral
  have hfun : (fun x : ℝ =>
      dfiEquation27C a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q) (dfiLocalizedWeight f φ h) x (x - h)) =
      g := by
    funext x
    simp [g, dfiEquation27SourceSliceFamily, dfiEquation27Slice]
  rw [hfun]
  calc
    ‖∫ x : ℝ, g x‖ ≤ ∫ x : ℝ, ‖g x‖ := hnorm
    _ ≤ min (X * B) (Y * B) := le_min hXbound hYbound
    _ = min X Y * B := (min_mul_of_nonneg X Y hB).symm
    _ = K * LX * LY * min X Y := by ring

/-- The elementary comparison series used for the logarithmic equation-(27)
tail is a `p`-series of exponent `3/2`. -/
theorem summable_natCast_inv_sq_mul_rpow_half :
    Summable (fun q : ℕ =>
      (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))) := by
  have hsum : Summable (fun q : ℕ => (q : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  convert hsum using 1
  funext q
  by_cases hq : q = 0
  · simp [hq]
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    calc
      ((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ) =
          (q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ) := by
        congr 1
        calc
          ((q : ℝ) ^ 2)⁻¹ = ((q : ℝ) ^ (2 : ℝ))⁻¹ :=
            congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (q : ℝ) 2).symm
          _ = (q : ℝ) ^ (-(2 : ℝ)) :=
            (Real.rpow_neg hqpos.le (2 : ℝ)).symm
      _ = (q : ℝ) ^ (-(2 : ℝ) + (1 / 2 : ℝ)) := by
        rw [Real.rpow_add hqpos]
      _ = (q : ℝ) ^ (-(3 / 2 : ℝ)) := by norm_num

/-- The exact integrated summand of DFI equation (3)/(27), including the
external Jacobian `(ab)⁻¹`. -/
noncomputable def dfiEquation27CentralSummand
    (a b h : ℕ) (F : ℝ → ℝ → ℂ) (q : ℕ) : ℂ :=
  (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) F h

/-- DFI's infinite Ramanujan main term after integration against the source
test function.  Absolute summability is proved below. -/
noncomputable def dfiEquation27CentralSeries
    (a b h : ℕ) (F : ℝ → ℝ → ℂ) : ℂ :=
  ∑' q : ℕ, dfiEquation27CentralSummand a b h F q

/-- Absolute convergence of the literal equation-(27) central series.  The
two logarithms cost only `q^(1/2)`, leaving the summable exponent `-3/2`
after the inverse-square arithmetic coefficient. -/
theorem summable_dfiEquation27CentralSummand
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b h
        (dfiLocalizedWeight f φ h) q) := by
  obtain ⟨K, hK, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_le
      (h := (h : ℝ)) hf hbox hφ hscale
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let D : ℝ :=
    ‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
      (AX + 8) * (AY + 8) * min X Y
  have hAX : 0 ≤ AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 ≤ AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hmin : 0 ≤ min X Y :=
    le_min (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hD : 0 ≤ D := by positivity
  have hmajor : Summable (fun q : ℕ =>
      D * (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))) :=
    summable_natCast_inv_sq_mul_rpow_half.mul_left D
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hqOne (by norm_num)
    have hlog := Real.log_natCast_le_rpow_div q
      (by norm_num : (0 : ℝ) < 1 / 4)
    have hLXpow : AX + 2 * Real.log q ≤
        (AX + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
      have hAXpow : AX ≤ AX * (q : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX]
      have hlog' : 2 * Real.log q ≤
          8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num at hlog ⊢
        linarith
      nlinarith
    have hLYpow : AY + 2 * Real.log q ≤
        (AY + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
      have hAYpow : AY ≤ AY * (q : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY]
      have hlog' : 2 * Real.log q ≤
          8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num at hlog ⊢
        linarith
      nlinarith
    have hhalf :
        (q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) =
          (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < q)]
      norm_num
    rw [dfiEquation27CentralSummand, norm_mul, norm_mul]
    have hprod := mul_le_mul
      (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
        a b h q ha hb hh)
      (hcentral a b q hq)
      (norm_nonneg (dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) h)) (by positivity)
    calc
      ‖((a : ℂ) * b)⁻¹‖ * ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖ =
        ‖((a : ℂ) * b)⁻¹‖ *
          (‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            ‖dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ h) h‖) := by ring
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          ((((a * b * h ^ 2 : ℕ) : ℝ)) * ((q : ℝ) ^ 2)⁻¹ *
            (K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
            min X Y) * ((q : ℝ) ^ 2)⁻¹ *
          (AX + 2 * Real.log q) * (AY + 2 * Real.log q) := by ring
      _ ≤ (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
            min X Y) * ((q : ℝ) ^ 2)⁻¹ *
          ((AX + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) *
          ((AY + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
      _ = D * (((q : ℝ) ^ 2)⁻¹ *
          ((q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ))) := by
        dsimp [D]
        ring
      _ = D * (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [hhalf]

/-- Source-strength pointwise majorant for the integrated equation-(27)
central summand.  For every `0 < ε < 1`, the two logarithms in the central
integral cost only `q^ε`; the arithmetic coefficient still supplies
`q⁻²`.  This is the quantitative input for truncating the infinite
Ramanujan main term at modulus `Q`. -/
theorem exists_norm_dfiEquation27CentralSummand_le_epsilon
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, 0 < q →
      ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) q‖ ≤
        D * (q : ℝ) ^ (-(2 - ε)) := by
  obtain ⟨K, hK, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_le
      (h := (h : ℝ)) hf hbox hφ hscale
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let E : ℝ := 4 * ε⁻¹
  let D : ℝ :=
    ‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
      (AX + E) * (AY + E) * min X Y
  have hAX : 0 ≤ AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 ≤ AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hmin : 0 ≤ min X Y :=
    le_min (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hD : 0 ≤ D := by positivity
  refine ⟨D, hD, ?_⟩
  intro q hq
  letI : NeZero q := ⟨hq.ne'⟩
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδ0 : (0 : ℝ) < ε / 2 := by positivity
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (ε / 2) :=
    Real.one_le_rpow hqOne hδ0.le
  have hlog := Real.log_natCast_le_rpow_div q hδ0
  have hlog' : 2 * Real.log q ≤ E * (q : ℝ) ^ (ε / 2) := by
    calc
      2 * Real.log q ≤ 2 * ((q : ℝ) ^ (ε / 2) / (ε / 2)) := by
        gcongr
      _ = E * (q : ℝ) ^ (ε / 2) := by
        dsimp [E]
        field_simp [ne_of_gt hε0]
        ring
  have hLXpow : AX + 2 * Real.log q ≤
      (AX + E) * (q : ℝ) ^ (ε / 2) := by
    have hAXpow : AX ≤ AX * (q : ℝ) ^ (ε / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX]
    nlinarith
  have hLYpow : AY + 2 * Real.log q ≤
      (AY + E) * (q : ℝ) ^ (ε / 2) := by
    have hAYpow : AY ≤ AY * (q : ℝ) ^ (ε / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY]
    nlinarith
  have hεpow :
      (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ ε := by
    rw [← Real.rpow_add hqreal]
    congr 1
    ring
  have hinvSq : ((q : ℝ) ^ 2)⁻¹ = (q : ℝ) ^ (-(2 : ℝ)) := by
    calc
      ((q : ℝ) ^ 2)⁻¹ = ((q : ℝ) ^ (2 : ℝ))⁻¹ :=
        congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (q : ℝ) 2).symm
      _ = (q : ℝ) ^ (-(2 : ℝ)) :=
        (Real.rpow_neg hqreal.le (2 : ℝ)).symm
  rw [dfiEquation27CentralSummand, norm_mul, norm_mul]
  have hprod := mul_le_mul
    (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b h q ha hb hh)
    (hcentral a b q hq)
    (norm_nonneg (dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) h)) (by positivity)
  calc
    ‖((a : ℂ) * b)⁻¹‖ * ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
        ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ =
      ‖((a : ℂ) * b)⁻¹‖ *
        (‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖) := by ring
    _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
        ((((a * b * h ^ 2 : ℕ) : ℝ)) * ((q : ℝ) ^ 2)⁻¹ *
          (K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
          min X Y) * ((q : ℝ) ^ 2)⁻¹ *
        (AX + 2 * Real.log q) * (AY + 2 * Real.log q) := by ring
    _ ≤ (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
          min X Y) * ((q : ℝ) ^ 2)⁻¹ *
        ((AX + E) * (q : ℝ) ^ (ε / 2)) *
        ((AY + E) * (q : ℝ) ^ (ε / 2)) := by
      gcongr
    _ = D * (((q : ℝ) ^ 2)⁻¹ *
        ((q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2))) := by
      dsimp [D]
      ring
    _ = D * ((q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ ε) := by
      rw [hεpow, hinvSq]
    _ = D * (q : ℝ) ^ (-(2 : ℝ) + ε) := by
      rw [Real.rpow_add hqreal]
    _ = D * (q : ℝ) ^ (-(2 - ε)) := by
      congr 2
      ring

/-- Quantitative tail of the integrated central series in DFI equation
(27).  This is the exact `Q⁻¹⁺ε` truncation estimate used in the passage
from the finite delta-symbol sum to the infinite Ramanujan main term. -/
theorem exists_tsum_norm_dfiEquation27CentralSummand_tail_le_epsilon
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (L : ℕ) (hL : 0 < L) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (L + (j + 1))‖ ≤
        D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := by
  obtain ⟨D, hD, hpoint⟩ :=
    exists_norm_dfiEquation27CentralSummand_le_epsilon
      hf hbox hφ hscale a b h ha hb hh hε0 hε1
  refine ⟨D, hD, ?_⟩
  have hp : 1 < 2 - ε := by linarith
  have hSeries := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 2 - ε) (Nat.cast_pos.mpr hL) hp
  have hSeries' :
      ∑' j : ℕ, ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) ≤
        (L : ℝ) ^ (-(1 - ε)) / (1 - ε) := by
    convert hSeries using 1
    all_goals ring_nf
  have hPowerSummable : Summable (fun j : ℕ =>
      ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 - ε))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hshift
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (L + (j + 1))‖ ≤
          ∑ j ∈ Finset.range N,
            D * ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        gcongr with j hj
        have hq : 0 < L + (j + 1) := by omega
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
          add_left_comm] using hpoint (L + (j + 1)) hq
      _ = D * ∑ j ∈ Finset.range N,
          ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        rw [Finset.mul_sum]
      _ ≤ D * ∑' j : ℕ,
          ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        gcongr
        exact hPowerSummable.sum_le_tsum (Finset.range N)
          (fun j _ => Real.rpow_nonneg (by positivity) _)
      _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) :=
        mul_le_mul_of_nonneg_left hSeries' hD

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

/-- The totalized equation-(24) main branch is exactly the equation-(27)
arithmetic coefficient times the physical main integral, including the
two divisor-variable Jacobians.  This is the source-entry bridge needed to
apply the analytic equation-(27) estimate to equation (22). -/
theorem dfiEquation24MainTotal_eq_equation27_summand
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b h q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) :
    dfiEquation24MainTotal q a b (h : ℤ)
        (dfiEquation23Weight w F a b (h : ℤ) q) =
      (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
        dfiEquation27PhysicalMainIntegral w q a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q) F (h : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation24MainTotal, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    rw [dfiEquation24MainTotal, dif_neg hq0]
    rw [dfiEquation27_main_summand_exact w a b q ha hb hab F (h : ℤ)]
    rw [dfiEquation27ArithmeticCoefficient_eq]
    rw [ramanujanSumInt_neg]
    rw [ramanujanSumInt_ofNat_eq_ramanujanSum, star_ramanujanSum]
    rw [dfiReducedModulus_denominator_eq,
      dfiReducedModulus_denominator_eq]
    push_cast
    field_simp

/-- The complete finite double-main contribution in equations (22)--(24)
is the finite physical equation-(27) sum. -/
theorem sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b h : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) :
    (∑ q ∈ dfiEquation22Moduli Q,
      dfiEquation24MainTotal q a b (h : ℤ)
        (dfiEquation23Weight w F a b (h : ℤ) q)) =
      ∑ q ∈ dfiEquation22Moduli Q,
        (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
          dfiEquation27PhysicalMainIntegral w q a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            F (h : ℝ) := by
  apply Finset.sum_congr rfl
  intro q _
  exact dfiEquation24MainTotal_eq_equation27_summand
    w a b h q ha hb hab F

/-- The finite central equation-(27) sum over the delta-symbol moduli
approximates the infinite Ramanujan main series with the precise
`Q⁻¹⁺ε` tail.  The cutoff is handled exactly as `[1, ceil(2Q))`, so no
endpoint convention is hidden in this estimate. -/
theorem exists_norm_sum_dfiEquation27Central_sub_series_le_epsilon
    {P X Y U Q : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
  let K : ℕ := ⌈2 * Q⌉₊
  let L : ℕ := K - 1
  have hceil : 2 * Q ≤ (K : ℝ) := by
    exact Nat.le_ceil (2 * Q)
  have hK : 1 < K := by
    have : (2 : ℝ) < K := by nlinarith
    have htwo : 2 < K := by exact_mod_cast this
    omega
  have hL : 0 < L := by
    dsimp [L]
    omega
  obtain ⟨D, hD, htail⟩ :=
    exists_tsum_norm_dfiEquation27CentralSummand_tail_le_epsilon
      hf hbox hφ hscale a b h ha hb hh hε0 hε1 L hL
  refine ⟨D, hD, ?_⟩
  let F : ℕ → ℂ := fun q =>
    dfiEquation27CentralSummand a b h (dfiLocalizedWeight f φ h) q
  have hF : Summable F :=
    summable_dfiEquation27CentralSummand
      hf hbox hφ hscale a b h ha hb hh
  have hSplit := hF.sum_add_tsum_nat_add K
  have hFinite : ∑ q ∈ Finset.range K, F q =
      ∑ q ∈ dfiEquation22Moduli Q, F q := by
    rw [dfiEquation22Moduli_eq_Ico]
    change ∑ q ∈ Finset.range K, F q = ∑ q ∈ Finset.Ico 1 K, F q
    rw [show Finset.range K = insert 0 (Finset.Ico 1 K) by
      ext q
      simp
      omega]
    simp [F, dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient]
  have hShift : Summable (fun j : ℕ => F (j + K)) :=
    (summable_nat_add_iff K).2 hF
  have hTailNorm :
      ‖∑' j : ℕ, F (j + K)‖ ≤ ∑' j : ℕ, ‖F (j + K)‖ :=
    norm_tsum_le_tsum_norm hShift.norm
  have hIndex : ∀ j : ℕ, j + K = L + (j + 1) := by
    intro j
    dsimp [L]
    omega
  have hTailBound :
      ∑' j : ℕ, ‖F (j + K)‖ ≤
        D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := by
    calc
      ∑' j : ℕ, ‖F (j + K)‖ =
          ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) (L + (j + 1))‖ := by
        apply tsum_congr
        intro j
        rw [← hIndex j]
      _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := htail
  have hLQ : Q ≤ (L : ℝ) := by
    have hKone : 1 ≤ K := hK.le
    have hcast : (L : ℝ) = (K : ℝ) - 1 := by
      dsimp [L]
      rw [Nat.cast_sub hKone, Nat.cast_one]
    rw [hcast]
    nlinarith
  have hQpos : 0 < Q := by linarith
  have hpow : (L : ℝ) ^ (-(1 - ε)) ≤ Q ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_nonpos hQpos hLQ (by linarith)
  have hden : 0 ≤ (1 - ε)⁻¹ := by positivity
  have hTailScale :
      D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) ≤
        D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
    apply mul_le_mul_of_nonneg_left _ hD
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hpow hden
  unfold dfiEquation27CentralSeries
  change ‖(∑ q ∈ dfiEquation22Moduli Q, F q) - ∑' q : ℕ, F q‖ ≤
    D * (Q ^ (-(1 - ε)) / (1 - ε))
  calc
    ‖(∑ q ∈ dfiEquation22Moduli Q, F q) - ∑' q : ℕ, F q‖ =
        ‖∑' j : ℕ, F (j + K)‖ := by
      rw [← hSplit, hFinite]
      simp
    _ ≤ ∑' j : ℕ, ‖F (j + K)‖ := hTailNorm
    _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := hTailBound
    _ ≤ D * (Q ^ (-(1 - ε)) / (1 - ε)) := hTailScale

/-- Equations (27)--(30), main branch: the finite double-main contribution
from the delta method differs from DFI's infinite Ramanujan main term by
the sum of the integrated small-modulus delta-kernel error and the exact
`Q⁻¹⁺ε` central tail.  No provisional error certificate occurs in this
statement: both terms are the concrete envelopes proved from equation (2). -/
theorem exists_norm_sum_dfiEquation24Main_sub_centralSeries_le
    {P X Y U Q : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hab : a.Coprime b) (j : ℕ) (hj : 2 ≤ j)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1
              ((((⌈2 * Q⌉₊ - 1) + 1 : ℕ) : ℝ) ^ ε))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b
              (⌈2 * Q⌉₊ - 1) j) +
          D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
  let K : ℕ := ⌈2 * Q⌉₊
  let L : ℕ := K - 1
  have hQpos : 0 < Q := by linarith
  have hceil : 2 * Q ≤ (K : ℝ) := Nat.le_ceil (2 * Q)
  have hKtwo : 2 < K := by
    exact_mod_cast (show (2 : ℝ) < K by nlinarith)
  have hL : 1 ≤ L := by
    dsimp [L]
    omega
  have hset : Finset.Icc 1 L = dfiEquation22Moduli Q := by
    rw [dfiEquation22Moduli_eq_Ico]
    change Finset.Icc 1 L = Finset.Ico 1 K
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    dsimp [L]
    omega
  obtain ⟨C, hC, hsmall⟩ :=
    norm_sum_Icc_dfiEquation27_reduced_main_error_le_epsilon
      hQpos w hf hbox hφ hscale j hj hε0
  obtain ⟨D, hD, htail⟩ :=
    exists_norm_sum_dfiEquation27Central_sub_series_le_epsilon
      hf hbox hφ hscale hQ a b h ha hb hh hε0 hε1
  refine ⟨C, D, hC, hD, ?_⟩
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let physical : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let central : ℕ → ℂ := fun q =>
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  have hsmallApply := hsmall a b h L ha hb hh hL
  rw [hset] at hsmallApply
  have hPhysCentral :
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * central q‖ ≤
      ‖c‖ *
        (C * (((a * b : ℕ) : ℝ) *
          (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
          ((1 + ε⁻¹) * max 1 ((((L + 1 : ℕ) : ℝ) ^ ε)))) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b L j) := by
    rw [← Finset.sum_sub_distrib]
    have hfactor :
        (∑ q ∈ dfiEquation22Moduli Q,
          (c * dfiEquation27ArithmeticCoefficient a b h q * physical q -
            c * dfiEquation27ArithmeticCoefficient a b h q * central q)) =
          c * ∑ q ∈ dfiEquation22Moduli Q,
            dfiEquation27ArithmeticCoefficient a b h q *
              (physical q - central q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hfactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hsmallApply (norm_nonneg c)
  have hMain :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) =
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q := by
    rw [sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
      w a b h ha hb hab (dfiLocalizedWeight f φ h)]
  have hCentral :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) q) =
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * central q := by
    apply Finset.sum_congr rfl
    intro q _
    rfl
  have hTriangle :
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        ‖(∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          ∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q‖ +
        ‖(∑ q ∈ dfiEquation22Moduli Q,
            dfiEquation27CentralSummand a b h
              (dfiLocalizedWeight f φ h) q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ := by
    rw [hMain, hCentral]
    calc
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ =
        ‖((∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          ∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q) +
          ((∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h))‖ := by
          congr 1
          ring
      _ ≤ _ := norm_add_le _ _
  calc
    ‖(∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24MainTotal q a b (h : ℤ)
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h
          (dfiLocalizedWeight f φ h)‖ ≤ _ := hTriangle
    _ ≤ ‖c‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1 ((((L + 1 : ℕ) : ℝ) ^ ε)))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b L j) +
        D * (Q ^ (-(1 - ε)) / (1 - ε)) :=
      add_le_add hPhysCentral htail
    _ = ‖(((a : ℂ) * b)⁻¹)‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1
              ((((⌈2 * Q⌉₊ - 1) + 1 : ℕ) : ℝ) ^ ε))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b
              (⌈2 * Q⌉₊ - 1) j) +
          D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
      rfl

end RiemannZeta.GuthMaynard
