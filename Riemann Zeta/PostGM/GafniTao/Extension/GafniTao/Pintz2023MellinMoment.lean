import GafniTao.Pintz2023MellinQuantitative

/-!
# A polynomial moment of Pintz's removable Mellin kernel

The shifted zeta factor in Lemma 3.4 grows polynomially in the translated
height.  This file proves that two powers of that height remain integrable
against the exact Mellin kernel, uniformly in the smoothing parameter.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

set_option maxHeartbeats 1200000 in
private theorem integrable_mellin_quadratic_envelope :
    Integrable (fun u : ℝ =>
      (|u| + 2) * (|u| + 1) ^ (2 : ℕ) *
        Real.exp (-(Real.pi * |u|) / 2)) := by
  let b : ℝ := Real.pi / 2
  let g : ℝ → ℝ := fun u =>
    (|u| + 2) * (|u| + 1) ^ (2 : ℕ) *
      Real.exp (-(Real.pi * |u|) / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hThreeRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (3 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hTwoRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (2 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hOneRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (1 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hZeroRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (0 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hThree : IntegrableOn
      (fun u : ℝ => u ^ (3 : ℕ) * Real.exp (-b * u)) (Ioi 0) := by
    simpa [Real.rpow_natCast] using hThreeRaw
  have hTwo : IntegrableOn
      (fun u : ℝ => u ^ (2 : ℕ) * Real.exp (-b * u)) (Ioi 0) := by
    simpa [Real.rpow_natCast] using hTwoRaw
  have hOne : IntegrableOn
      (fun u : ℝ => u * Real.exp (-b * u)) (Ioi 0) := by
    simpa using hOneRaw
  have hZero : IntegrableOn
      (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) := by
    simpa using hZeroRaw
  have hPos : IntegrableOn g (Ioi 0) := by
    have hSum :=
      ((hThree.add (hTwo.const_mul 4)).add (hOne.const_mul 5)).add
        (hZero.const_mul 2)
    apply hSum.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := hu
    have he : -b * u = -(Real.pi * u) / 2 := by
      dsimp only [b]
      ring
    simp only [g, abs_of_pos huPos]
    rw [← he]
    simp only [Pi.add_apply]
    ring_nf
  have hComp : IntegrableOn (fun u : ℝ => g (-u)) (Iio 0) :=
    (show IntegrableOn g (Ioi (-0)) by simpa using hPos).comp_neg_Iio
  have hNegOpen : IntegrableOn g (Iio 0) := by
    apply hComp.congr
    filter_upwards with u
    simp [g]
  have hNeg : IntegrableOn g (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hNegOpen
  rw [← integrableOn_univ]
  have hUnion := integrableOn_union.2 ⟨hNeg, hPos⟩
  simpa only [Iic_union_Ioi, g] using hUnion

set_option maxHeartbeats 1200000 in
/-- The exact imaginary-axis Mellin kernel has a uniform quadratic moment. -/
theorem exists_pintz2023MellinWeight_imaginary_quadratic_moment :
    ∃ L : ℝ, 0 < L ∧ ∀ N : ℕ, 0 < N →
      Integrable (fun u : ℝ =>
        ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          (|u| + 1) ^ (2 : ℕ)) ∧
      (∫ u : ℝ, ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          (|u| + 1) ^ (2 : ℕ)) ≤ L := by
  obtain ⟨C, hC, hTail⟩ :=
    exists_norm_pintz2023MellinWeight_imaginary_tail_le
  let q : ℝ → ℝ := fun u =>
    (|u| + 2) * (|u| + 1) ^ (2 : ℕ) *
      Real.exp (-(Real.pi * |u|) / 2)
  let m : ℝ → ℝ := fun u =>
    (Icc (-1 : ℝ) 1).indicator
        (fun v => Real.log 2 * (|v| + 1) ^ (2 : ℕ)) u + C * q u
  have hCentral : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun v => Real.log 2 * (|v| + 1) ^ (2 : ℕ))) := by
    have hContinuous : Continuous (fun v : ℝ =>
        Real.log 2 * (|v| + 1) ^ (2 : ℕ)) := by fun_prop
    exact (hContinuous.continuousOn.integrableOn_compact
      isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_mellin_quadratic_envelope
  have hm : Integrable m := hCentral.add (hq.const_mul C)
  let L : ℝ := (∫ u : ℝ, m u) + 1
  have hmNonneg : ∀ u : ℝ, 0 ≤ m u := by
    intro u
    dsimp only [m]
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
      positivity
    · rw [Set.indicator_of_notMem hu, zero_add]
      positivity
  have hIntNonneg : 0 ≤ ∫ u : ℝ, m u := integral_nonneg hmNonneg
  refine ⟨L, by dsimp only [L]; linarith, ?_⟩
  intro N hN
  let f : ℝ → ℝ := fun u =>
    ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
      (|u| + 1) ^ (2 : ℕ)
  have hWeightContinuous : Continuous (fun u : ℝ =>
      pintz2023MellinWeight N ((u : ℂ) * I)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hDiff := differentiableOn_pintz2023MellinWeight hN
      ((u : ℂ) * I) (by norm_num)
    have hOpen : IsOpen {w : ℂ | -(1 : ℝ) < w.re} :=
      isOpen_lt continuous_const continuous_re
    have hAt := hDiff.continuousWithinAt.continuousAt
      (hOpen.mem_nhds (by norm_num))
    exact ContinuousAt.comp
      (g := pintz2023MellinWeight N)
      (f := fun v : ℝ => (v : ℂ) * I) hAt (by fun_prop)
  have hfContinuous : Continuous f := by
    dsimp only [f]
    exact hWeightContinuous.norm.mul
      ((continuous_abs.add continuous_const).pow 2)
  have hMeas : AEStronglyMeasurable f :=
    hfContinuous.aestronglyMeasurable
  have hBound : ∀ᵐ u : ℝ ∂volume, f u ≤ m u := by
    filter_upwards [(show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton])] with u hu
    by_cases hsmall : |u| ≤ 1
    · have hmem : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(abs_le.mp hsmall).1, (abs_le.mp hsmall).2⟩
      have hKernel := norm_pintz2023MellinWeight_imaginary_le_log hN hu
      dsimp only [f, m]
      rw [Set.indicator_of_mem hmem]
      have hfactor : 0 ≤ (|u| + 1) ^ (2 : ℕ) := by positivity
      exact (mul_le_mul_of_nonneg_right hKernel hfactor).trans
        (le_add_of_nonneg_right (by positivity))
    · have hlarge : 1 ≤ |u| := by linarith
      have hnotmem : u ∉ Icc (-1 : ℝ) 1 := by
        intro hmem
        exact hsmall (abs_le.mpr hmem)
      have hKernel := hTail N u hN hlarge
      dsimp only [f, m]
      rw [Set.indicator_of_notMem hnotmem, zero_add]
      have hfactor : 0 ≤ (|u| + 1) ^ (2 : ℕ) := by positivity
      calc
        ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
            (|u| + 1) ^ (2 : ℕ) ≤
          (C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2)) *
            (|u| + 1) ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_right hKernel hfactor
        _ = C * q u := by dsimp only [q]; ring
  have hfNonneg : ∀ u : ℝ, 0 ≤ f u := by
    intro u
    dsimp only [f]
    positivity
  have hBoundNorm : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ m u := by
    filter_upwards [hBound] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg u)]
    exact hu
  have hf : Integrable f := hm.mono' hMeas hBoundNorm
  refine ⟨hf, ?_⟩
  have hIntegral := integral_mono_ae hf hm hBound
  dsimp only [L]
  exact hIntegral.trans (le_add_of_nonneg_right zero_le_one)

#print axioms exists_pintz2023MellinWeight_imaginary_quadratic_moment

end

end GafniTao
