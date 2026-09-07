import GafniTao.HeathBrownMellinBounds
import GafniTao.HeathBrownLocalSecondMoment

/-!
# Heath--Brown's off-critical zeta-square estimate

This file estimates the retained line in the exact two-pole Mellin shift.
The singular factor `(delta + |u|)⁻¹` is kept explicitly.  This is the
quantitative form of equation (40) before the source choice
`delta = (log t)⁻¹`.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exact weighted critical-line moment produced by the shifted Gamma
kernel. -/
noncomputable def heathBrownMellinCriticalMoment (delta t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u|) / (delta + |u|) *
    heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)

/-- The untruncated exponential convolution occurring after the source choice
`delta = (log t)⁻¹`. -/
noncomputable def heathBrownFullCriticalMoment (t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u|) *
    heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)

private theorem heathBrownMellinCriticalMoment_integrand_nonneg
    {delta t u : ℝ} (hdelta : 0 < delta) :
    0 ≤ Real.exp (-|u|) / (delta + |u|) *
      heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) := by
  positivity

/-- Absolute convergence of the exact weighted critical-line moment. -/
theorem integrable_heathBrownMellinCriticalMoment
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ => Real.exp (-|u|) / (delta + |u|) *
      heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) / (delta + |u|) *
    heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)
  let B : ℝ := |t| + 2
  let M : ℝ := 100 / delta
  let g : ℝ → ℝ := fun u => M * (|u| ^ 2 * Real.exp (-|u|))
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith [abs_nonneg t]
  have hMnonneg : 0 ≤ M := by dsimp only [M]; positivity
  have hCont : Continuous f := by
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro u hu
        have : 0 < delta + |u| := by positivity
        exact this.ne' hu
    · exact continuous_heathBrownCriticalZetaNorm_sq.comp (by fun_prop)
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul M
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      have htri := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add] at htri
      rw [add_comm] at htri
      linarith
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
    have hzRe : (1 / 4 : ℝ) ≤ z.re := by
      simp [z]
      norm_num
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by simpa [z] using hheight)
    have hnorm : ‖z‖ ≤ 2 * |u| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 : ℝ) + |t + u| := by simp [z]
        _ ≤ 1 / 2 + (|t| + |u|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |u| := by linarith
    have hzeta' : heathBrownCriticalZetaNorm (t + u) ≤ 10 * |u| := by
      unfold heathBrownCriticalZetaNorm
      change ‖riemannZeta z‖ ≤ _
      exact hzeta.trans (by nlinarith)
    have hdenom : delta ≤ delta + |u| := by linarith [abs_nonneg u]
    have hrecip : 1 / (delta + |u|) ≤ 1 / delta := by
      exact one_div_le_one_div_of_le hdelta hdenom
    have hsq : heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
        100 * |u| ^ 2 := by
      calc
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
            (10 * |u|) ^ (2 : ℕ) :=
          pow_le_pow_left₀
            (norm_nonneg (riemannZeta
              (((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I))) hzeta' 2
        _ = 100 * |u| ^ 2 := by ring
    have hfNonneg : 0 ≤ f u := by
      dsimp only [f]
      exact heathBrownMellinCriticalMoment_integrand_nonneg hdelta
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g, M]
    have hexp : 0 ≤ Real.exp (-|u|) := (Real.exp_pos _).le
    calc
      Real.exp (-|u|) / (delta + |u|) *
          heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
        (Real.exp (-|u|) / delta) * (100 * |u| ^ 2) := by
          gcongr
      _ = 100 / delta * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hTail u (by rw [abs_of_pos (hBpos.trans hu)]; exact hu)
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have hu' : u < -B := Set.mem_Iio.mp hu
    have huNeg : u < 0 := hu'.trans_le (neg_nonpos.mpr hBpos.le)
    apply hTail u
    rw [abs_of_neg huNeg]
    linarith
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext u
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ -B
      · exact Or.inl hu
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext u
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt u B
  rwa [hAllSet] at hAll

/-- Absolute convergence of Heath--Brown's full exponential convolution. -/
theorem integrable_heathBrownFullCriticalMoment (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-|u|) *
      heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) *
    heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)
  let B : ℝ := |t| + 2
  let g : ℝ → ℝ := fun u => 100 * (|u| ^ 2 * Real.exp (-|u|))
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith [abs_nonneg t]
  have hCont : Continuous f := by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-|u|))).mul
      (continuous_heathBrownCriticalZetaNorm_sq.comp (by fun_prop))
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul 100
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      have htri := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at htri
      linarith
    let z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
    have hzRe : (1 / 4 : ℝ) ≤ z.re := by
      simp [z]
      norm_num
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by simpa [z] using hheight)
    have hnorm : ‖z‖ ≤ 2 * |u| := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 : ℝ) + |t + u| := by simp [z]
        _ ≤ 1 / 2 + (|t| + |u|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |u| := by linarith
    have hzeta' : heathBrownCriticalZetaNorm (t + u) ≤ 10 * |u| := by
      unfold heathBrownCriticalZetaNorm
      change ‖riemannZeta z‖ ≤ _
      exact hzeta.trans (by nlinarith)
    have hsq : heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
        100 * |u| ^ 2 := by
      calc
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
            (10 * |u|) ^ (2 : ℕ) :=
          pow_le_pow_left₀
            (norm_nonneg (riemannZeta
              (((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I))) hzeta' 2
        _ = 100 * |u| ^ 2 := by ring
    have hfNonneg : 0 ≤ f u := by dsimp only [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g]
    calc
      Real.exp (-|u|) * heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
          Real.exp (-|u|) * (100 * |u| ^ 2) := by gcongr
      _ = 100 * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hTail u (by rw [abs_of_pos (hBpos.trans hu)]; exact hu)
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have hu' : u < -B := Set.mem_Iio.mp hu
    have huNeg : u < 0 := hu'.trans_le (neg_nonpos.mpr hBpos.le)
    apply hTail u
    rw [abs_of_neg huNeg]
    linarith
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext u
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ -B
      · exact Or.inl hu
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext u
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt u B
  rwa [hAllSet] at hAll

/-- The exact Gamma-kernel moment loses at most `delta⁻¹` against the
unweighted exponential convolution. -/
theorem heathBrownMellinCriticalMoment_le_full
    {delta t : ℝ} (hdelta : 0 < delta) :
    heathBrownMellinCriticalMoment delta t ≤
      (1 / delta) * heathBrownFullCriticalMoment t := by
  unfold heathBrownMellinCriticalMoment heathBrownFullCriticalMoment
  calc
    (∫ u : ℝ, Real.exp (-|u|) / (delta + |u|) *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) ≤
      ∫ u : ℝ, (1 / delta) * (Real.exp (-|u|) *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by
          apply integral_mono
            (integrable_heathBrownMellinCriticalMoment
              (delta := delta) (t := t) hdelta)
            ((integrable_heathBrownFullCriticalMoment t).const_mul (1 / delta))
          intro u
          have hdenom : delta ≤ delta + |u| := by
            linarith [abs_nonneg u]
          have hrecip : 1 / (delta + |u|) ≤ 1 / delta :=
            one_div_le_one_div_of_le hdelta hdenom
          change Real.exp (-|u|) / (delta + |u|) *
              heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
            (1 / delta) * (Real.exp (-|u|) *
              heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ))
          calc
            Real.exp (-|u|) / (delta + |u|) *
                heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) =
              (1 / (delta + |u|)) * (Real.exp (-|u|) *
                heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by ring
            _ ≤ (1 / delta) * (Real.exp (-|u|) *
                heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by
              gcongr
    _ = (1 / delta) * ∫ u : ℝ, Real.exp (-|u|) *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) :=
      integral_const_mul _ _

theorem heathBrownMellinCriticalMoment_nonneg
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 ≤ heathBrownMellinCriticalMoment delta t := by
  unfold heathBrownMellinCriticalMoment
  exact integral_nonneg fun u =>
    heathBrownMellinCriticalMoment_integrand_nonneg hdelta

theorem heathBrownFullCriticalMoment_nonneg (t : ℝ) :
    0 ≤ heathBrownFullCriticalMoment t := by
  unfold heathBrownFullCriticalMoment
  exact integral_nonneg fun u => by positivity

/-- Pointwise domination of the retained Mellin integrand by the exact
critical-line kernel. -/
theorem exists_norm_heathBrown_leftMellinIntegrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t u : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * (Real.exp (-|u|) / (delta + |u|) *
          heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hKernel⟩ := exists_heathBrown_Gamma_shift_kernel_bound
  refine ⟨C, hC, ?_⟩
  intro delta t u hdelta hdeltaUpper
  have hdenom : 0 < delta + |u| := by positivity
  have hGamma :
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (-|u|) / (delta + |u|) := by
    apply (le_div_iff₀ hdenom).2
    simpa only [mul_comm] using
      (hKernel delta u hdelta hdeltaUpper).2
  have harg :
      (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I) +
          (((-delta : ℝ) : ℂ) + (u : ℂ) * I) =
        ((1 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  change _ * heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤ _
  calc
    ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) ≤
      (C * Real.exp (-|u|) / (delta + |u|)) *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ) := by
          gcongr
    _ = C * (Real.exp (-|u|) / (delta + |u|) *
        heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)) := by ring

/-- Quantitative bound for the complete retained vertical line in the
two-pole shift. -/
theorem exists_norm_heathBrown_leftVertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖VerticalIntegral'
          (heathBrownZetaSquareMellinIntegrand
            (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)) (-delta)‖ ≤
        C * heathBrownMellinCriticalMoment delta t := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrown_leftMellinIntegrand_le
  let D : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  let C : ℝ := D * B
  have hD : 0 < D := by
    dsimp only [D]
    rw [norm_pos_iff]
    apply one_div_ne_zero
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  refine ⟨C, mul_pos hD hB, ?_⟩
  intro delta t hdelta hdeltaUpper
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let f : ℝ → ℂ := fun u =>
    heathBrownZetaSquareMellinIntegrand s
      (((-delta : ℝ) : ℂ) + (u : ℂ) * I)
  let g : ℝ → ℝ := fun u => Real.exp (-|u|) / (delta + |u|) *
    heathBrownCriticalZetaNorm (t + u) ^ (2 : ℕ)
  have hf : Integrable f := by
    apply integrable_heathBrownZetaSquareMellinIntegrand_minus
      (s := s) hdelta hdeltaUpper
    · dsimp only [s]
      simp
      norm_num
    · dsimp only [s]
      simp
  have hg : Integrable g := by
    simpa only [g] using
      integrable_heathBrownMellinCriticalMoment (delta := delta) (t := t) hdelta
  have hIntegral : (∫ u : ℝ, ‖f u‖) ≤ B * ∫ u : ℝ, g u := by
    calc
      (∫ u : ℝ, ‖f u‖) ≤ ∫ u : ℝ, B * g u := by
        apply integral_mono hf.norm (hg.const_mul B)
        intro u
        simpa only [f, g, s] using hPoint delta t u hdelta hdeltaUpper
      _ = B * ∫ u : ℝ, g u := integral_const_mul B g
  unfold VerticalIntegral' VerticalIntegral
  rw [norm_smul, norm_smul]
  simp only [norm_I, one_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖∫ u : ℝ, f u‖ ≤
        D * ∫ u : ℝ, ‖f u‖ := by
      dsimp only [D]
      gcongr
      exact norm_integral_le_integral_norm f
    _ ≤ D * (B * ∫ u : ℝ, g u) := by
      exact mul_le_mul_of_nonneg_left hIntegral hD.le
    _ = C * heathBrownMellinCriticalMoment delta t := by
      dsimp only [C, D]
      unfold heathBrownMellinCriticalMoment
      change _ = (_ * B) * ∫ u : ℝ, g u
      ring

/-- Heath--Brown's equation-(40) estimate on the right of the critical line,
with the exact weighted moment still visible. -/
theorem exists_heathBrown_offCritical_plus_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) ≤
        C * (1 + heathBrownMellinCriticalMoment delta t) := by
  obtain ⟨R, hR, hResidue⟩ :=
    exists_norm_heathBrownMovingPoleResidue_le
  obtain ⟨V, hV, hVertical⟩ :=
    exists_norm_heathBrown_leftVertical_le
  let S : ℝ := heathBrownSmoothedDivisorMajorant
  let C : ℝ := S + R + V + 1
  have hS : 0 ≤ S := by
    exact heathBrownSmoothedDivisorMajorant_nonneg
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let m : ℝ := heathBrownMellinCriticalMoment delta t
  have hsRe : s.re = 1 / 2 + delta := by simp [s]
  have hEq := heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical
    (s := s) hdelta hdeltaUpper hsRe
  have hSeries : ‖heathBrownSmoothedDivisorSeries s‖ ≤ S := by
    exact norm_heathBrownSmoothedDivisorSeries_le (by rw [hsRe]; linarith)
  have hRes : ‖heathBrownMovingPoleResidue s‖ ≤ R := by
    simpa only [s] using hResidue delta t hdelta hdeltaUpper ht
  have hVert :
      ‖VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ ≤
        V * m := by
    simpa only [s, m] using hVertical delta t hdelta hdeltaUpper
  have hm : 0 ≤ m :=
    heathBrownMellinCriticalMoment_nonneg hdelta
  change ‖riemannZeta s‖ ^ (2 : ℕ) ≤ C * (1 + m)
  rw [← norm_pow, hEq]
  calc
    ‖heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s -
        VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ ≤
      ‖heathBrownSmoothedDivisorSeries s‖ +
        ‖heathBrownMovingPoleResidue s‖ +
        ‖VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta)‖ := by
          have hOuter := norm_sub_le
            (heathBrownSmoothedDivisorSeries s - heathBrownMovingPoleResidue s)
            (VerticalIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta))
          have hInner := norm_sub_le
            (heathBrownSmoothedDivisorSeries s)
            (heathBrownMovingPoleResidue s)
          linarith
    _ ≤ S + R + V * m := by linarith
    _ ≤ C * (1 + m) := by
      dsimp only [C]
      nlinarith [mul_nonneg hS hm, mul_nonneg hR.le hm,
        mul_nonneg hV.le hm]

/-- Equation (40) on the positive displaced line after setting
`delta = 1 / log t`. -/
theorem exists_heathBrown_offCritical_plus_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, Real.exp 4 ≤ t →
      ‖riemannZeta
          (((1 / 2 + 1 / Real.log t : ℝ) : ℂ) + (t : ℂ) * I)‖ ^
          (2 : ℕ) ≤
        C * (1 + Real.log t * heathBrownFullCriticalMoment t) := by
  obtain ⟨C, hC, hPlus⟩ := exists_heathBrown_offCritical_plus_le
  refine ⟨C, hC, ?_⟩
  intro t ht
  have htPos : 0 < t := (Real.exp_pos 4).trans_le ht
  have hlog : 4 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 4) ht
    simpa using this
  have hlogPos : 0 < Real.log t := lt_of_lt_of_le (by norm_num) hlog
  let delta : ℝ := 1 / Real.log t
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdeltaUpper : delta ≤ 1 / 4 := by
    dsimp only [delta]
    exact (one_div_le_one_div_of_le (by norm_num) hlog)
  have hExpFourTen : (10 : ℝ) ≤ Real.exp 4 := by
    have hp : (2 : ℝ) ^ (4 : ℕ) < Real.exp 1 ^ (4 : ℕ) :=
      pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
    rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num,
      Real.exp_add, Real.exp_add, Real.exp_add]
    nlinarith
  have hsource := hPlus delta t hdelta hdeltaUpper
    (by linarith)
  have hm := heathBrownMellinCriticalMoment_le_full
    (delta := delta) (t := t) hdelta
  have hInv : 1 / delta = Real.log t := by
    dsimp only [delta]
    field_simp
  rw [hInv] at hm
  have hfull := heathBrownFullCriticalMoment_nonneg t
  have hmono :
      C * (1 + heathBrownMellinCriticalMoment delta t) ≤
        C * (1 + Real.log t * heathBrownFullCriticalMoment t) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith
  simpa only [delta] using hsource.trans hmono


end

end GafniTao
