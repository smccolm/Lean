import GafniTao.Pintz2023MellinHorizontal
import GafniTao.FordZetaBasic

/-!
# Pintz (2023), Lemma 3.4: vertical-line integrability

Both complete vertical lines in the Mellin shift are absolutely integrable.
On the left line the removable Gamma singularity is retained exactly; only
outside a compact interval do we rewrite it as the literal source product.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem continuous_pintz2023MellinContourIntegrand_vertical
    {N : ℕ} (hN : 0 < N) {s a : ℂ}
    (ha : -(1 : ℝ) < a.re) (hpole : (s + a).re ≠ 1) :
    Continuous (fun t : ℝ =>
      pintz2023MellinContourIntegrand N s (a + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.2
  intro t
  have harg : -(1 : ℝ) < (a + (t : ℂ) * I).re := by simpa using ha
  have hOpen : IsOpen {w : ℂ | -(1 : ℝ) < w.re} :=
    isOpen_lt continuous_const continuous_re
  have hWeightAt : ContinuousAt (pintz2023MellinWeight N)
      (a + (t : ℂ) * I) :=
    ((differentiableOn_pintz2023MellinWeight hN
      (a + (t : ℂ) * I) harg).continuousWithinAt).continuousAt
        (hOpen.mem_nhds harg)
  have hWeight : ContinuousAt
      (fun u : ℝ => pintz2023MellinWeight N (a + (u : ℂ) * I)) t :=
    ContinuousAt.comp (g := pintz2023MellinWeight N)
      (f := fun u : ℝ => a + (u : ℂ) * I) hWeightAt (by fun_prop)
  have hzetaPoint : s + (a + (t : ℂ) * I) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_self, add_zero, one_re] at hre
    exact hpole hre
  have hZeta : ContinuousAt
      (fun u : ℝ => riemannZeta (s + (a + (u : ℂ) * I))) t :=
    ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => s + (a + (u : ℂ) * I))
      (differentiableAt_riemannZeta hzetaPoint).continuousAt (by fun_prop)
  exact hWeight.mul hZeta

theorem integrable_pintz2023MellinContourIntegrand_right
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ =>
      pintz2023MellinContourIntegrand N s
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let Z : ℝ := ‖riemannZeta (((s.re + 2 : ℝ) : ℂ))‖
  let M : ℝ := 5 * (N : ℝ) ^ 2 * Z
  have hCont : Continuous (fun t : ℝ =>
      pintz2023MellinContourIntegrand N s
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    apply continuous_pintz2023MellinContourIntegrand_vertical hN
    · norm_num
    · simp
      linarith
  have hMajorant : Integrable (fun t : ℝ =>
      M * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
    integrable_pintz2023_Gamma_two_vertical.norm.const_mul M
  apply hMajorant.mono' hCont.aestronglyMeasurable
  filter_upwards with t
  have hPower := norm_pintz2023MellinPowerDiff_horizontal_le
    (x := (2 : ℝ)) (y := t) hN (by norm_num)
  have hzeta :
      ‖riemannZeta (s + (((2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤ Z := by
    have hraw := ford_norm_riemannZeta_le_real
      (sigma := s.re + 2) (t := s.im + t) (by linarith)
    have heq : s + (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
        (((s.re + 2 : ℝ) : ℂ) + I * (s.im + t)) := by
      apply Complex.ext <;> simp [mul_comm]
    rw [heq]
    simpa [Z] using hraw
  have hw : (((2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  rw [pintz2023MellinContourIntegrand_eq_source hw,
    norm_mul, norm_mul]
  change _ ≤ M * _
  dsimp only [M]
  calc
    ‖pintz2023MellinPowerDiff N (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖riemannZeta (s + (((2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤
      (5 * (N : ℝ) ^ 2) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ * Z := by
      gcongr
    _ = (5 * (N : ℝ) ^ 2 * Z) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by ring

noncomputable def pintz2023MellinLeftTailSize (N : ℕ) : ℝ :=
  1200 * (N : ℝ) ^ 2

theorem norm_pintz2023MellinContourIntegrand_left_far_le
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 1 / 4 ≤ s.re)
    {u : ℝ} (hu : |s.re| + |s.im| + 2 ≤ |u|) :
    ‖pintz2023MellinContourIntegrand N s ((u : ℂ) * I)‖ ≤
      pintz2023MellinLeftTailSize N / |u| ^ 2 := by
  have huOne : 1 ≤ |u| := by
    have hnonneg : 0 ≤ |s.re| + |s.im| := by positivity
    linarith
  have huPos : 0 < |u| := zero_lt_one.trans_le huOne
  have hu0 : u ≠ 0 := abs_pos.mp huPos
  have hw : (u : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hu0) I_ne_zero
  have hPower := norm_pintz2023MellinPowerDiff_horizontal_le
    (x := (0 : ℝ)) (y := u) hN (by norm_num)
  have hPower' : ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ ≤
      5 * (N : ℝ) ^ 2 := by simpa using hPower
  have hGamma := pintz2023_Gamma_positive_strip_norm_le
    (a := (0 : ℝ)) (t := u) (by norm_num) (by norm_num) huOne
  have hGamma' : ‖Complex.Gamma ((u : ℂ) * I)‖ ≤ 24 / |u| ^ 3 := by
    simpa using hGamma
  have hheight : 1 ≤ |s.im + u| := by
    have htri := abs_sub_abs_le_abs_sub u (-s.im)
    rw [abs_neg, sub_neg_eq_add] at htri
    rw [add_comm]
    linarith [abs_nonneg s.re]
  have hzetaRe : (1 / 4 : ℝ) ≤ (s + (u : ℂ) * I).re := by
    simpa using hs
  have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe (by simpa using hheight)
  have hnorm : ‖s + (u : ℂ) * I‖ ≤ 2 * |u| := by
    calc
      ‖s + (u : ℂ) * I‖ ≤ |(s + (u : ℂ) * I).re| +
          |(s + (u : ℂ) * I).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re| + |s.im + u| := by congr 1 <;> simp
      _ ≤ |s.re| + (|s.im| + |u|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 2 * |u| := by linarith
  rw [pintz2023MellinContourIntegrand_eq_source hw,
    norm_mul, norm_mul]
  calc
    ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ *
        ‖Complex.Gamma ((u : ℂ) * I)‖ *
        ‖riemannZeta (s + (u : ℂ) * I)‖ ≤
      (5 * (N : ℝ) ^ 2) * (24 / |u| ^ 3) *
        (5 * ‖s + (u : ℂ) * I‖) := by
      apply mul_le_mul
      · exact mul_le_mul hPower' hGamma' (norm_nonneg _) (by positivity)
      · exact hzeta
      · exact norm_nonneg _
      · positivity
    _ ≤ (5 * (N : ℝ) ^ 2) * (24 / |u| ^ 3) *
        (5 * (2 * |u|)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
      · positivity
    _ = pintz2023MellinLeftTailSize N / |u| ^ 2 := by
      unfold pintz2023MellinLeftTailSize
      field_simp
      ring

theorem integrable_pintz2023MellinContourIntegrand_left
    {N : ℕ} {s : ℂ} (hN : 0 < N)
    (hsLower : 1 / 4 ≤ s.re) (hsUpper : s.re < 1) :
    Integrable (fun u : ℝ =>
      pintz2023MellinContourIntegrand N s ((u : ℂ) * I)) := by
  let f : ℝ → ℂ := fun u =>
    pintz2023MellinContourIntegrand N s ((u : ℂ) * I)
  let B : ℝ := |s.re| + |s.im| + 2
  let g : ℝ → ℝ := fun u => pintz2023MellinLeftTailSize N * u ^ (-(2 : ℝ))
  have hBone : 1 ≤ B := by
    dsimp only [B]
    have hnonneg : 0 ≤ |s.re| + |s.im| := by positivity
    linarith
  have hBpos : 0 < B := zero_lt_one.trans_le hBone
  have hCont : Continuous f := by
    simpa [f] using continuous_pintz2023MellinContourIntegrand_vertical
      hN (a := (0 : ℂ)) (s := s) (by norm_num) (by simp; linarith)
  have hGPos : IntegrableOn g (Set.Ioi B) := by
    exact (integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ))
      (by norm_num) hBpos).const_mul (pintz2023MellinLeftTailSize N)
  have hPos : IntegrableOn f (Set.Ioi B) := by
    apply Integrable.mono' hGPos hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := hBpos.trans hu
    have hfar : |s.re| + |s.im| + 2 ≤ |u| := by
      rw [abs_of_pos huPos]
      exact hu.le
    have hbound := norm_pintz2023MellinContourIntegrand_left_far_le
      hN hsLower hfar
    have heq : pintz2023MellinLeftTailSize N / |u| ^ 2 = g u := by
      dsimp only [g]
      rw [abs_of_pos huPos, Real.rpow_neg huPos.le]
      simp [div_eq_mul_inv]
    rw [← heq]
    exact hbound
  have hGNeg : IntegrableOn (fun u : ℝ => g (-u)) (Set.Iio (-B)) := by
    have hSource : IntegrableOn g (Set.Ioi (-(-B))) := by simpa using hGPos
    exact hSource.comp_neg_Iio
  have hNeg : IntegrableOn f (Set.Iio (-B)) := by
    apply Integrable.mono' hGNeg hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have huNeg : u < 0 := hu.trans_le (neg_nonpos.mpr hBpos.le)
    have hfar : |s.re| + |s.im| + 2 ≤ |u| := by
      rw [abs_of_neg huNeg]
      change u < -(|s.re| + |s.im| + 2) at hu
      linarith
    have hbound := norm_pintz2023MellinContourIntegrand_left_far_le
      hN hsLower hfar
    have hnegPos : 0 < -u := neg_pos.mpr huNeg
    have heq : pintz2023MellinLeftTailSize N / |u| ^ 2 = g (-u) := by
      dsimp only [g]
      rw [abs_of_neg huNeg, Real.rpow_neg hnegPos.le]
      simp [div_eq_mul_inv]
    rw [← heq]
    exact hbound
  have hMid : IntegrableOn f (Set.Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Set.Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hNeg
  have hLeftUnion := integrableOn_union.2 ⟨hNegClosed, hMid⟩
  have hLeftSet : Set.Iic (-B) ∪ Set.Icc (-B) B = Set.Iic B := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ -B
      · exact Or.inl hu
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeftUnion
  rw [← integrableOn_univ]
  have hAll := integrableOn_union.2 ⟨hLeftUnion, hPos⟩
  have hAllSet : Set.Iic B ∪ Set.Ioi B = Set.univ := by
    ext u
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt u B
  rwa [hAllSet] at hAll

#print axioms integrable_pintz2023MellinContourIntegrand_right
#print axioms norm_pintz2023MellinContourIntegrand_left_far_le
#print axioms integrable_pintz2023MellinContourIntegrand_left

end

end GafniTao
