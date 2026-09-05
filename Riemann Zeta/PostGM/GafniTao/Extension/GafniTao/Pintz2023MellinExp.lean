import GafniTao.Pintz2023SmoothedZeta
import RiemannZeta.GuthMaynard.GammaVerticalDecay
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Pintz (2023), Lemma 3.4: Mellin inversion of the exponential

This file proves the exact inverse-Mellin formula used in Pintz (3.5).  The
vertical integrability of `Gamma` on `Re w = 2` is derived from the Gamma
recurrence and Euler's integral; it is not inserted as an analytic premise.
-/

open Complex Set MeasureTheory Filter
open scoped Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Cubic decay on the literal right line `Re w = 2`. -/
theorem pintz2023_Gamma_two_vertical_decay (t : ℝ) :
    |t| ^ 3 * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 24 := by
  by_cases ht : t = 0
  · subst t
    norm_num
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hsFactor : ∀ (j : ℕ), j < 3 → s + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have him := congrArg Complex.im hzero
    simp [s] at him
    exact ht him
  have hRec := Gamma_add_nat_eq_prod_mul s 3 hsFactor
  have hNormRec :
      ‖Complex.Gamma (s + 3)‖ =
        ‖∏ j ∈ Finset.range 3, (s + (j : ℂ))‖ * ‖Complex.Gamma s‖ := by
    have hRec' : Complex.Gamma (s + 3) =
        (∏ j ∈ Finset.range 3, (s + (j : ℂ))) * Complex.Gamma s := by
      simpa using hRec
    rw [hRec', norm_mul]
  have hProd : |t| ^ 3 ≤ ‖∏ j ∈ Finset.range 3, (s + (j : ℂ))‖ := by
    simpa [s] using abs_im_pow_le_norm_prod_horizontal 2 t 3
  have hShiftRe : (s + 3).re = 5 := by norm_num [s]
  have hNormShift : ‖Complex.Gamma (s + 3)‖ ≤ Real.Gamma 5 := by
    simpa [hShiftRe] using
      Complex.Gamma.norm_le_Gamma_re (z := s + 3) (by norm_num [hShiftRe])
  have hGammaFive : Real.Gamma 5 = 24 := by
    rw [show (5 : ℝ) = (4 : ℕ) + 1 by norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num
  calc
    |t| ^ 3 * ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)‖ ≤
        ‖∏ j ∈ Finset.range 3, (s + (j : ℂ))‖ * ‖Complex.Gamma s‖ := by
      simpa [s] using mul_le_mul_of_nonneg_right hProd (norm_nonneg _)
    _ = ‖Complex.Gamma (s + 3)‖ := hNormRec.symm
    _ ≤ Real.Gamma 5 := hNormShift
    _ = 24 := hGammaFive

theorem continuous_pintz2023_Gamma_two_vertical :
    Continuous (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hNoPole : ∀ m : ℕ, (2 : ℂ) + (t : ℂ) * I ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmNonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact ContinuousAt.comp'
    (Complex.differentiableAt_Gamma _ hNoPole).continuousAt (by fun_prop)

set_option maxHeartbeats 800000 in
/-- Absolute convergence of the inverse-Mellin line in (3.5). -/
theorem integrable_pintz2023_Gamma_two_vertical :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)) := by
  let f : ℝ → ℂ := fun t => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun t => 24 * t ^ (-(3 : ℝ))
  have hCont : Continuous f := by
    simpa [f] using continuous_pintz2023_Gamma_two_vertical
  have hGPos : IntegrableOn g (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 24
  have hPos : IntegrableOn f (Ioi (1 : ℝ)) := by
    apply Integrable.mono' hGPos hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := zero_lt_one.trans ht
    have htAbs : 1 ≤ |t| := by simpa [abs_of_pos htPos] using ht.le
    have hDecay := pintz2023_Gamma_two_vertical_decay t
    have hDiv : ‖f t‖ ≤ 24 / |t| ^ 3 := by
      apply (le_div_iff₀ (pow_pos (abs_pos.mpr (by linarith)) 3)).2
      simpa [f, mul_comm] using hDecay
    have hEq : 24 / |t| ^ 3 = g t := by
      dsimp [g]
      rw [abs_of_pos htPos]
      simp [div_eq_mul_inv, Real.rpow_neg htPos.le]
    rw [← hEq]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hDiv
  have hGNeg : IntegrableOn (fun t : ℝ => g (-t)) (Iio (-1 : ℝ)) := by
    have hSource : IntegrableOn g (Ioi (-(-1 : ℝ))) := by simpa using hGPos
    exact hSource.comp_neg_Iio
  have hNeg : IntegrableOn f (Iio (-1 : ℝ)) := by
    apply Integrable.mono' hGNeg hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    change t < -1 at ht
    have htNeg : t < 0 := by linarith
    have htAbs : 1 ≤ |t| := by rw [abs_of_neg htNeg]; linarith
    have hDecay := pintz2023_Gamma_two_vertical_decay t
    have hDiv : ‖f t‖ ≤ 24 / |t| ^ 3 := by
      apply (le_div_iff₀ (pow_pos (abs_pos.mpr (by linarith)) 3)).2
      simpa [f, mul_comm] using hDecay
    have hEq : 24 / |t| ^ 3 = g (-t) := by
      dsimp [g]
      have hnegPos : 0 < -t := by linarith
      rw [abs_of_neg htNeg]
      simp [div_eq_mul_inv, Real.rpow_neg hnegPos.le]
    rw [← hEq]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hDiv
  have hMid : IntegrableOn f (Icc (-1 : ℝ) 1) :=
    hCont.continuousOn.integrableOn_Icc
  have hLeft : IntegrableOn f (Iic (1 : ℝ)) := by
    have hNegClosed : IntegrableOn f (Iic (-1 : ℝ)) :=
      (integrableOn_Iic_iff_integrableOn_Iio).mpr hNeg
    have hUnion := integrableOn_union.2 ⟨hNegClosed, hMid⟩
    have hSet : Iic (-1 : ℝ) ∪ Icc (-1 : ℝ) 1 = Iic 1 := by
      ext t
      simp only [mem_union, mem_Iic, mem_Icc]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        by_cases ht : t ≤ -1
        · exact Or.inl ht
        · exact Or.inr ⟨by linarith, h⟩
    rwa [hSet] at hUnion
  rw [← integrableOn_univ]
  have hAll := integrableOn_union.2 ⟨hLeft, hPos⟩
  have hSet : Iic (1 : ℝ) ∪ Ioi (1 : ℝ) = Set.univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 1
  rwa [hSet] at hAll

theorem pintz2023_mellinConvergent_exp_neg_two :
    MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) 2 := by
  rw [MellinConvergent]
  simpa [Complex.GammaIntegral, mul_comm] using
    (Complex.GammaIntegral_convergent (by norm_num : (0 : ℝ) < (2 : ℂ).re))

theorem pintz2023_verticalIntegrable_mellin_exp_neg_two :
    VerticalIntegrable
      (mellin (fun x : ℝ => (Real.exp (-x) : ℂ))) 2 := by
  unfold VerticalIntegrable
  apply integrable_pintz2023_Gamma_two_vertical.congr
  filter_upwards with t
  rw [← Complex.GammaIntegral_eq_mellin]
  exact Complex.Gamma_eq_integral (by norm_num :
    (0 : ℝ) < ((2 : ℂ) + (t : ℂ) * I).re)

/-- Exact inverse-Mellin formula for the exponential on Pintz's right line. -/
theorem pintz2023_inverseMellin_exp_neg {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      Real.exp (-x) := by
  have hInv := mellinInv_mellin_eq 2
    (fun y : ℝ => (Real.exp (-y) : ℂ)) hx
    pintz2023_mellinConvergent_exp_neg_two
    pintz2023_verticalIntegrable_mellin_exp_neg_two
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousAt
  have hMellinEq : ∀ t : ℝ,
      mellin (fun y : ℝ => (Real.exp (-y) : ℂ))
          (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
        Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    intro t
    rw [← Complex.GammaIntegral_eq_mellin]
    exact (Complex.Gamma_eq_integral (by norm_num :
      (0 : ℝ) < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re)).symm
  unfold mellinInv at hInv
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        mellin (fun y : ℝ => (Real.exp (-y) : ℂ))
          (((2 : ℝ) : ℂ) + (t : ℂ) * I))) = Real.exp (-x) at hInv
  simpa only [hMellinEq] using hInv

#print axioms pintz2023_Gamma_two_vertical_decay
#print axioms integrable_pintz2023_Gamma_two_vertical
#print axioms pintz2023_inverseMellin_exp_neg

end

end GafniTao
