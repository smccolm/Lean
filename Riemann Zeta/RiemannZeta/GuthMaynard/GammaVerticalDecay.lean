import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds

open Complex
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-- Iterating the Gamma recurrence across a finite number of nonzero factors. -/
theorem Gamma_add_nat_eq_prod_mul (s : ℂ) (n : ℕ)
    (hs : ∀ j < n, s + (j : ℂ) ≠ 0) :
    Complex.Gamma (s + n) =
      (∏ j ∈ Finset.range n, (s + (j : ℂ))) * Complex.Gamma s := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsn : s + (n : ℂ) ≠ 0 := hs n (Nat.lt_succ_self n)
      calc
        Complex.Gamma (s + (n + 1 : ℕ)) =
            Complex.Gamma ((s + (n : ℂ)) + 1) := by
              congr 1
              push_cast
              ring
        _ = (s + (n : ℂ)) * Complex.Gamma (s + (n : ℂ)) :=
          Complex.Gamma_add_one _ hsn
        _ = (s + (n : ℂ)) *
            ((∏ j ∈ Finset.range n, (s + (j : ℂ))) * Complex.Gamma s) := by
              rw [ih (fun j hj => hs j (hj.trans (Nat.lt_succ_self n)))]
        _ = (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) * Complex.Gamma s := by
              rw [Finset.prod_range_succ]
              ring

/-- Every recurrence factor on a horizontal translate dominates the ordinate. -/
lemma abs_im_pow_le_norm_prod_horizontal (a t : ℝ) (n : ℕ) :
    |t| ^ n ≤ ‖∏ j ∈ Finset.range n,
      ((a : ℂ) + (t : ℂ) * I + (j : ℂ))‖ := by
  rw [norm_prod]
  calc
    |t| ^ n = ∏ _j ∈ Finset.range n, |t| := by simp
    _ ≤ ∏ j ∈ Finset.range n, ‖(a : ℂ) + (t : ℂ) * I + (j : ℂ)‖ := by
      apply Finset.prod_le_prod
      · intro j hj
        exact abs_nonneg t
      · intro j hj
        have hIm : (((a : ℂ) + (t : ℂ) * I + (j : ℂ))).im = t := by simp
        simpa [hIm] using
          (Complex.abs_im_le_norm ((a : ℂ) + (t : ℂ) * I + (j : ℂ)))

/--
Uniform arbitrary-order polynomial decay for Gamma on the real strip used by
the Type-II contour.  The estimate follows only from the Gamma recurrence,
the Euler-integral norm bound after shifting to the right, and monotonicity of
the real Gamma function on `[2, ∞)`.
-/
theorem typeII_Gamma_vertical_decay (n : ℕ) (hn : 3 ≤ n)
    {a t : ℝ} (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    |t| ^ n * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
      (Nat.factorial (n - 1) : ℝ) := by
  by_cases ht : t = 0
  · subst t
    have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    rw [abs_zero, zero_pow hnPos.ne', zero_mul]
    positivity
  let s : ℂ := (a : ℂ) + (t : ℂ) * I
  have hsFactor : ∀ j < n, s + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have him := congrArg Complex.im hzero
    simp [s, ht] at him
  have hRec := Gamma_add_nat_eq_prod_mul s n hsFactor
  have hNormRec :
      ‖Complex.Gamma (s + n)‖ =
        ‖∏ j ∈ Finset.range n, (s + (j : ℂ))‖ * ‖Complex.Gamma s‖ := by
    rw [hRec, norm_mul]
  have hProd : |t| ^ n ≤ ‖∏ j ∈ Finset.range n, (s + (j : ℂ))‖ := by
    simpa [s] using abs_im_pow_le_norm_prod_horizontal a t n
  have hShiftRe : (s + n).re = a + n := by simp [s]
  have hShiftPos : 0 < (s + n).re := by
    rw [hShiftRe]
    have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hNormShift : ‖Complex.Gamma (s + n)‖ ≤ Real.Gamma (a + n) := by
    simpa [hShiftRe] using Complex.Gamma.norm_le_Gamma_re hShiftPos
  have hTwo : (2 : ℝ) ≤ a + n := by
    have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hUpper : a + n ≤ (n : ℝ) := by linarith
  have hNtwo : (2 : ℝ) ≤ n := by
    exact_mod_cast (show 2 ≤ n by omega)
  have hGammaMono : Real.Gamma (a + n) ≤ Real.Gamma n :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hTwo hNtwo hUpper
  have hGammaNat : Real.Gamma n = (Nat.factorial (n - 1) : ℝ) := by
    have hn0 : n ≠ 0 := Nat.ne_of_gt (by omega : 0 < n)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simpa using Real.Gamma_nat_eq_factorial m
  calc
    |t| ^ n * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖
        ≤ ‖∏ j ∈ Finset.range n, (s + (j : ℂ))‖ * ‖Complex.Gamma s‖ := by
          simpa [s] using mul_le_mul_of_nonneg_right hProd (norm_nonneg _)
    _ = ‖Complex.Gamma (s + n)‖ := hNormRec.symm
    _ ≤ Real.Gamma (a + n) := hNormShift
    _ ≤ Real.Gamma n := hGammaMono
    _ = (Nat.factorial (n - 1) : ℝ) := hGammaNat

/-- Division form of `typeII_Gamma_vertical_decay`, convenient for tail estimates. -/
theorem typeII_Gamma_norm_le_inv_pow (n : ℕ) (hn : 3 ≤ n)
    {a t : ℝ} (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ))
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
      (Nat.factorial (n - 1) : ℝ) / |t| ^ n := by
  have htPos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  apply (le_div_iff₀ (pow_pos htPos n)).2
  simpa [mul_comm] using typeII_Gamma_vertical_decay n hn haLower haUpper

/-- A uniform bound on the compact central part of the Type-II Gamma strip. -/
theorem typeII_Gamma_norm_le_fourteen {a t : ℝ}
    (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 14 := by
  let s : ℂ := (a : ℂ) + (t : ℂ) * I
  have hsFactor : ∀ (j : ℕ), j < 3 → s + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have hRe := congrArg Complex.re hzero
    simp [s] at hRe
    interval_cases j <;> norm_num at hRe ⊢ <;> linarith
  have hRec := Gamma_add_nat_eq_prod_mul s (3 : ℕ) hsFactor
  have hShiftRe : (s + 3).re = a + 3 := by simp [s]
  have hShiftPos : 0 < (s + 3).re := by rw [hShiftRe]; linarith
  have hNormShift : ‖Complex.Gamma (s + 3)‖ ≤ Real.Gamma (a + 3) := by
    simpa [hShiftRe] using Complex.Gamma.norm_le_Gamma_re hShiftPos
  have hTwo : (2 : ℝ) ≤ a + 3 := by linarith
  have hThree : a + 3 ≤ (3 : ℝ) := by linarith
  have hGammaMono : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn hTwo (by norm_num) hThree
  have hGammaThree : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 using 1
    all_goals norm_num
  have hShift : ‖Complex.Gamma (s + 3)‖ ≤ 2 :=
    hNormShift.trans (hGammaMono.trans_eq hGammaThree)
  have h0 : (1 / 5 : ℝ) ≤ ‖s‖ := by
    calc
      (1 / 5 : ℝ) ≤ |a| := by rw [abs_of_neg (by linarith)]; linarith
      _ = |s.re| := by simp [s]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have h1 : (1 / 2 : ℝ) ≤ ‖s + 1‖ := by
    calc
      (1 / 2 : ℝ) ≤ |(s + 1).re| := by
        simp [s, abs_of_nonneg (by linarith : 0 ≤ a + 1)]
        linarith
      _ ≤ ‖s + 1‖ := Complex.abs_re_le_norm (s + 1)
  have h2 : (3 / 2 : ℝ) ≤ ‖s + 2‖ := by
    calc
      (3 / 2 : ℝ) ≤ |(s + 2).re| := by
        simp [s, abs_of_nonneg (by linarith : 0 ≤ a + 2)]
        linarith
      _ ≤ ‖s + 2‖ := Complex.abs_re_le_norm (s + 2)
  have hProd : (3 / 20 : ℝ) ≤
      ‖∏ j ∈ Finset.range 3, (s + (j : ℂ))‖ := by
    rw [norm_prod]
    norm_num [Finset.prod_range_succ]
    have h01 : (1 / 10 : ℝ) ≤ ‖s‖ * ‖s + 1‖ := by
      calc
        (1 / 10 : ℝ) = (1 / 5 : ℝ) * (1 / 2 : ℝ) := by norm_num
        _ ≤ ‖s‖ * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h0 (by norm_num)
        _ ≤ ‖s‖ * ‖s + 1‖ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
    have h012 : (3 / 20 : ℝ) ≤ (‖s‖ * ‖s + 1‖) * ‖s + 2‖ := by
      calc
        (3 / 20 : ℝ) = (1 / 10 : ℝ) * (3 / 2 : ℝ) := by norm_num
        _ ≤ (‖s‖ * ‖s + 1‖) * (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h01 (by norm_num)
        _ ≤ (‖s‖ * ‖s + 1‖) * ‖s + 2‖ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
    simpa [mul_assoc] using h012
  have hNormRec :
      ‖Complex.Gamma (s + 3)‖ =
        ‖∏ j ∈ Finset.range 3, (s + (j : ℂ))‖ * ‖Complex.Gamma s‖ := by
    have hRec' : Complex.Gamma (s + 3) =
        (∏ j ∈ Finset.range 3, (s + (j : ℂ))) * Complex.Gamma s := by
      simpa using hRec
    rw [hRec', norm_mul]
  rw [hNormRec] at hShift
  have hGammaNonneg := norm_nonneg (Complex.Gamma s)
  have hGap := mul_nonneg (sub_nonneg.mpr hProd) hGammaNonneg
  nlinarith

/-- Gamma is continuous along every horizontal line in the Type-II contour strip. -/
theorem continuous_typeII_Gamma_horizontal {a : ℝ}
    (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hNoPole : ∀ m : ℕ, (a : ℂ) + (t : ℂ) * I ≠ -m := by
    intro m hm
    have hRe := congrArg Complex.re hm
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_self, add_zero, neg_re, natCast_re] at hRe
    by_cases hm0 : m = 0
    · subst m
      norm_num at hRe
      linarith
    · have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hm0)
      linarith
  have hInner : ContinuousAt (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) t := by
    fun_prop
  exact ContinuousAt.comp'
    (Complex.differentiableAt_Gamma _ hNoPole).continuousAt hInner

set_option maxHeartbeats 800000 in
/-- The Gamma factor itself is integrable on every horizontal line in the Type-II strip. -/
theorem integrable_typeII_Gamma_horizontal {a : ℝ}
    (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    MeasureTheory.Integrable
      (fun t : ℝ => Complex.Gamma ((a : ℂ) + (t : ℂ) * I)) := by
  let f : ℝ → ℂ := fun t => Complex.Gamma ((a : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun t => 2 * t ^ (-(3 : ℝ))
  have hCont : Continuous f := by
    simpa [f] using continuous_typeII_Gamma_horizontal haLower haUpper
  have hGPos : MeasureTheory.IntegrableOn g (Set.Ioi (1 : ℝ)) := by
    exact (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  have hPos : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    apply MeasureTheory.Integrable.mono' hGPos hCont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 1 < t := ht
    have htPos : 0 < t := lt_trans zero_lt_one ht'
    have htAbs : 1 ≤ |t| := by
      rw [abs_of_pos htPos]
      exact ht'.le
    have hDecay := typeII_Gamma_norm_le_inv_pow 3 (by norm_num)
      haLower haUpper htAbs
    have hEq : (2 : ℝ) / t ^ 3 = 2 * t ^ (-(3 : ℝ)) := by
      simp [div_eq_mul_inv, Real.rpow_neg htPos.le]
    dsimp [g]
    rw [← hEq]
    norm_num at hDecay ⊢
    simpa [abs_of_pos htPos] using hDecay
  have hGNeg : MeasureTheory.IntegrableOn (fun t : ℝ => g (-t)) (Set.Iio (-1 : ℝ)) := by
    have hSource : MeasureTheory.IntegrableOn g (Set.Ioi (-(-1 : ℝ))) := by
      simpa using hGPos
    exact hSource.comp_neg_Iio
  have hNeg : MeasureTheory.IntegrableOn f (Set.Iio (-1 : ℝ)) := by
    apply MeasureTheory.Integrable.mono' hGNeg hCont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with t ht
    change t < -1 at ht
    have htAbs : 1 ≤ |t| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have hDecay := typeII_Gamma_norm_le_inv_pow 3 (by norm_num)
      haLower haUpper htAbs
    have htNegPos : 0 < -t := by linarith
    have htNeg : t < 0 := by linarith
    have hAbs : |t| = -t := abs_of_neg htNeg
    have hEq : (2 : ℝ) / |t| ^ 3 = g (-t) := by
      dsimp [g]
      rw [hAbs]
      simp [div_eq_mul_inv, Real.rpow_neg htNegPos.le]
    rw [← hEq]
    norm_num at hDecay ⊢
    exact hDecay
  have hMid : MeasureTheory.IntegrableOn f (Set.Icc (-1 : ℝ) 1) :=
    hCont.continuousOn.integrableOn_Icc
  have hLeft : MeasureTheory.IntegrableOn f (Set.Iic (1 : ℝ)) := by
    have hNegClosed : MeasureTheory.IntegrableOn f (Set.Iic (-1 : ℝ)) :=
      (integrableOn_Iic_iff_integrableOn_Iio).mpr hNeg
    have hUnion := MeasureTheory.integrableOn_union.2 ⟨hNegClosed, hMid⟩
    have hSet : Set.Iic (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 = Set.Iic 1 := by
      ext t
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
      constructor <;> intro h
      · rcases h with h | h <;> linarith
      · by_cases ht : t ≤ -1
        · exact Or.inl ht
        · exact Or.inr ⟨by linarith, h⟩
    rwa [hSet] at hUnion
  rw [← MeasureTheory.integrableOn_univ]
  have hAll := MeasureTheory.integrableOn_union.2 ⟨hLeft, hPos⟩
  have hSet : Set.Iic (1 : ℝ) ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt t 1
  rwa [hSet] at hAll

set_option maxHeartbeats 800000 in
/-- Multiplying the horizontal Gamma factor by a linear ordinate weight
preserves whole-line integrability. -/
theorem integrable_one_add_abs_mul_typeII_Gamma_horizontal {a : ℝ}
    (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    MeasureTheory.Integrable (fun t : ℝ =>
      ((1 + |t| : ℝ) : ℂ) * Complex.Gamma ((a : ℂ) + (t : ℂ) * I)) := by
  let f : ℝ → ℂ := fun t =>
    ((1 + |t| : ℝ) : ℂ) * Complex.Gamma ((a : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun t => 4 * t ^ (-(2 : ℝ))
  have hCont : Continuous f := by
    dsimp [f]
    have hScalar : Continuous (fun t : ℝ => ((1 + |t| : ℝ) : ℂ)) := by
      fun_prop
    exact hScalar.mul (continuous_typeII_Gamma_horizontal haLower haUpper)
  have hGPos : MeasureTheory.IntegrableOn g (Set.Ioi (1 : ℝ)) := by
    exact (integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num) (by norm_num)).const_mul 4
  have hPos : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    apply MeasureTheory.Integrable.mono' hGPos hCont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have htPos : 0 < t := by linarith
    have htAbs : 1 ≤ |t| := by simpa [abs_of_pos htPos] using ht.le
    have hDecay := typeII_Gamma_norm_le_inv_pow 3 (by norm_num)
      haLower haUpper htAbs
    have hWeight : 1 + |t| ≤ 2 * |t| := by linarith
    have hNormGamma : 0 ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
    have hProduct :
        (1 + |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
          4 / |t| ^ 2 := by
      calc
        (1 + |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ :=
              mul_le_mul_of_nonneg_right hWeight hNormGamma
        _ ≤ (2 * |t|) * (2 / |t| ^ 3) := by
              apply mul_le_mul_of_nonneg_left
              · norm_num at hDecay ⊢
                exact hDecay
              · positivity
        _ = 4 / |t| ^ 2 := by
              field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one htAbs)]
              ring
    have hEq : 4 / |t| ^ 2 = g t := by
      dsimp [g]
      rw [abs_of_pos htPos]
      simp [div_eq_mul_inv, Real.rpow_neg htPos.le]
    rw [← hEq]
    change ‖((1 + |t| : ℝ) : ℂ) *
      Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 4 / |t| ^ 2
    rw [norm_mul]
    have hScalarNorm : ‖((1 + |t| : ℝ) : ℂ)‖ = 1 + |t| := by
      change ‖Complex.ofReal (1 + |t|)‖ = 1 + |t|
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 + |t| : ℝ))]
    rw [hScalarNorm]
    exact hProduct
  have hGNeg : MeasureTheory.IntegrableOn (fun t : ℝ => g (-t)) (Set.Iio (-1 : ℝ)) := by
    have hSource : MeasureTheory.IntegrableOn g (Set.Ioi (-(-1 : ℝ))) := by
      simpa using hGPos
    exact hSource.comp_neg_Iio
  have hNeg : MeasureTheory.IntegrableOn f (Set.Iio (-1 : ℝ)) := by
    apply MeasureTheory.Integrable.mono' hGNeg hCont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with t ht
    change t < -1 at ht
    have htNeg : t < 0 := by linarith
    have htAbs : 1 ≤ |t| := by
      rw [abs_of_neg htNeg]
      linarith
    have hDecay := typeII_Gamma_norm_le_inv_pow 3 (by norm_num)
      haLower haUpper htAbs
    have hWeight : 1 + |t| ≤ 2 * |t| := by linarith
    have hNormGamma : 0 ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
    have hProduct :
        (1 + |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
          4 / |t| ^ 2 := by
      calc
        (1 + |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * |t|) * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ :=
              mul_le_mul_of_nonneg_right hWeight hNormGamma
        _ ≤ (2 * |t|) * (2 / |t| ^ 3) := by
              apply mul_le_mul_of_nonneg_left
              · norm_num at hDecay ⊢
                exact hDecay
              · positivity
        _ = 4 / |t| ^ 2 := by
              field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one htAbs)]
              ring
    have htNegPos : 0 < -t := by linarith
    have hEq : 4 / |t| ^ 2 = g (-t) := by
      dsimp [g]
      rw [abs_of_neg htNeg]
      simp [div_eq_mul_inv, Real.rpow_neg htNegPos.le]
    rw [← hEq]
    change ‖((1 + |t| : ℝ) : ℂ) *
      Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 4 / |t| ^ 2
    rw [norm_mul]
    have hScalarNorm : ‖((1 + |t| : ℝ) : ℂ)‖ = 1 + |t| := by
      change ‖Complex.ofReal (1 + |t|)‖ = 1 + |t|
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 + |t| : ℝ))]
    rw [hScalarNorm]
    exact hProduct
  have hMid : MeasureTheory.IntegrableOn f (Set.Icc (-1 : ℝ) 1) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : MeasureTheory.IntegrableOn f (Set.Iic (-1 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hNeg
  have hLeftUnion := MeasureTheory.integrableOn_union.2 ⟨hNegClosed, hMid⟩
  have hLeftSet : Set.Iic (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 = Set.Iic 1 := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases ht : t ≤ -1
      · exact Or.inl ht
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeftUnion
  rw [← MeasureTheory.integrableOn_univ]
  have hAll := MeasureTheory.integrableOn_union.2 ⟨hLeftUnion, hPos⟩
  have hAllSet : Set.Iic (1 : ℝ) ∪ Set.Ioi 1 = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt t 1
  rwa [hAllSet] at hAll

end RiemannZeta.GuthMaynard
