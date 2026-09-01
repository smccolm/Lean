import GafniTao.FordTentWeights
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Ford's tent Fourier coefficients

The removable zero frequency is represented with `Real.sinc`.  Thus the
coefficient below is literally

`w * sinc (pi * n * w)^2`,

including its value `w` at `n = 0`.
-/

open Real

namespace GafniTao

noncomputable section

/-- The continuous complex-valued version of Ford's periodic tent. -/
def fordTentCircle (w : ℝ) : C(UnitAddCircle, ℂ) where
  toFun x := ((max 0 (1 - ‖x‖ / w) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

@[simp]
theorem fordTentCircle_coe (x w : ℝ) :
    fordTentCircle w (x : UnitAddCircle) = (fordTent x w : ℂ) := by
  rfl

/-- The exact Fourier coefficient occurring in Ford's tent expansion. -/
def fordTentFourierCoefficient (w : ℝ) (n : ℤ) : ℂ :=
  ((w * Real.sinc (Real.pi * (n : ℝ) * w) ^ 2 : ℝ) : ℂ)

@[simp]
theorem fordTentFourierCoefficient_zero (w : ℝ) :
    fordTentFourierCoefficient w 0 = w := by
  simp [fordTentFourierCoefficient]

theorem fordTentFourierCoefficient_of_ne_zero
    {w : ℝ} {n : ℤ} (hw : w ≠ 0) (hn : n ≠ 0) :
    fordTentFourierCoefficient w n =
      (((Real.sin (Real.pi * (n : ℝ) * w)) ^ 2 /
        (Real.pi ^ 2 * w * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have harg : Real.pi * (n : ℝ) * w ≠ 0 :=
    mul_ne_zero (mul_ne_zero Real.pi_ne_zero hnR) hw
  simp only [fordTentFourierCoefficient, Real.sinc_of_ne_zero harg]
  norm_cast
  field_simp [Real.pi_ne_zero, hnR, hw]
  push_cast
  ring

theorem summable_fordTentFourierCoefficient {w : ℝ} (hw : 0 < w) :
    Summable (fordTentFourierCoefficient w) := by
  let C : ℝ := 1 / (Real.pi ^ 2 * w)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmajor : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left C
  refine hmajor.of_norm_bounded_eventually ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [fordTentFourierCoefficient_of_ne_zero hw.ne' hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hden : 0 < Real.pi ^ 2 * w * (n : ℝ) ^ 2 := by positivity
  have hsin : Real.sin (Real.pi * (n : ℝ) * w) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin (Real.pi * (n : ℝ) * w)),
      Real.neg_one_le_sin (Real.pi * (n : ℝ) * w),
      Real.sin_le_one (Real.pi * (n : ℝ) * w)]
  rw [Complex.norm_real]
  have hfrac : 0 ≤
      Real.sin (Real.pi * (n : ℝ) * w) ^ 2 /
        (Real.pi ^ 2 * w * (n : ℝ) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hfrac]
  dsimp [C]
  rw [one_div, inv_mul_eq_div]
  have hrhs :
      1 / (n : ℝ) ^ 2 / (Real.pi ^ 2 * w) =
        1 / (Real.pi ^ 2 * w * (n : ℝ) ^ 2) := by
    field_simp [Real.pi_ne_zero, hw.ne', hnR]
  rw [hrhs]
  exact (div_le_div_iff_of_pos_right hden).2 hsin

/-- The elementary integration-by-parts identity underlying the nonzero
Fourier coefficients of the tent. -/
theorem ford_integral_linear_tent_cos
    {w a : ℝ} (hw : w ≠ 0) (ha : a ≠ 0) :
    (∫ x in (0 : ℝ)..w, (1 - x / w) * Real.cos (a * x)) =
      (1 - Real.cos (a * w)) / (w * a ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    (1 - x / w) * Real.sin (a * x) / a -
      Real.cos (a * x) / (w * a ^ 2)
  have hF : ∀ x : ℝ,
      HasDerivAt F ((1 - x / w) * Real.cos (a * x)) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => 1 - y / w) (-1 / w) x := by
      convert (hasDerivAt_const x 1).sub ((hasDerivAt_id x).div_const w) using 1
      all_goals simp [div_eq_mul_inv]
    have harg : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (Real.cos (a * x) * a) x :=
      (Real.hasDerivAt_sin (a * x)).comp x harg
    have hcos : HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-Real.sin (a * x) * a) x :=
      (Real.hasDerivAt_cos (a * x)).comp x harg
    dsimp [F]
    convert ((hlin.mul hsin).div_const a).sub
      (hcos.div_const (w * a ^ 2)) using 1
    all_goals
      field_simp [hw, ha]
      ring
  rw [intervalIntegral.integral_deriv_eq_sub' F
    (funext fun x => (hF x).deriv) (fun x _ => (hF x).differentiableAt)]
  · dsimp [F]
    simp [hw]
    field_simp [hw, ha]
    ring
  · fun_prop

theorem fordAdditiveCharacter_pair_eq_cos (x : ℝ) :
    fordAdditiveCharacter x + fordAdditiveCharacter (-x) =
      ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  unfold fordAdditiveCharacter
  have hpos :
      2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
        ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hneg :
      2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) =
        ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  apply Complex.ext <;> simp <;> ring

/-- The Fourier integral of the even tent reduces exactly to its cosine
integral on the positive half interval. -/
theorem ford_integral_symmetric_tent_character
    {w : ℝ} (hw : 0 < w) (n : ℤ) :
    (∫ x in -w..w,
        ((1 - |x| / w : ℝ) : ℂ) *
          fordAdditiveCharacter (-((n : ℝ) * x))) =
      ((2 * ∫ x in (0 : ℝ)..w,
          (1 - x / w) * Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    ((1 - |x| / w : ℝ) : ℂ) * fordAdditiveCharacter (-((n : ℝ) * x))
  have hchar : Continuous fordAdditiveCharacter := by
    unfold fordAdditiveCharacter
    fun_prop
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hf : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    exact hfcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf (-w) 0) (hf 0 w)]
  have hneg :
      (∫ x in (0 : ℝ)..w, f (-x)) = ∫ x in -w..0, f x := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  have hfneg : IntervalIntegrable (fun x : ℝ => f (-x))
      MeasureTheory.volume 0 w := by
    simpa only [Function.comp_apply] using
      (hfcont.comp continuous_neg).intervalIntegrable (0 : ℝ) w
  rw [← hneg, ← intervalIntegral.integral_add
    hfneg (hf 0 w)]
  calc
    (∫ x in (0 : ℝ)..w, f (-x) + f x) =
        ∫ x in (0 : ℝ)..w,
          ((2 * ((1 - x / w) * Real.cos (2 * Real.pi * (n : ℝ) * x)) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by
        rcases Set.mem_uIcc.mp hx with h | h
        · exact h.1
        · linarith
      simp only [f, abs_neg, abs_of_nonneg hx0]
      rw [show -((n : ℝ) * -x) = (n : ℝ) * x by ring]
      rw [← mul_add]
      rw [fordAdditiveCharacter_pair_eq_cos]
      push_cast
      ring_nf
    _ = ((∫ x in (0 : ℝ)..w,
          2 * ((1 - x / w) * Real.cos (2 * Real.pi * (n : ℝ) * x)) : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    _ = ((2 * ∫ x in (0 : ℝ)..w,
          (1 - x / w) * Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul]

/-- The exact compactly supported Fourier transform of the tent, with the
removable zero frequency included. -/
theorem ford_integral_symmetric_tent_character_eq_coefficient
    {w : ℝ} (hw : 0 < w) (n : ℤ) :
    (∫ x in -w..w,
        ((1 - |x| / w : ℝ) : ℂ) *
          fordAdditiveCharacter (-((n : ℝ) * x))) =
      fordTentFourierCoefficient w n := by
  rw [ford_integral_symmetric_tent_character hw n]
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_zero,
      fordTentFourierCoefficient_zero]
    have hlinear :
        (∫ x in (0 : ℝ)..w, (1 - x / w)) = w / 2 := by
      have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
          MeasureTheory.volume 0 w := continuous_const.intervalIntegrable 0 w
      have hquot : IntervalIntegrable (fun x : ℝ => x / w)
          MeasureTheory.volume 0 w :=
        (by fun_prop : Continuous fun x : ℝ => x / w).intervalIntegrable 0 w
      rw [intervalIntegral.integral_sub hone hquot]
      simp only [intervalIntegral.integral_const, intervalIntegral.integral_div,
        integral_id, sub_zero, smul_eq_mul, pow_succ]
      field_simp [hw.ne']
      ring
    simp only [mul_one]
    rw [hlinear]
    norm_cast
    ring
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have ha : 2 * Real.pi * (n : ℝ) ≠ 0 := by
      positivity
    rw [ford_integral_linear_tent_cos hw.ne' ha]
    rw [fordTentFourierCoefficient_of_ne_zero hw.ne' hn]
    norm_cast
    have harg :
        (2 * Real.pi * (n : ℝ)) * w =
          2 * (Real.pi * (n : ℝ) * w) := by ring
    rw [harg]
    have htrig :
        1 - Real.cos (2 * (Real.pi * (n : ℝ) * w)) =
          2 * Real.sin (Real.pi * (n : ℝ) * w) ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (n : ℝ) * w)]
    rw [htrig]
    field_simp [Real.pi_ne_zero, hw.ne', hnR]
    push_cast
    ring_nf

private def fordTentCharacterIntegrand (w : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  ((max 0 (1 - |x| / w) : ℝ) : ℂ) *
    fordAdditiveCharacter (-((n : ℝ) * x))

private theorem support_fordTentCharacterIntegrand_subset
    {w : ℝ} (hw : 0 < w) (n : ℤ) :
    Function.support (fordTentCharacterIntegrand w n) ⊆ Set.Ioc (-w) w := by
  intro x hx
  have hmul :
      ((max 0 (1 - |x| / w) : ℝ) : ℂ) *
          fordAdditiveCharacter (-((n : ℝ) * x)) ≠ 0 := hx
  have htentC : ((max 0 (1 - |x| / w) : ℝ) : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp hmul).1
  have htent : max 0 (1 - |x| / w) ≠ 0 := by exact_mod_cast htentC
  have hlinear : 0 < 1 - |x| / w := by
    by_contra hnot
    have hle : 1 - |x| / w ≤ 0 := le_of_not_gt hnot
    apply htent
    exact max_eq_left hle
  have habsdiv : |x| / w < 1 := by linarith
  have habs : |x| < w := (div_lt_one hw).mp habsdiv
  exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩

private theorem ford_fourier_coe_eq_character (n : ℤ) (x : ℝ) :
    @fourier (1 : ℝ) (-n) (x : UnitAddCircle) =
      fordAdditiveCharacter (-((n : ℝ) * x)) := by
  rw [fourier_coe_apply]
  unfold fordAdditiveCharacter
  congr 1
  push_cast
  ring

/-- The coefficient defined above is literally Mathlib's Fourier coefficient
of the periodic tent. -/
theorem fourierCoeff_fordTentCircle
    {w : ℝ} (hw : 0 < w) (hwHalf : w ≤ 1 / 2) (n : ℤ) :
    fourierCoeff (fordTentCircle w) n =
      fordTentFourierCoefficient w n := by
  rw [fourierCoeff_eq_intervalIntegral (fordTentCircle w) n (-1 / 2)]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, one_smul]
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  have hlarge :
      (∫ x in (-1 / 2 : ℝ)..1 / 2, fordTentCharacterIntegrand w n x) =
        ∫ x : ℝ, fordTentCharacterIntegrand w n x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hsmall := support_fordTentCharacterIntegrand_subset hw n hx
    constructor <;> linarith [hsmall.1, hsmall.2]
  have hsmall :
      (∫ x in -w..w, fordTentCharacterIntegrand w n x) =
        ∫ x : ℝ, fordTentCharacterIntegrand w n x :=
    intervalIntegral.integral_eq_integral_of_support_subset
      (support_fordTentCharacterIntegrand_subset hw n)
  calc
    (∫ x in (-1 / 2 : ℝ)..1 / 2,
        @fourier (1 : ℝ) (-n) x • fordTentCircle w x) =
        ∫ x in (-1 / 2 : ℝ)..1 / 2, fordTentCharacterIntegrand w n x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxabs : |x| ≤ (1 : ℝ) / 2 := by
        rcases Set.mem_uIcc.mp hx with h | h
        · apply abs_le.mpr
          constructor <;> linarith
        · exfalso
          linarith
      have hnorm : ‖(x : UnitAddCircle)‖ = |x| :=
        (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ))
          (by norm_num : (1 : ℝ) ≠ 0)).2 (by simpa using hxabs)
      simp only [fordTentCircle_coe]
      rw [ford_fourier_coe_eq_character]
      simp only [smul_eq_mul, fordTentCharacterIntegrand, fordTent, hnorm]
      ring
    _ = ∫ x in -w..w, fordTentCharacterIntegrand w n x := hlarge.trans hsmall.symm
    _ = ∫ x in -w..w,
        ((1 - |x| / w : ℝ) : ℂ) *
          fordAdditiveCharacter (-((n : ℝ) * x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxabs : |x| ≤ w := by
        rcases Set.mem_uIcc.mp hx with h | h
        · exact abs_le.mpr h
        · linarith
      simp only [fordTentCharacterIntegrand]
      rw [max_eq_right]
      exact sub_nonneg.mpr ((div_le_one hw).mpr hxabs)
    _ = fordTentFourierCoefficient w n :=
      ford_integral_symmetric_tent_character_eq_coefficient hw n

/-- The exact tent Fourier series, evaluated at a real representative. -/
theorem hasSum_fordTentFourierSeries
    {w : ℝ} (hw : 0 < w) (hwHalf : w ≤ 1 / 2) (y : ℝ) :
    HasSum
      (fun n : ℤ => fordTentFourierCoefficient w n *
        fordAdditiveCharacter ((n : ℝ) * y))
      (fordTent y w : ℂ) := by
  have hcoeff : Summable (fourierCoeff (fordTentCircle w)) := by
    refine (summable_fordTentFourierCoefficient hw).congr ?_
    intro n
    exact (fourierCoeff_fordTentCircle hw hwHalf n).symm
  have hsum := has_pointwise_sum_fourier_series_of_summable hcoeff
    (y : UnitAddCircle)
  convert hsum using 1
  · ext n
    rw [fourierCoeff_fordTentCircle hw hwHalf]
    simp only [smul_eq_mul]
    rw [fourier_coe_apply]
    unfold fordAdditiveCharacter
    congr 2
    push_cast
    ring

/-- Ford's `f_j(n)` is exactly the tent coefficient multiplied by
`pi^2 r M^j / 2`, including at `n = 0`. -/
theorem fordSincSquareWeight_eq_tentCoefficient
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) (n : ℤ) :
    (fordSincSquareWeight r M j (n : ℝ) : ℂ) =
      ((Real.pi ^ 2 * ((r * M ^ j : ℕ) : ℝ) / 2 : ℝ) : ℂ) *
        fordTentFourierCoefficient
          (1 / (2 * ((r * M ^ j : ℕ) : ℝ))) n := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hA : A ≠ 0 := by
    dsimp [A]
    positivity
  unfold fordSincSquareWeight fordTentFourierCoefficient
  norm_cast
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hAeq : A = (r : ℝ) * (M : ℝ) ^ j := by
    simp [A]
  rw [← hAeq]
  change (Real.pi / 2 * Real.sinc (Real.pi * (n : ℝ) / (2 * A))) ^ 2 =
    (Real.pi ^ 2 * A / 2) *
      ((1 / (2 * A)) *
        Real.sinc (Real.pi * (n : ℝ) * (1 / (2 * A))) ^ 2)
  field_simp [hA]

/-- Ford's displayed Fourier expansion of the sinc-square weight.  The
statement is a `HasSum`, so its convergence and its value are both explicit. -/
theorem hasSum_fordSincSquareWeight_character
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) (y : ℝ) :
    HasSum
      (fun n : ℤ => (fordSincSquareWeight r M j (n : ℝ) : ℂ) *
        fordAdditiveCharacter ((n : ℝ) * y))
      (((Real.pi ^ 2 * ((r * M ^ j : ℕ) : ℝ) / 2) *
        fordTent y (1 / (2 * ((r * M ^ j : ℕ) : ℝ))) : ℝ) : ℂ) := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hAge : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity : r * M ^ j ≠ 0)
  have hw : 0 < 1 / (2 * A) := by positivity
  have hwHalf : 1 / (2 * A) ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity)).2
    linarith
  have hs := hasSum_fordTentFourierSeries hw hwHalf y
  have hscaled := hs.mul_left (((Real.pi ^ 2 * A / 2 : ℝ) : ℂ))
  convert hscaled using 1
  · ext n
    rw [← mul_assoc]
    rw [← fordSincSquareWeight_eq_tentCoefficient hr hM n]
  · dsimp [A]
    push_cast
    ring

theorem tsum_fordSincSquareWeight_character
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) (y : ℝ) :
    ∑' n : ℤ, (fordSincSquareWeight r M j (n : ℝ) : ℂ) *
        fordAdditiveCharacter ((n : ℝ) * y) =
      (((Real.pi ^ 2 * ((r * M ^ j : ℕ) : ℝ) / 2) *
        fordTent y (1 / (2 * ((r * M ^ j : ℕ) : ℝ))) : ℝ) : ℂ) :=
  (hasSum_fordSincSquareWeight_character hr hM y).tsum_eq

#print axioms fordTentFourierCoefficient_of_ne_zero
#print axioms summable_fordTentFourierCoefficient
#print axioms ford_integral_linear_tent_cos
#print axioms fordAdditiveCharacter_pair_eq_cos
#print axioms ford_integral_symmetric_tent_character
#print axioms ford_integral_symmetric_tent_character_eq_coefficient
#print axioms fourierCoeff_fordTentCircle
#print axioms hasSum_fordTentFourierSeries
#print axioms fordSincSquareWeight_eq_tentCoefficient
#print axioms hasSum_fordSincSquareWeight_character
#print axioms tsum_fordSincSquareWeight_character

end

end GafniTao
