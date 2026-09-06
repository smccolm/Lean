import GafniTao.Pintz2023Equation416

/-!
# Pintz (2023), powered-block upper scale

The source block selected in equation (4.16) has length `2^q U^h` with
`q < h`.  This file derives the coarse but uniform upper bound needed to
absorb the moving-pole residue in equation (4.20).  Both alternatives in the
source power choice are retained.
-/

namespace GafniTao

noncomputable section

/-- The perturbed critical exponent is strictly below one. -/
theorem pintz2023EllThreshold_lt_one
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilonSmall : 6 * (ell : ℝ) * epsilon < 1 / 15) :
    pintz2023EllThreshold eta epsilon ell < 1 := by
  have hbound :=
    pintz2023EllThreshold_lt_five_thirds hcell hepsilonSmall
  have hell : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
  have hellPos : (0 : ℝ) < ell := by positivity
  have hfive : 5 / (3 * (ell : ℝ)) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < 3 * (ell : ℝ))]
    nlinarith
  exact hbound.trans hfive

/-- The upper endpoint of the nonsquare power window is below one. -/
theorem pintz2023EllPowerWindowUpper_lt_one
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilonUpper : epsilon ≤ 1)
    (hepsilonSmall : 6 * (ell : ℝ) * epsilon < 1 / 15) :
    pintz2023EllPowerWindowUpper eta epsilon ell < 1 := by
  have hell : (3 : ℝ) ≤ ell := by exact_mod_cast hcell.2.1
  have hellPos : (0 : ℝ) < ell := by positivity
  have hthreshold :=
    pintz2023EllThreshold_lt_five_thirds hcell hepsilonSmall
  have hthresholdScaled :
      pintz2023EllThreshold eta epsilon ell * (ell : ℝ) < 5 / 3 := by
    have hmul := mul_lt_mul_of_pos_right hthreshold hellPos
    convert hmul using 1
    all_goals field_simp
  have hscaled :
      pintz2023EllPowerWindowUpper eta epsilon ell * (ell : ℝ) =
        (3 / 2 : ℝ) *
            (pintz2023EllThreshold eta epsilon ell * (ell : ℝ)) +
          epsilon / 20 := by
    unfold pintz2023EllPowerWindowUpper
    field_simp [hellPos.ne']
  have hscaledLt :
      pintz2023EllPowerWindowUpper eta epsilon ell * (ell : ℝ) <
        1 * (ell : ℝ) := by
    rw [hscaled]
    nlinarith
  nlinarith

/-- Either source power choice places `h u` strictly below two. -/
theorem pintz2023_power_choice_log_scale_lt_two
    {eta epsilon u : ℝ} {k ell h : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilonUpper : epsilon ≤ 1)
    (hepsilonSmall : 6 * (ell : ℝ) * epsilon < 1 / 15)
    (huUpper : u < pintz2023EllThreshold eta epsilon ell)
    (hcase : h = 2 ∨
      (h : ℝ) * u < pintz2023EllPowerWindowUpper eta epsilon ell) :
    (h : ℝ) * u < 2 := by
  rcases hcase with rfl | hwindow
  · have hthreshold :=
      pintz2023EllThreshold_lt_one hcell hepsilonSmall
    norm_num
    linarith
  · exact hwindow.trans
      (pintz2023EllPowerWindowUpper_lt_one hcell hepsilonUpper
        hepsilonSmall |>.trans (by norm_num))

/-- A logarithmic upper scale and the bounded dyadic factor imply the
physical powered block is below `T^3`. -/
theorem pintz2023_powered_dyadic_cast_lt_cube
    {T : ℝ} {U q h : ℕ}
    (hT : 1 < T) (hU : 0 < U) (hq : q < h)
    (hScale : (h : ℝ) * pintz2023LogScale T U < 2)
    (hDyadic : (2 : ℝ) ^ (h : ℝ) < T) :
    ((2 ^ q * U ^ h : ℕ) : ℝ) < T ^ (3 : ℝ) := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hUReal : (0 : ℝ) < U := by exact_mod_cast hU
  have hlog :
      (h : ℝ) * Real.log (U : ℝ) < 2 * Real.log T := by
    unfold pintz2023LogScale at hScale
    have hmul := mul_lt_mul_of_pos_right hScale hlogT
    field_simp [hlogT.ne'] at hmul
    nlinarith
  have hUpowPos : (0 : ℝ) < (U : ℝ) ^ h := pow_pos hUReal h
  have hTsqPos : (0 : ℝ) < T ^ (2 : ℕ) := pow_pos hTPos 2
  have hUpow : (U : ℝ) ^ h < T ^ (2 : ℕ) := by
    rw [← Real.log_lt_log_iff hUpowPos hTsqPos]
    rw [Real.log_pow, Real.log_pow]
    norm_num
    simpa [mul_comm] using hlog
  have hqle : q ≤ h := Nat.le_of_lt hq
  have htwo : (1 : ℝ) ≤ 2 := by norm_num
  have hDyadicQ : (2 : ℝ) ^ q < T :=
    (pow_le_pow_right₀ htwo hqle).trans_lt
      (by simpa only [Real.rpow_natCast] using hDyadic)
  have hprod :
      ((2 ^ q * U ^ h : ℕ) : ℝ) < T * T ^ (2 : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact (mul_lt_mul_of_pos_right hDyadicQ (pow_pos hUReal h)).trans_le
      (mul_le_mul_of_nonneg_left hUpow.le hTPos.le)
  calc
    ((2 ^ q * U ^ h : ℕ) : ℝ) < T * T ^ (2 : ℕ) := hprod
    _ = T ^ (3 : ℕ) := by ring_nf
    _ = T ^ (3 : ℝ) := (Real.rpow_natCast T 3).symm

/-- Uniform source form: the bounded power selected after (4.15) makes every
second dyadic block smaller than `T^3`. -/
theorem eventually_pintz2023_powered_dyadic_cast_lt_cube
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {U q h : ℕ}, 0 < U → q < h →
        (h : ℝ) < 20 / data.epsilon →
        pintz2023LogScale T U <
          pintz2023EllThreshold eta data.epsilon ell →
        (h = 2 ∨
          (h : ℝ) * pintz2023LogScale T U <
            pintz2023EllPowerWindowUpper eta data.epsilon ell) →
        ((2 ^ q * U ^ h : ℕ) : ℝ) < T ^ (3 : ℝ) := by
  have hfixed := eventually_two_rpow_lt_rpow
    (c := 20 / data.epsilon) (delta := (1 : ℝ)) (by norm_num)
  filter_upwards [hfixed, Filter.eventually_gt_atTop 1] with T hfixedT hT
  intro U q h hU hq hhBound huUpper hcase
  have hhScale : (h : ℝ) * pintz2023LogScale T U < 2 :=
    pintz2023_power_choice_log_scale_lt_two hcell data.epsilon_le_one
      data.power_smallness huUpper hcase
  have hDyadic : (2 : ℝ) ^ (h : ℝ) < T := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hhBound
    exact hpow.trans (by simpa using hfixedT)
  exact pintz2023_powered_dyadic_cast_lt_cube hT hU hq hhScale hDyadic

/-- The form used by the equation-(4.16) consumer.  Its recorded support
inequality supplies the upper logarithmic scale, including the fixed `2T`
factor and the perturbation reserve. -/
theorem eventually_pintz2023_source_powered_block_lt_cube
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {U q h : ℕ}, 0 < U → q < h →
        (h : ℝ) < 20 / data.epsilon →
        (U : ℝ) <
          (pintz2023SourceX T data.epsilon ell : ℝ) *
            (2 * T) ^
              pintz2023CriticalScaleExponent
                k eta data.epsilon →
        (h = 2 ∨
          (h : ℝ) * pintz2023LogScale T U <
            pintz2023EllPowerWindowUpper eta data.epsilon ell) →
        ((2 ^ q * U ^ h : ℕ) : ℝ) < T ^ (3 : ℝ) := by
  have hfactor := eventually_two_rpow_lt_rpow data.delta_pos
    (c := pintz2023CriticalScaleExponent k eta data.epsilon)
  have hcube :=
    eventually_pintz2023_powered_dyadic_cast_lt_cube hcell data
  filter_upwards [hfactor, hcube, Filter.eventually_gt_atTop 1] with
      T hfactorT hcubeT hT
  intro U q h hU hq hhBound hsupport hcase
  have huUpperReserve :
      pintz2023LogScale T U <
        data.epsilon / (10 * (ell : ℝ)) +
          pintz2023CriticalScaleExponent k eta data.epsilon +
            data.delta :=
    pintz2023_logScale_upper_of_support hT hU hfactorT hsupport
  have huUpper :
      pintz2023LogScale T U <
        pintz2023EllThreshold eta data.epsilon ell :=
    huUpperReserve.trans data.scale_separation
  exact hcubeT hU hq hhBound huUpper hcase

#print axioms pintz2023EllThreshold_lt_one
#print axioms pintz2023EllPowerWindowUpper_lt_one
#print axioms pintz2023_power_choice_log_scale_lt_two
#print axioms pintz2023_powered_dyadic_cast_lt_cube
#print axioms eventually_pintz2023_powered_dyadic_cast_lt_cube
#print axioms eventually_pintz2023_source_powered_block_lt_cube

end

end GafniTao
