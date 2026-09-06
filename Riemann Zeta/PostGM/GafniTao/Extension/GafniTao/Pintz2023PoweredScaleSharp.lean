import GafniTao.Pintz2023Equation419Shell

/-!
# Pintz (2023), sharp upper scales for the selected powered block

The square branch and the higher-power branch in equation (4.16) lead to
different final exponents.  This file preserves that split and absorbs only
the bounded dyadic factor `2^q` into an arbitrarily small positive power of
the physical height.
-/

open Filter

namespace GafniTao

noncomputable section

/-- A logarithmic upper bound for `U^h`, together with a separate bound for
the dyadic factor, gives the corresponding physical upper bound for
`2^q U^h`. -/
theorem pintz2023_powered_dyadic_cast_lt_rpow
    {T a delta : ℝ} {U q h : ℕ}
    (hT : 1 < T) (hU : 0 < U) (hq : q < h)
    (hScale : (h : ℝ) * pintz2023LogScale T U < a)
    (hDyadic : (2 : ℝ) ^ (h : ℝ) < T ^ delta) :
    ((2 ^ q * U ^ h : ℕ) : ℝ) < T ^ (a + delta) := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hUReal : (0 : ℝ) < U := by exact_mod_cast hU
  have hlog :
      (h : ℝ) * Real.log (U : ℝ) < a * Real.log T := by
    unfold pintz2023LogScale at hScale
    have hmul := mul_lt_mul_of_pos_right hScale hlogT
    field_simp [hlogT.ne'] at hmul
    nlinarith
  have hUpowPos : (0 : ℝ) < (U : ℝ) ^ h := pow_pos hUReal h
  have hTaPos : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos hTPos _
  have hUpow : (U : ℝ) ^ h < T ^ a := by
    rw [← Real.log_lt_log_iff hUpowPos hTaPos]
    rw [Real.log_pow, Real.log_rpow hTPos]
    simpa [mul_comm] using hlog
  have hqle : q ≤ h := Nat.le_of_lt hq
  have hDyadicQ : (2 : ℝ) ^ q < T ^ delta :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hqle).trans_lt
      (by simpa only [Real.rpow_natCast] using hDyadic)
  calc
    ((2 ^ q * U ^ h : ℕ) : ℝ) =
        (2 : ℝ) ^ q * (U : ℝ) ^ h := by norm_num
    _ < T ^ delta * (U : ℝ) ^ h :=
      mul_lt_mul_of_pos_right hDyadicQ hUpowPos
    _ < T ^ delta * T ^ a :=
      mul_lt_mul_of_pos_left hUpow (Real.rpow_pos_of_pos hTPos _)
    _ = T ^ (a + delta) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring

/-- Exact two-case upper scale for the block returned by equation (4.16).
The sole new loss `delta` comes from the bounded dyadic factor `2^q`. -/
theorem eventually_pintz2023_equation416_powered_scale_split
    {eta target delta : ℝ} {k ell : ℕ}
    (data : Pintz2023PowerMarginData eta target k ell)
    (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {U q h : ℕ}, 0 < U → q < h →
        (h : ℝ) < 20 / data.epsilon →
        (U : ℝ) <
          (pintz2023SourceX T data.epsilon ell : ℝ) *
            (2 * T) ^
              pintz2023CriticalScaleExponent k eta data.epsilon →
        (h = 2 ∨
          (h : ℝ) * pintz2023LogScale T U <
            pintz2023EllPowerWindowUpper eta data.epsilon ell) →
        (h = 2 ∧
            ((2 ^ q * U ^ h : ℕ) : ℝ) <
              T ^ (2 * (data.epsilon / (10 * (ell : ℝ)) +
                pintz2023CriticalScaleExponent k eta data.epsilon +
                data.delta) + delta)) ∨
          (h ≠ 2 ∧
            ((2 ^ q * U ^ h : ℕ) : ℝ) <
              T ^ (pintz2023EllPowerWindowUpper eta data.epsilon ell +
                delta)) := by
  have hSupportFactor := eventually_two_rpow_lt_rpow data.delta_pos
    (c := pintz2023CriticalScaleExponent k eta data.epsilon)
  have hDyadicFactor := eventually_two_rpow_lt_rpow hdelta
    (c := 20 / data.epsilon)
  filter_upwards [hSupportFactor, hDyadicFactor,
    eventually_gt_atTop 1] with T hSupportFactorT hDyadicFactorT hT
  intro U q h hU hq hhBound hSupport hhCase
  have hDyadic : (2 : ℝ) ^ (h : ℝ) < T ^ delta :=
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      hhBound).trans hDyadicFactorT
  by_cases hh : h = 2
  · left
    refine ⟨hh, ?_⟩
    subst h
    have hLogScale : pintz2023LogScale T U <
        data.epsilon / (10 * (ell : ℝ)) +
          pintz2023CriticalScaleExponent k eta data.epsilon +
          data.delta :=
      pintz2023_logScale_upper_of_support hT hU hSupportFactorT hSupport
    apply pintz2023_powered_dyadic_cast_lt_rpow hT hU hq _ hDyadic
    norm_num
    nlinarith
  · right
    refine ⟨hh, ?_⟩
    have hWindow := hhCase.resolve_left hh
    exact pintz2023_powered_dyadic_cast_lt_rpow hT hU hq hWindow hDyadic

#print axioms pintz2023_powered_dyadic_cast_lt_rpow
#print axioms eventually_pintz2023_equation416_powered_scale_split

end

end GafniTao
