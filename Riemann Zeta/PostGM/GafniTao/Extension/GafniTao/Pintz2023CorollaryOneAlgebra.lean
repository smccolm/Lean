import GafniTao.Pintz2023HeathBrownMajorant

/-!
# Pintz (2023), equation (3.2): exact exponent algebra

This file substitutes the logarithmic phase derivative into Heath--Brown's
three-term estimate.  The constants depending only on the derivative order
remain explicit, while the powers of `N` and `t` are put in the precise form
used in Pintz Corollary 1.
-/

namespace GafniTao

noncomputable section

/-- `1 / (r(r-1))`, the positive exponent in the first derivative term. -/
noncomputable def pintz2023HBAlpha (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * ((r : ℝ) - 1))

/-- `2 / (r^2(r-1))`, the magnitude of the negative height exponent. -/
noncomputable def pintz2023HBGamma (r : ℕ) : ℝ :=
  2 / ((r : ℝ) ^ 2 * ((r : ℝ) - 1))

/-- The positive `r`-dependent constant in the logarithmic phase's
`r`-th derivative at `2N`. -/
noncomputable def pintz2023DerivativeConstant (r : ℕ) : ℝ :=
  (r - 1).factorial / (2 * Real.pi) * (2 : ℝ) ^ (-(r : ℝ))

theorem pintz2023HBAlpha_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < pintz2023HBAlpha r := by
  unfold pintz2023HBAlpha
  have hrReal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsub : 0 < (r : ℝ) - 1 := by linarith
  exact one_div_pos.mpr (mul_pos (by positivity) hsub)

theorem pintz2023HBGamma_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < pintz2023HBGamma r := by
  unfold pintz2023HBGamma
  have hrReal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsub : 0 < (r : ℝ) - 1 := by linarith
  exact div_pos (by norm_num) (mul_pos (sq_pos_of_pos (by positivity)) hsub)

theorem pintz2023DerivativeConstant_pos (r : ℕ) :
    0 < pintz2023DerivativeConstant r := by
  unfold pintz2023DerivativeConstant
  have hfactorial : 0 < ((r - 1).factorial : ℝ) := by positivity
  positivity

theorem pintz2023_r_mul_alpha {r : ℕ} (hr : 2 ≤ r) :
    (r : ℝ) * pintz2023HBAlpha r = 1 / ((r : ℝ) - 1) := by
  have hrReal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold pintz2023HBAlpha
  field_simp

theorem pintz2023_r_mul_gamma {r : ℕ} (hr : 2 ≤ r) :
    (r : ℝ) * pintz2023HBGamma r =
      2 / ((r : ℝ) * ((r : ℝ) - 1)) := by
  have hrReal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold pintz2023HBGamma
  field_simp

/-- Exact separation of the derivative scale into its order constant,
height, and length powers. -/
theorem pintz2023DerivativeLambda_eq
    {r N : ℕ} {t : ℝ} (hN : 0 < N) :
    pintz2023DerivativeLambda r N t =
      pintz2023DerivativeConstant r * t *
        (N : ℝ) ^ (-(r : ℝ)) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hNr : (0 : ℝ) ≤ N := hNReal.le
  unfold pintz2023DerivativeLambda pintz2023DerivativeConstant
  rw [← Real.rpow_intCast]
  rw [Real.mul_rpow htwo hNr]
  push_cast
  ring

/-- The positive derivative term contributes the source power
`N^(-1/(r-1)) t^(1/(r(r-1)))`. -/
theorem pintz2023DerivativeLambda_rpow_alpha
    {r N : ℕ} {t : ℝ} (hr : 2 ≤ r) (hN : 0 < N) (ht : 0 ≤ t) :
    (pintz2023DerivativeLambda r N t) ^ pintz2023HBAlpha r =
      (pintz2023DerivativeConstant r) ^ pintz2023HBAlpha r *
        t ^ pintz2023HBAlpha r *
        (N : ℝ) ^ (-1 / ((r : ℝ) - 1)) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := (pintz2023DerivativeConstant_pos r).le
  rw [pintz2023DerivativeLambda_eq hN]
  rw [Real.mul_rpow (mul_nonneg hd ht) (Real.rpow_nonneg hNReal.le _),
    Real.mul_rpow hd ht]
  rw [← Real.rpow_mul hNReal.le]
  have hExp : (-(r : ℝ)) * pintz2023HBAlpha r =
      -1 / ((r : ℝ) - 1) := by
    rw [neg_mul, pintz2023_r_mul_alpha hr]
    ring
  rw [hExp]

/-- The negative derivative term cancels its `N^(-2/(r(r-1)))`
prefactor exactly. -/
theorem pintz2023DerivativeLambda_rpow_neg_gamma
    {r N : ℕ} {t : ℝ} (hr : 2 ≤ r) (hN : 0 < N) (ht : 0 < t) :
    (pintz2023DerivativeLambda r N t) ^ (-pintz2023HBGamma r) =
      (pintz2023DerivativeConstant r) ^ (-pintz2023HBGamma r) *
        t ^ (-pintz2023HBGamma r) *
        (N : ℝ) ^
          (2 / ((r : ℝ) * ((r : ℝ) - 1))) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := (pintz2023DerivativeConstant_pos r).le
  rw [pintz2023DerivativeLambda_eq hN]
  rw [Real.mul_rpow (mul_nonneg hd ht.le) (Real.rpow_nonneg hNReal.le _),
    Real.mul_rpow hd ht.le]
  rw [← Real.rpow_mul hNReal.le]
  have hExp : (-(r : ℝ)) * (-pintz2023HBGamma r) =
      2 / ((r : ℝ) * ((r : ℝ) - 1)) := by
    rw [neg_mul_neg, pintz2023_r_mul_gamma hr]
  rw [hExp]

/-- Fully expanded three-term factor after multiplying by the weighted
outer power `N^(xi+epsilon)`. -/
theorem pintz2023_scaled_derivative_factor_eq
    {r N : ℕ} {t xi epsilon : ℝ}
    (hr : 3 ≤ r) (hN : 0 < N) (ht : 0 < t) :
    (N : ℝ) ^ (xi + epsilon) *
        heathBrownKthDerivativeFactor r N
          (pintz2023DerivativeLambda r N t) =
      (pintz2023DerivativeConstant r) ^ pintz2023HBAlpha r *
          (N : ℝ) ^
            (xi - 1 / ((r : ℝ) - 1) + epsilon) *
          t ^ pintz2023HBAlpha r +
        (N : ℝ) ^ (xi + epsilon - pintz2023HBAlpha r) +
        (pintz2023DerivativeConstant r) ^ (-pintz2023HBGamma r) *
          (N : ℝ) ^ (xi + epsilon) *
          t ^ (-pintz2023HBGamma r) := by
  have hrTwo : 2 ≤ r := by omega
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hAlpha :
      1 / ((r : ℝ) * ((r : ℝ) - 1)) = pintz2023HBAlpha r := by
    rfl
  have hnegOne :
      -1 / ((r : ℝ) * ((r : ℝ) - 1)) = -pintz2023HBAlpha r := by
    unfold pintz2023HBAlpha
    ring
  have hnegTwo :
      -2 / ((r : ℝ) * ((r : ℝ) - 1)) =
        -(2 / ((r : ℝ) * ((r : ℝ) - 1))) := by ring
  have hnegGamma :
      -2 / ((r : ℝ) ^ 2 * ((r : ℝ) - 1)) =
        -pintz2023HBGamma r := by
    unfold pintz2023HBGamma
    ring
  unfold heathBrownKthDerivativeFactor
  rw [hAlpha, hnegOne, hnegTwo, hnegGamma]
  rw [pintz2023DerivativeLambda_rpow_alpha hrTwo hN ht.le]
  rw [pintz2023DerivativeLambda_rpow_neg_gamma hrTwo hN ht]
  have hpowFirst :
      (N : ℝ) ^ (xi + epsilon) *
          (N : ℝ) ^ (-1 / ((r : ℝ) - 1)) =
        (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + epsilon) := by
    rw [← Real.rpow_add hNReal]
    congr 1
    ring
  have hpowSecond :
      (N : ℝ) ^ (xi + epsilon) *
          (N : ℝ) ^ (-pintz2023HBAlpha r) =
        (N : ℝ) ^ (xi + epsilon - pintz2023HBAlpha r) := by
    rw [← Real.rpow_add hNReal]
    congr 1
  have hpowCancel :
      (N : ℝ) ^ (-(2 / ((r : ℝ) * ((r : ℝ) - 1)))) *
          (N : ℝ) ^ (2 / ((r : ℝ) * ((r : ℝ) - 1))) = 1 := by
    rw [← Real.rpow_add hNReal]
    have hz :
        -(2 / ((r : ℝ) * ((r : ℝ) - 1))) +
          2 / ((r : ℝ) * ((r : ℝ) - 1)) = 0 := by ring
    rw [hz, Real.rpow_zero]
  calc
    _ = (pintz2023DerivativeConstant r) ^ pintz2023HBAlpha r *
          t ^ pintz2023HBAlpha r *
          ((N : ℝ) ^ (xi + epsilon) *
            (N : ℝ) ^ (-1 / ((r : ℝ) - 1))) +
        ((N : ℝ) ^ (xi + epsilon) *
          (N : ℝ) ^ (-pintz2023HBAlpha r)) +
        (pintz2023DerivativeConstant r) ^ (-pintz2023HBGamma r) *
          t ^ (-pintz2023HBGamma r) * (N : ℝ) ^ (xi + epsilon) *
          ((N : ℝ) ^ (-(2 / ((r : ℝ) * ((r : ℝ) - 1)))) *
            (N : ℝ) ^ (2 / ((r : ℝ) * ((r : ℝ) - 1)))) := by
              ring
    _ = _ := by rw [hpowFirst, hpowSecond, hpowCancel]; ring

#print axioms pintz2023DerivativeLambda_eq
#print axioms pintz2023DerivativeLambda_rpow_alpha
#print axioms pintz2023DerivativeLambda_rpow_neg_gamma
#print axioms pintz2023_scaled_derivative_factor_eq

end

end GafniTao
