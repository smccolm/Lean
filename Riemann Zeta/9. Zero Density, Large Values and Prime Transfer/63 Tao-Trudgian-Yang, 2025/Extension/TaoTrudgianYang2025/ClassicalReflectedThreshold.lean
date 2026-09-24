import TaoTrudgianYang2025.ClassicalReflectedIndexedSourceFourier

/-!
# Reflected source threshold normalization

The exponent comparison uses the actual reflected upper length scale and
the complete source threshold, without discarding the loss in d or u.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalReflected_threshold_exponent_margin
    (sigma tau d u : ℝ) (hsigma : 1/2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (htau : 0 < tau) (htauTwo : tau ≤ 2) (hd : 0 ≤ d) :
    sigma*(1+d-1/tau)-u-3*d ≤
      1/2-u-d*sigma+(sigma-1)/tau-d := by
  have hInv : (1/2 : ℝ) ≤ 1/tau := by
    exact div_le_div_of_nonneg_left (by norm_num) htau htauTwo
  have hp := mul_nonneg (show 0 ≤ 2*sigma-1 by linarith)
    (show 0 ≤ 1/tau-1/2 by linarith)
  have hdprod := mul_nonneg hd (sub_nonneg.mpr hsigmaUpper)
  simp only [div_eq_mul_inv] at hInv hp ⊢
  nlinarith

theorem classicalReflected_threshold_lower_of_physical_scale
    (sigma tau d u T C L : ℝ) (N : ℕ)
    (hsigma : 1/2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (htau : 0 < tau) (htauTwo : tau ≤ 2) (hd : 0 ≤ d)
    (hT : 1 ≤ T) (hC : 0 < C)
    (hN : (N : ℝ) ≤ T^(1+d-1/tau))
    (hL : T^(1/2-u-d*sigma+(sigma-1)/tau-d)/C ≤ L) :
    (N : ℝ)^sigma*T^(-u-3*d)/C ≤ L := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hsigmaNonneg : 0 ≤ sigma := by linarith
  have hNpow := Real.rpow_le_rpow (Nat.cast_nonneg N) hN hsigmaNonneg
  rw [← Real.rpow_mul hTpos.le] at hNpow
  have hmargin := classicalReflected_threshold_exponent_margin
    sigma tau d u hsigma hsigmaUpper htau htauTwo hd
  calc
    (N : ℝ)^sigma*T^(-u-3*d)/C ≤
        T^((1+d-1/tau)*sigma)*T^(-u-3*d)/C := by
      gcongr
    _ = T^(sigma*(1+d-1/tau)-u-3*d)/C := by
      rw [← Real.rpow_add hTpos]
      congr 2
      ring
    _ ≤ T^(1/2-u-d*sigma+(sigma-1)/tau-d)/C :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hT hmargin) hC.le
    _ ≤ L := hL

theorem classicalReflected_normalized_threshold_ge
    (sigma L : ℝ) (M N : ℕ)
    (hsigma : 0 ≤ sigma) (hL : 0 ≤ L) (hN : 0 < N) (hNM : N ≤ M) :
    L/(4*classicalTypeIFourierL1 (-sigma)) ≤
      (M : ℝ)^sigma*L /
        (4*(N : ℝ)^sigma*classicalTypeIFourierL1 (-sigma)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ)^sigma := Real.rpow_pos_of_pos hNpos _
  have hmass := classicalTypeIFourierL1_pos (-sigma)
  have hpow : (N : ℝ)^sigma ≤ (M : ℝ)^sigma :=
    Real.rpow_le_rpow hNpos.le (by exact_mod_cast hNM) hsigma
  calc
    L/(4*classicalTypeIFourierL1 (-sigma)) =
        (N : ℝ)^sigma*L/(4*(N : ℝ)^sigma*classicalTypeIFourierL1 (-sigma)) := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hL) (by positivity)


theorem classicalReflected_dyadic_length_le_physical_scale
    {T tau d : ℝ} {Q N : ℕ}
    (hT : 0 < T) (htau : 0 < tau) (hQ : 1 < Q)
    (hScale : (Q : ℝ)^tau = T)
    (hN : N ≤ mediumTypeIDualCutoff T d Q) :
    (N : ℝ) ≤ T^(1+d-1/tau) := by
  have hQEq : (Q : ℝ) = T^(1/tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQ htau hScale
  calc
    (N : ℝ) ≤ (mediumTypeIDualCutoff T d Q : ℝ) := by exact_mod_cast hN
    _ ≤ T^(1+d)/Q := mediumTypeIDualCutoff_cast_le hT.le
    _ = T^(1+d-1/tau) := by rw [hQEq, ← Real.rpow_sub hT]

end TaoTrudgianYang2025

