import GafniTao.HeathBrownZetaExponent

/-!
# Heath--Brown Theorem 4: exact range arithmetic

These are the rational inequalities used in the proof of the exponential-sum
estimate (1.9).  They are kept separate from the analytic exponent-pair
arguments so that every range endpoint in the published proof is checked by
the kernel.
-/

namespace GafniTao

noncomputable section

/-- The `ABA^2B(0,1) = (1/9,13/18)` range in Heath--Brown's proof. -/
theorem heathBrown_EP1_low_range
    {tau : ℝ} (hlow : 2 ≤ tau) (hhigh : tau ≤ 59 / 22) :
    (2 * tau - 7) / 18 ≤ -49 / (80 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hpoly : 160 * tau ^ 3 - 560 * tau ^ 2 + 882 ≤ 0 := by
    by_cases hleft : tau ≤ 7 / 3
    · have hquad : 160 * tau ^ 2 - 240 * tau - 480 ≤ 0 := by
        nlinarith [sq_nonneg (tau - 7 / 3)]
      have hprod :
          (tau - 2) * (160 * tau ^ 2 - 240 * tau - 480) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hquad
      nlinarith
    · have hright : 7 / 3 ≤ tau := by linarith
      let b : ℝ := 59 / 22
      have hb : tau ≤ b := by simpa only [b] using hhigh
      have hq : 0 ≤
          160 * (tau ^ 2 + tau * b + b ^ 2) - 560 * (tau + b) := by
        dsimp only [b]
        nlinarith [sq_nonneg (tau - 7 / 3)]
      have hprod :
          (tau - b) *
            (160 * (tau ^ 2 + tau * b + b ^ 2) - 560 * (tau + b)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
      dsimp only [b] at hprod
      nlinarith
  have hden : 0 < 1440 * tau ^ 2 := by positivity
  have hidentity :
      (-49 / (80 * tau ^ 2) - (2 * tau - 7) / 18) *
          (1440 * tau ^ 2) =
        -(160 * tau ^ 3 - 560 * tau ^ 2 + 882) := by
    field_simp [htau.ne']
    ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 1440 * tau ^ 2) _ hden
  rw [hidentity]
  linarith

/-- The `A^2BA^2B(0,1) = (1/20,33/40)` range. -/
theorem heathBrown_EP1_middle_exponent_pair_range
    {tau : ℝ} (hlow : 59 / 22 ≤ tau) (hhigh : tau ≤ 7 / 2) :
    (2 * tau - 9) / 40 ≤ -49 / (80 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have hquad : 0 ≤ 2 * tau ^ 2 - 2 * tau - 7 := by
    nlinarith [sq_nonneg (tau - 1 / 2)]
  have hfactor :
      (2 * tau - 7) * (2 * tau ^ 2 - 2 * tau - 7) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hquad
  have hden : 0 < 80 * tau ^ 2 := by positivity
  have hidentity :
      (-49 / (80 * tau ^ 2) - (2 * tau - 9) / 40) *
          (80 * tau ^ 2) =
        -((2 * tau - 7) * (2 * tau ^ 2 - 2 * tau - 7)) := by
    field_simp [htau.ne']
    ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 80 * tau ^ 2) _ hden
  rw [hidentity]
  linarith

/-- The constant-saving part of the `k=5` derivative-test range. -/
theorem heathBrown_EP1_kfive_constant_range
    {tau : ℝ} (hlow : 7 / 2 ≤ tau) (_hhigh : tau ≤ 4) :
    (-1 / 20 : ℝ) ≤ -49 / (80 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  have htauSq : 49 / 4 ≤ tau ^ 2 := by nlinarith
  have hden : 0 < 80 * tau ^ 2 := by positivity
  have hidentity :
      (-49 / (80 * tau ^ 2) - (-1 / 20)) * (80 * tau ^ 2) =
        4 * tau ^ 2 - 49 := by
    field_simp [htau.ne']
    ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 80 * tau ^ 2) _ hden
  rw [hidentity]
  nlinarith

/-- The sloping part of the `k=5` derivative-test range. -/
theorem heathBrown_EP1_kfive_sloping_range
    {tau : ℝ} (hlow : 4 ≤ tau) (hhigh : tau ≤ 13 / 3) :
    -(5 - tau) / 20 ≤ -49 / (80 * tau ^ 2) := by
  have htau : 0 < tau := by linarith
  let b : ℝ := 13 / 3
  have hb : tau ≤ b := by simpa only [b] using hhigh
  have hq : 0 ≤
      4 * (tau ^ 2 + tau * b + b ^ 2) - 20 * (tau + b) := by
    dsimp only [b]
    nlinarith [sq_nonneg (tau - 5 / 2)]
  have hprod :
      (tau - b) *
        (4 * (tau ^ 2 + tau * b + b ^ 2) - 20 * (tau + b)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
  dsimp only [b] at hprod
  have hden : 0 < 80 * tau ^ 2 := by positivity
  have hidentity :
      (-49 / (80 * tau ^ 2) - (-(5 - tau) / 20)) *
          (80 * tau ^ 2) =
        -(4 * tau ^ 3 - 20 * tau ^ 2 + 49) := by
    field_simp [htau.ne']
    ring
  have hpoly : 4 * tau ^ 3 - 20 * tau ^ 2 + 49 ≤ 0 := by
    nlinarith
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 80 * tau ^ 2) _ hden
  rw [hidentity]
  linarith

/-- The exact rational inequality at the break points
`tau=(k^2+1)/(k+1)`, used for all `k>=5`. -/
theorem heathBrown_EP1_large_breakpoint
    {k : ℕ} (hk : 5 ≤ k) :
    (49 / 80 : ℝ) ≤
      (((k : ℝ) ^ 2 + 1) ^ 2) /
        ((k : ℝ) * ((k : ℝ) + 1) ^ 3) := by
  have hkReal : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by linarith
  have hkOnePos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  let m : ℝ := (k : ℝ) - 5
  have hm : 0 ≤ m := by dsimp only [m]; linarith
  have hpoly :
      0 ≤ 31 * (k : ℝ) ^ 4 - 147 * (k : ℝ) ^ 3 +
        13 * (k : ℝ) ^ 2 - 49 * (k : ℝ) + 80 := by
    have hnonneg :
        0 ≤ 31 * m ^ 4 + 473 * m ^ 3 + 2458 * m ^ 2 +
          4556 * m + 1160 := by positivity
    dsimp only [m] at hnonneg
    nlinarith
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 80)
    (mul_pos hkPos (pow_pos hkOnePos 3))]
  nlinarith

#print axioms heathBrown_EP1_low_range
#print axioms heathBrown_EP1_middle_exponent_pair_range
#print axioms heathBrown_EP1_kfive_constant_range
#print axioms heathBrown_EP1_kfive_sloping_range
#print axioms heathBrown_EP1_large_breakpoint

end

end GafniTao
