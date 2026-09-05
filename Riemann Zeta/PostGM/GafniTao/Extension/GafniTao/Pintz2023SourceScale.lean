import GafniTao.Pintz2023DetectionNative

/-!
# Pintz (2023), equation (4.1): exact physical scales

This file fixes the integer convention for the source mollifier endpoint and
records the exact bridges from Pintz's powers of `T` to the logarithmic
parameter `lambda`.  No asymptotic loss is taken here.
-/

namespace GafniTao

noncomputable section

/-- The integer mollifier endpoint corresponding to Pintz's
`X = T^(epsilon/(10 ell))`. -/
noncomputable def pintz2023SourceX
    (T epsilon : ℝ) (ell : ℕ) : ℕ :=
  Nat.floor (T ^ (epsilon / (10 * (ell : ℝ))))

/-- Pintz's `lambda = log Y = (2/k) log T`. -/
noncomputable def pintz2023SourceLambda
    (T : ℝ) (k : ℕ) : ℝ :=
  (2 / (k : ℝ)) * Real.log T

theorem pintz2023SourceX_cast_le
    {T epsilon : ℝ} {ell : ℕ}
    (hpow : 0 ≤ T ^ (epsilon / (10 * (ell : ℝ)))) :
    (pintz2023SourceX T epsilon ell : ℝ) ≤
      T ^ (epsilon / (10 * (ell : ℝ))) := by
  exact Nat.floor_le hpow

theorem pintz2023SourceX_pos
    {T epsilon : ℝ} {ell : ℕ}
    (hpow : 1 ≤ T ^ (epsilon / (10 * (ell : ℝ)))) :
    0 < pintz2023SourceX T epsilon ell := by
  exact Nat.floor_pos.mpr hpow

theorem pintz2023SourceLambda_pos
    {T : ℝ} {k : ℕ} (hT : 1 < T) (hk : 0 < k) :
    0 < pintz2023SourceLambda T k := by
  unfold pintz2023SourceLambda
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  exact mul_pos (div_pos (by norm_num) hkReal) (Real.log_pos hT)

theorem exp_pintz2023SourceLambda
    {T : ℝ} {k : ℕ} (hT : 0 < T) :
    Real.exp (pintz2023SourceLambda T k) = T ^ (2 / (k : ℝ)) := by
  rw [Real.rpow_def_of_pos hT]
  unfold pintz2023SourceLambda
  congr 1
  ring

theorem exp_neg_pintz2023SourceLambda_mul
    {T eta : ℝ} {k : ℕ} (hT : 0 < T) (hk : 0 < k) :
    Real.exp (-pintz2023SourceLambda T k * eta) =
      T ^ (-2 * eta / (k : ℝ)) := by
  rw [Real.rpow_def_of_pos hT]
  unfold pintz2023SourceLambda
  congr 1
  field_simp

theorem exp_neg_two_pintz2023SourceLambda
    {T : ℝ} {k : ℕ} (hT : 0 < T) (hk : 0 < k) :
    Real.exp (-2 * pintz2023SourceLambda T k) =
      T ^ (-4 / (k : ℝ)) := by
  rw [Real.rpow_def_of_pos hT]
  unfold pintz2023SourceLambda
  congr 1
  field_simp
  ring

theorem exp_neg_three_pintz2023SourceLambda
    {T : ℝ} {k : ℕ} (hT : 0 < T) (hk : 0 < k) :
    Real.exp (-3 * pintz2023SourceLambda T k) =
      T ^ (-6 / (k : ℝ)) := by
  rw [Real.rpow_def_of_pos hT]
  unfold pintz2023SourceLambda
  congr 1
  field_simp
  ring

theorem pintz2023SourceX_le_cutoff
    {T epsilon : ℝ} {k ell : ℕ}
    (hT : 1 ≤ T)
    (hexponent : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ)) :
    pintz2023SourceX T epsilon ell ≤
      pintz2023Cutoff (pintz2023SourceLambda T k) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hpowNonneg : 0 ≤ T ^ (epsilon / (10 * (ell : ℝ))) :=
    (Real.rpow_pos_of_pos hTPos _).le
  have hpowMono :
      T ^ (epsilon / (10 * (ell : ℝ))) ≤ T ^ (2 / (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hT hexponent
  have hExp : T ^ (2 / (k : ℝ)) =
      Real.exp (pintz2023SourceLambda T k) :=
    (exp_pintz2023SourceLambda hTPos).symm
  have hThree : Real.exp (pintz2023SourceLambda T k) ≤
      Real.exp (pintz2023SourceLambda T k + 3) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hCeil : Real.exp (pintz2023SourceLambda T k + 3) ≤
      (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast (pintz2023SourceX_cast_le hpowNonneg).trans
    (hpowMono.trans (hExp.le.trans (hThree.trans hCeil)))

#print axioms pintz2023SourceX_cast_le
#print axioms pintz2023SourceX_pos
#print axioms pintz2023SourceLambda_pos
#print axioms exp_pintz2023SourceLambda
#print axioms exp_neg_pintz2023SourceLambda_mul
#print axioms exp_neg_two_pintz2023SourceLambda
#print axioms exp_neg_three_pintz2023SourceLambda
#print axioms pintz2023SourceX_le_cutoff

end

end GafniTao
