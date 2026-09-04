import GafniTao.HeathBrownRefinedCountBound

/-!
# Heath-Brown's literal Taylor-block length

The source chooses `H = floor ((A * lambda)^(-1/k))`.  The following
finite lemmas retain that floor and prove the two-sided comparison required
for the later exponent algebra.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownHChoice
    (k : ℕ) (A lambda : ℝ) : ℕ :=
  ⌊(A * lambda) ^ (-(1 / (k : ℝ)))⌋₊

theorem heathBrownHChoice_rpow_one_le
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    1 ≤ (A * lambda) ^ (-(1 / (k : ℝ))) := by
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
  · positivity
  · linarith
  · have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    exact neg_nonpos.mpr (by positivity)

theorem heathBrownHChoice_pos
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    0 < heathBrownHChoice k A lambda := by
  unfold heathBrownHChoice
  exact Nat.floor_pos.mpr
    (heathBrownHChoice_rpow_one_le hk hA hlambda hsmall)

theorem heathBrownHChoice_cast_le_rpow
    {k : ℕ} {A lambda : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda) :
    (heathBrownHChoice k A lambda : ℝ) ≤
      (A * lambda) ^ (-(1 / (k : ℝ))) := by
  unfold heathBrownHChoice
  exact Nat.floor_le (Real.rpow_nonneg (mul_pos hA hlambda).le _)

theorem heathBrownHChoice_rpow_lt_cast_add_one
    {k : ℕ} {A lambda : ℝ} :
    (A * lambda) ^ (-(1 / (k : ℝ))) <
      (heathBrownHChoice k A lambda : ℝ) + 1 := by
  unfold heathBrownHChoice
  simpa only [Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one ((A * lambda) ^ (-(1 / (k : ℝ))))

theorem heathBrownHChoice_rpow_le_two_mul
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    (A * lambda) ^ (-(1 / (k : ℝ))) ≤
      2 * heathBrownHChoice k A lambda := by
  have hH : (1 : ℝ) ≤ heathBrownHChoice k A lambda := by
    exact_mod_cast (heathBrownHChoice_pos hk hA hlambda hsmall)
  have hlt := heathBrownHChoice_rpow_lt_cast_add_one
    (k := k) (A := A) (lambda := lambda)
  norm_num at hlt ⊢
  linarith

theorem heathBrownHChoice_rpow_pow_k
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    ((A * lambda) ^ (-(1 / (k : ℝ)))) ^ k =
      (A * lambda)⁻¹ := by
  have hp : 0 < A * lambda := mul_pos hA hlambda
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  rw [show -(1 / (k : ℝ)) * k = (-1 : ℝ) by field_simp,
    Real.rpow_neg_one]

theorem heathBrownHChoice_scale_pow_le_one
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    A * lambda * (heathBrownHChoice k A lambda : ℝ) ^ k ≤ 1 := by
  have hp : 0 < A * lambda := mul_pos hA hlambda
  have hHnonneg : (0 : ℝ) ≤ heathBrownHChoice k A lambda := by positivity
  have hpow := pow_le_pow_left₀ hHnonneg
    (heathBrownHChoice_cast_le_rpow hA hlambda) k
  rw [heathBrownHChoice_rpow_pow_k hk hA hlambda] at hpow
  calc
    A * lambda * (heathBrownHChoice k A lambda : ℝ) ^ k ≤
        A * lambda * (A * lambda)⁻¹ :=
      mul_le_mul_of_nonneg_left hpow hp.le
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- The floor costs at most a factor two in every inverse integral power.
This is the exact device used to replace powers of the natural `H` by powers
of the real source scale before absorbing constants depending on `k`. -/
theorem heathBrownHChoice_inv_pow_le
    {k r : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    (((heathBrownHChoice k A lambda : ℝ) ^ r)⁻¹) ≤
      (((A * lambda) ^ (-(1 / (k : ℝ))) / 2) ^ (-(r : ℝ))) := by
  let q := (A * lambda) ^ (-(1 / (k : ℝ)))
  let H := heathBrownHChoice k A lambda
  have hqpos : 0 < q := by
    dsimp only [q]
    exact Real.rpow_pos_of_pos (mul_pos hA hlambda) _
  have hHpos : (0 : ℝ) < H := by
    exact_mod_cast (heathBrownHChoice_pos hk hA hlambda hsmall)
  have hqle : q ≤ 2 * H := by
    simpa only [q, H] using
      (heathBrownHChoice_rpow_le_two_mul hk hA hlambda hsmall)
  have hhalf : q / 2 ≤ (H : ℝ) := by linarith
  have hneg : -(r : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg r)
  have hmono := Real.rpow_le_rpow_of_nonpos
    (div_pos hqpos (by norm_num : (0 : ℝ) < 2)) hhalf hneg
  rw [Real.rpow_neg hHpos.le, Real.rpow_natCast] at hmono
  simpa only [q, H] using hmono

theorem heathBrownHChoice_half_rpow_neg_eq
    {k r : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    (((A * lambda) ^ (-(1 / (k : ℝ))) / 2) ^ (-(r : ℝ))) =
      (2 : ℝ) ^ r *
        (A * lambda) ^ ((r : ℝ) / k) := by
  have hp : 0 < A * lambda := mul_pos hA hlambda
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hq : 0 ≤ (A * lambda) ^ (-(1 / (k : ℝ))) :=
    Real.rpow_nonneg hp.le _
  rw [div_eq_mul_inv, Real.mul_rpow hq (by positivity)]
  rw [← Real.rpow_mul hp.le]
  rw [show -(1 / (k : ℝ)) * -(r : ℝ) = (r : ℝ) / k by field_simp]
  rw [← Real.rpow_neg_one]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (-1 : ℝ) * -(r : ℝ) = r by ring, Real.rpow_natCast]
  ring

theorem heathBrownHChoice_inv_pow_le_source
    {k r : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    (((heathBrownHChoice k A lambda : ℝ) ^ r)⁻¹) ≤
      (2 : ℝ) ^ r * (A * lambda) ^ ((r : ℝ) / k) := by
  calc
    (((heathBrownHChoice k A lambda : ℝ) ^ r)⁻¹) ≤
        (((A * lambda) ^ (-(1 / (k : ℝ))) / 2) ^ (-(r : ℝ))) :=
      heathBrownHChoice_inv_pow_le hk hA hlambda hsmall
    _ = (2 : ℝ) ^ r * (A * lambda) ^ ((r : ℝ) / k) :=
      heathBrownHChoice_half_rpow_neg_eq hk hA hlambda

theorem heathBrown_width_le_half_of_eight_le
    {k H : ℕ} (hk : 3 ≤ k) (hH : 8 ≤ H) :
    4 * (((H : ℝ) ^ (k - 2))⁻¹) ≤ 1 / 2 ∧
      4 * (((H : ℝ) ^ (k - 1))⁻¹) ≤ 1 / 2 := by
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
  have hHeight : (8 : ℝ) ≤ H := by exact_mod_cast hH
  have bound (r : ℕ) (hr : 1 ≤ r) :
      4 * (((H : ℝ) ^ r)⁻¹) ≤ 1 / 2 := by
    have hpow : (H : ℝ) ≤ (H : ℝ) ^ r := by
      simpa only [pow_one] using pow_le_pow_right₀ hHone hr
    have hpowpos : 0 < (H : ℝ) ^ r := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpowpos]
    nlinarith
  exact ⟨bound (k - 2) (by omega), bound (k - 1) (by omega)⟩

#print axioms heathBrownHChoice_rpow_one_le
#print axioms heathBrownHChoice_pos
#print axioms heathBrownHChoice_cast_le_rpow
#print axioms heathBrownHChoice_rpow_lt_cast_add_one
#print axioms heathBrownHChoice_rpow_le_two_mul
#print axioms heathBrownHChoice_rpow_pow_k
#print axioms heathBrownHChoice_scale_pow_le_one
#print axioms heathBrownHChoice_inv_pow_le
#print axioms heathBrownHChoice_half_rpow_neg_eq
#print axioms heathBrownHChoice_inv_pow_le_source
#print axioms heathBrown_width_le_half_of_eight_le

end

end GafniTao
