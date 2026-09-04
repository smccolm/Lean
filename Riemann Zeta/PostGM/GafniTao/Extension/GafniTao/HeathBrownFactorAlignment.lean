import GafniTao.HeathBrownFloorRemainder

/-!
# Alignment with the published Heath-Brown Theorem 1 factor

This file proves both source algebra steps after Lemma 1: the three critical
monomials are exactly `N` times the displayed theorem factor, and the extra
`lambda^(-1/k)` term is dominated by the third critical monomial whenever
that monomial does not already make the trivial bound sufficient.
-/

namespace GafniTao

noncomputable section

theorem heathBrownKthDerivativeFactor_eq_critical
    {k : ℕ} (hk : 2 ≤ k) (N lambda : ℝ) :
    heathBrownKthDerivativeFactor k N lambda =
      let r := heathBrownCriticalReciprocal k
      lambda ^ r + N ^ (-r) +
        N ^ (-2 * r) * lambda ^ (-2 * r / (k : ℝ)) := by
  dsimp only
  unfold heathBrownKthDerivativeFactor heathBrownCriticalReciprocal
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hkm10 : (k : ℝ) - 1 ≠ 0 := by linarith
  congr 1
  · congr 1
    field_simp
  · congr 1
    · congr 1
      field_simp
    · congr 1
      field_simp

theorem heathBrownThreeTerm_scaled_identity
    {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k)
    (lambda epsilon : ℝ) :
    (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda =
      (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N lambda := by
  let r := heathBrownCriticalReciprocal k
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfirst :
      (N : ℝ) ^ epsilon * (N : ℝ) ^ (1 - r) =
        (N : ℝ) ^ (1 + epsilon) * (N : ℝ) ^ (-r) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hmiddle :
      (N : ℝ) ^ epsilon * ((N : ℝ) * lambda ^ r) =
        (N : ℝ) ^ (1 + epsilon) * lambda ^ r := by
    calc
      (N : ℝ) ^ epsilon * ((N : ℝ) * lambda ^ r) =
          ((N : ℝ) ^ epsilon * (N : ℝ)) * lambda ^ r := by ring
      _ = (N : ℝ) ^ (epsilon + 1) * lambda ^ r := by
        rw [Real.rpow_add_one hNpos.ne']
      _ = (N : ℝ) ^ (1 + epsilon) * lambda ^ r := by
        rw [add_comm epsilon 1]
  have hlast :
      (N : ℝ) ^ epsilon *
          ((N : ℝ) ^ (1 - 2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) =
        (N : ℝ) ^ (1 + epsilon) *
          ((N : ℝ) ^ (-2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) := by
    have hpow :
        (N : ℝ) ^ epsilon * (N : ℝ) ^ (1 - 2 * r) =
          (N : ℝ) ^ (1 + epsilon) * (N : ℝ) ^ (-2 * r) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      (N : ℝ) ^ epsilon *
          ((N : ℝ) ^ (1 - 2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) =
          ((N : ℝ) ^ epsilon * (N : ℝ) ^ (1 - 2 * r)) *
            lambda ^ (-2 * r / (k : ℝ)) := by ring
      _ = ((N : ℝ) ^ (1 + epsilon) * (N : ℝ) ^ (-2 * r)) *
            lambda ^ (-2 * r / (k : ℝ)) := by rw [hpow]
      _ = (N : ℝ) ^ (1 + epsilon) *
          ((N : ℝ) ^ (-2 * r) *
            lambda ^ (-2 * r / (k : ℝ))) := by ring
  rw [heathBrownKthDerivativeFactor_eq_critical hk N lambda]
  unfold heathBrownThreeTerm
  dsimp only
  rw [mul_add, mul_add, mul_add, mul_add]
  rw [hfirst, hmiddle, hlast]
  ring

theorem heathBrown_lambda_power_identity
    {k : ℕ} (hk : 2 ≤ k) {lambda : ℝ} (hlambda : 0 < lambda) :
    let r := heathBrownCriticalReciprocal k
    (lambda ^ (-(1 / (k : ℝ)))) ^ (2 * r) =
      lambda ^ (-2 * r / (k : ℝ)) := by
  dsimp only
  let r := heathBrownCriticalReciprocal k
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_mul hlambda.le]
  congr 1
  field_simp

/-- Source final case split: below the trivial range, the extra
`lambda^(-1/k)` term is bounded by the third displayed monomial. -/
theorem heathBrown_lambda_term_le_third_of_third_le_N
    {N k : ℕ} (hN : 1 ≤ N) (hk : 3 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hthird :
      (N : ℝ) ^ (1 - 2 * heathBrownCriticalReciprocal k) *
          lambda ^ (-2 * heathBrownCriticalReciprocal k / (k : ℝ)) ≤
        N) :
    lambda ^ (-(1 / (k : ℝ))) ≤
      (N : ℝ) ^ (1 - 2 * heathBrownCriticalReciprocal k) *
        lambda ^ (-2 * heathBrownCriticalReciprocal k / (k : ℝ)) := by
  let r := heathBrownCriticalReciprocal k
  let L := lambda ^ (-(1 / (k : ℝ)))
  have hr : 0 < r := heathBrownCriticalReciprocal_pos (by omega : 2 ≤ k)
  have hrHalf : r ≤ 1 / 2 :=
    heathBrownCriticalReciprocal_le_half (by omega : 2 ≤ k)
  have hq : 0 ≤ 1 - 2 * r := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hlambdaPower : L ^ (2 * r) =
      lambda ^ (-2 * r / (k : ℝ)) := by
    simpa only [L, r] using heathBrown_lambda_power_identity
      (by omega : 2 ≤ k) hlambda
  have hNsplit :
      (N : ℝ) = (N : ℝ) ^ (1 - 2 * r) *
        (N : ℝ) ^ (2 * r) := by
    rw [← Real.rpow_add hNpos]
    rw [show 1 - 2 * r + 2 * r = 1 by ring, Real.rpow_one]
  have hpower : L ^ (2 * r) ≤ (N : ℝ) ^ (2 * r) := by
    have hthird' : (N : ℝ) ^ (1 - 2 * r) * L ^ (2 * r) ≤
        (N : ℝ) := by
      rw [hlambdaPower]
      simpa only [r] using hthird
    rw [hNsplit] at hthird'
    have hfactorPos : 0 < (N : ℝ) ^ (1 - 2 * r) :=
      Real.rpow_pos_of_pos hNpos _
    nlinarith
  have hLN : L ≤ (N : ℝ) :=
    (Real.rpow_le_rpow_iff hLpos.le hNpos.le (by positivity : 0 < 2 * r)).mp hpower
  have hbasePower : L ^ (1 - 2 * r) ≤
      (N : ℝ) ^ (1 - 2 * r) :=
    Real.rpow_le_rpow hLpos.le hLN hq
  calc
    lambda ^ (-(1 / (k : ℝ))) = L := rfl
    _ = L ^ (1 - 2 * r) * L ^ (2 * r) := by
      rw [← Real.rpow_add hLpos]
      rw [show 1 - 2 * r + 2 * r = 1 by ring, Real.rpow_one]
    _ ≤ (N : ℝ) ^ (1 - 2 * r) * L ^ (2 * r) := by gcongr
    _ = (N : ℝ) ^ (1 - 2 * r) *
        lambda ^ (-2 * r / (k : ℝ)) := by rw [hlambdaPower]
    _ = _ := by rfl

#print axioms heathBrownKthDerivativeFactor_eq_critical
#print axioms heathBrownThreeTerm_scaled_identity
#print axioms heathBrown_lambda_power_identity
#print axioms heathBrown_lambda_term_le_third_of_third_le_N

end

end GafniTao
