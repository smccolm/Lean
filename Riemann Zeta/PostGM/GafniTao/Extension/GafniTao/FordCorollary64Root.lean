import GafniTao.FordCorollary64Moment

/-!
# Ford Corollary 6.4: root extraction and scale exponent
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_even_root_power
    {s M : ℕ} (hs : 1 ≤ s) (hM : 1 ≤ M) :
    (((M : ℝ) ^ (2 * s : ℕ) : ℝ) ^
        (1 / (2 * s : ℝ))) = M := by
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hsR : (0 : ℝ) < 2 * s := by
    have : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hs)
    positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]
  have hexp : ((2 * s : ℕ) : ℝ) * (1 / (2 * s : ℝ)) = 1 := by
    push_cast
    field_simp [ne_of_gt hsR]
  rw [hexp, Real.rpow_one]

theorem fordCorollary64_root_cancel
    {s M : ℕ} {A delta : ℝ}
    (hs : 1 ≤ s) (hM : 1 ≤ M) (hA : 0 ≤ A) :
    (1 / (M : ℝ)) *
        (A * (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) =
      (A * (M : ℝ) ^ (1 + delta)) ^
        (1 / (2 * s : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have htail : 0 ≤ (M : ℝ) ^ (1 + delta) := Real.rpow_nonneg hMpos.le _
  have hsplit :
      (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta) =
        (M : ℝ) ^ (2 * s : ℕ) *
          (M : ℝ) ^ (1 + delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hMpos]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have hmain : 0 ≤ (M : ℝ) ^ (2 * s : ℕ) := by positivity
  rw [show A * ((M : ℝ) ^ (2 * s : ℕ) *
      (M : ℝ) ^ (1 + delta)) =
        (M : ℝ) ^ (2 * s : ℕ) *
          (A * (M : ℝ) ^ (1 + delta)) by ring]
  rw [Real.mul_rpow hmain (mul_nonneg hA htail)]
  rw [fordCorollary64_even_root_power hs hM]
  field_simp

theorem fordCorollary64_scale_tail_le
    {k : ℕ} {N M lambda delta : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (hMscale : M = N ^ fordCorollary64Mu k lambda) :
    M ^ (1 + delta) ≤
      N ^ ((2 + 2 * delta) / (k + 1 : ℝ)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmu := (fordCorollary64Mu_bounds hlower hupper).2
  have htail : 0 ≤ 1 + delta := by linarith
  rw [hMscale, ← Real.rpow_mul hNpos.le]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hden : (0 : ℝ) < k + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmu htail
  calc
    fordCorollary64Mu k lambda * (1 + delta) ≤
        (2 / (k + 1 : ℝ)) * (1 + delta) := hmul
    _ = (2 + 2 * delta) / (k + 1 : ℝ) := by
      field_simp [ne_of_gt hden]

theorem fordCorollary64_root_factor_le
    {s k M N : ℕ} {t C delta lambda : ℝ}
    (hs : 1 ≤ s) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (ht : 0 < t) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (hMscale : (M : ℝ) = (N : ℝ) ^ fordCorollary64Mu k lambda)
    (hW : fordLemma63W N k M t ≤ (2 : ℝ) ^ k * M)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    (1 / (M : ℝ)) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              (M : ℝ) ^ fordVinogradovKappa k) *
            fordLemma63W N k M t *
            (fordVinogradovMomentNat s k M : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
      ((C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
          (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))) ^
        (1 / (2 * s : ℝ)) := by
  let A : ℝ := C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq : 0 ≤ (1 / (2 * s : ℝ)) := by positivity
  have hfactor := fordCorollary64_moment_factor_le hM ht hW hmoment
  have hroot :
      ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              (M : ℝ) ^ fordVinogradovKappa k) *
            fordLemma63W N k M t *
            (fordVinogradovMomentNat s k M : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
        (A * (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) := by
    apply Real.rpow_le_rpow
    · have hW0 : 0 ≤ fordLemma63W N k M t := by
        unfold fordLemma63W
        positivity
      positivity
    · simpa [A] using hfactor
    · exact hq
  have htail := fordCorollary64_scale_tail_le
    (k := k) (N := (N : ℝ)) (M := (M : ℝ))
    (by exact_mod_cast hN) hdelta hlower hupper hMscale
  calc
    (1 / (M : ℝ)) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              (M : ℝ) ^ fordVinogradovKappa k) *
            fordLemma63W N k M t *
            (fordVinogradovMomentNat s k M : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
      (1 / (M : ℝ)) *
        (A * (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) := by gcongr
    _ = (A * (M : ℝ) ^ (1 + delta)) ^
      (1 / (2 * s : ℝ)) :=
      fordCorollary64_root_cancel hs hM hA
    _ ≤ (A * (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))) ^
          (1 / (2 * s : ℝ)) := by
      apply Real.rpow_le_rpow
      · positivity
      · gcongr
      · exact hq
    _ = _ := by rfl

#print axioms fordCorollary64_root_cancel
#print axioms fordCorollary64_scale_tail_le
#print axioms fordCorollary64_root_factor_le

end

end GafniTao
