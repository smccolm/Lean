import GafniTao.FordCorollary64Overlap
import GafniTao.FordScaledCoreCompact

/-!
# Ford Corollary 6.4: insertion of the Vinogradov moment estimate

This is the exact exponent cancellation in the leading term of Lemma 6.3.
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_scale_power_identity
    {s k M : ℕ} {delta : ℝ} (hM : 1 ≤ M) :
    (M : ℝ) ^ fordVinogradovKappa k * M *
        (M : ℝ) ^ fordLambda34 s k delta =
      (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  calc
    (M : ℝ) ^ fordVinogradovKappa k * M *
          (M : ℝ) ^ fordLambda34 s k delta =
        (M : ℝ) ^ (fordVinogradovKappa k : ℝ) *
          (M : ℝ) ^ (1 : ℝ) *
          (M : ℝ) ^ fordLambda34 s k delta := by
            rw [Real.rpow_natCast, Real.rpow_one]
    _ = (M : ℝ) ^
        ((fordVinogradovKappa k : ℝ) + 1 +
          fordLambda34 s k delta) := by
      rw [← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
    _ = (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta) := by
      congr 1
      rw [fordVinogradovKappa_cast]
      unfold fordLambda34
      ring

theorem fordCorollary64_moment_factor_le
    {s k M N : ℕ} {t C delta : ℝ}
    (hM : 1 ≤ M) (ht : 0 < t)
    (hW : fordLemma63W N k M t ≤ (2 : ℝ) ^ k * M)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) *
        fordLemma63W N k M t *
        (fordVinogradovMomentNat s k M : ℝ) ≤
      (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta) := by
  have hJ := hmoment M hM
  have hD : 0 ≤ Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
      (M : ℝ) ^ fordVinogradovKappa k := by positivity
  have hW0 : 0 ≤ fordLemma63W N k M t := by
    unfold fordLemma63W
    positivity
  have hJ0 : 0 ≤ (fordVinogradovMomentNat s k M : ℝ) := by positivity
  calc
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) *
        fordLemma63W N k M t *
        (fordVinogradovMomentNat s k M : ℝ) ≤
      (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) *
        ((2 : ℝ) ^ k * M) *
        (C * (M : ℝ) ^ fordLambda34 s k delta) := by
          gcongr
    _ = (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        ((M : ℝ) ^ fordVinogradovKappa k * M *
          (M : ℝ) ^ fordLambda34 s k delta) := by
      rw [mul_pow]
      ring
    _ = (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        (M : ℝ) ^ (2 * (s : ℝ) + 1 + delta) := by
      rw [fordCorollary64_scale_power_identity hM]

#print axioms fordCorollary64_scale_power_identity
#print axioms fordCorollary64_moment_factor_le

end

end GafniTao
