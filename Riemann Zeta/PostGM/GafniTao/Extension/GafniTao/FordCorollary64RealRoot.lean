import GafniTao.FordCorollary64RealMoment
import GafniTao.FordCorollary64Root

/-!
# Ford Corollary 6.4: root extraction at the literal real scale
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_real_even_root_power
    {s : ℕ} {P : ℝ} (hs : 1 ≤ s) (hP : 0 < P) :
    (P ^ (2 * s : ℕ) : ℝ) ^ (1 / (2 * s : ℝ)) = P := by
  have hsR : (0 : ℝ) < 2 * s := by
    have : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hs)
    positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  have hexp : ((2 * s : ℕ) : ℝ) * (1 / (2 * s : ℝ)) = 1 := by
    push_cast
    field_simp [ne_of_gt hsR]
  rw [hexp, Real.rpow_one]

theorem fordCorollary64_real_root_cancel
    {s : ℕ} {P A delta : ℝ}
    (hs : 1 ≤ s) (hP : 0 < P) (hA : 0 ≤ A) :
    (1 / P) *
        (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) =
      (A * P ^ (1 + delta)) ^ (1 / (2 * s : ℝ)) := by
  have htail : 0 ≤ P ^ (1 + delta) := Real.rpow_nonneg hP.le _
  have hsplit :
      P ^ (2 * (s : ℝ) + 1 + delta) =
        P ^ (2 * s : ℕ) * P ^ (1 + delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hP]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have hmain : 0 ≤ P ^ (2 * s : ℕ) := by positivity
  rw [show A * (P ^ (2 * s : ℕ) * P ^ (1 + delta)) =
      P ^ (2 * s : ℕ) * (A * P ^ (1 + delta)) by ring]
  rw [Real.mul_rpow hmain (mul_nonneg hA htail)]
  rw [fordCorollary64_real_even_root_power hs hP]
  field_simp

theorem fordCorollary64_real_root_factor_le
    {s k N : ℕ} {P t C delta lambda : ℝ}
    (hs : 1 ≤ s) (hP : 1 ≤ P) (hN : 1 ≤ N)
    (ht : 0 < t) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k)
    (hPscale : P = (N : ℝ) ^ fordCorollary64Mu k lambda)
    (hW : fordLemma63WReal N k P t ≤ (2 : ℝ) ^ k * P)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    (1 / P) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              P ^ fordVinogradovKappa k) *
            fordLemma63WReal N k P t *
            (fordVinogradovMoment s k P : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
      ((C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
          (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))) ^
        (1 / (2 * s : ℝ)) := by
  let A : ℝ := C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq : 0 ≤ (1 / (2 * s : ℝ)) := by positivity
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hfactor := fordCorollary64_real_moment_factor_le hP ht hW hmoment
  have hroot :
      ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              P ^ fordVinogradovKappa k) *
            fordLemma63WReal N k P t *
            (fordVinogradovMoment s k P : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
        (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) := by
    apply Real.rpow_le_rpow
    · have hW0 : 0 ≤ fordLemma63WReal N k P t := by
        unfold fordLemma63WReal
        positivity
      positivity
    · simpa [A] using hfactor
    · exact hq
  have htail := fordCorollary64_scale_tail_le
    (k := k) (N := (N : ℝ)) (M := P)
    (by exact_mod_cast hN) hdelta hlower hupper hPscale
  calc
    (1 / P) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              P ^ fordVinogradovKappa k) *
            fordLemma63WReal N k P t *
            (fordVinogradovMoment s k P : ℝ)) ^
          (1 / (2 * s : ℝ)) ≤
      (1 / P) *
        (A * P ^ (2 * (s : ℝ) + 1 + delta)) ^
          (1 / (2 * s : ℝ)) := by gcongr
    _ = (A * P ^ (1 + delta)) ^ (1 / (2 * s : ℝ)) :=
      fordCorollary64_real_root_cancel hs hPpos hA
    _ ≤ (A * (N : ℝ) ^ ((2 + 2 * delta) / (k + 1 : ℝ))) ^
          (1 / (2 * s : ℝ)) := by
      apply Real.rpow_le_rpow
      · positivity
      · gcongr
      · exact hq
    _ = _ := by rfl

#print axioms fordCorollary64_real_root_cancel
#print axioms fordCorollary64_real_root_factor_le

end

end GafniTao
