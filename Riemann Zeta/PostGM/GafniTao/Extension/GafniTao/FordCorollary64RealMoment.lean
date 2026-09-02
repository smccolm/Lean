import GafniTao.FordCorollary64RealOverlap
import GafniTao.FordMomentReal
import GafniTao.FordScaledCoreCompact

/-!
# Ford Corollary 6.4: the moment estimate at a real scale

Ford's cutoff `P = N^μ` is real.  The finite Vinogradov system therefore ends
at `⌊P⌋`, while the scale factors in Lemma 6.3 and Corollary 6.4 remain the
literal real `P`.  This module inserts the natural-endpoint mean-value theorem
through its proved real-endpoint bridge without an integrality hypothesis.
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_real_scale_power_identity
    {s k : ℕ} {P delta : ℝ} (hP : 0 < P) :
    P ^ fordVinogradovKappa k * P *
        P ^ fordLambda34 s k delta =
      P ^ (2 * (s : ℝ) + 1 + delta) := by
  calc
    P ^ fordVinogradovKappa k * P * P ^ fordLambda34 s k delta =
        P ^ (fordVinogradovKappa k : ℝ) * P ^ (1 : ℝ) *
          P ^ fordLambda34 s k delta := by
      rw [Real.rpow_natCast, Real.rpow_one]
    _ = P ^ ((fordVinogradovKappa k : ℝ) + 1 +
        fordLambda34 s k delta) := by
      rw [← Real.rpow_add hP, ← Real.rpow_add hP]
    _ = P ^ (2 * (s : ℝ) + 1 + delta) := by
      congr 1
      rw [fordVinogradovKappa_cast]
      unfold fordLambda34
      ring

theorem fordCorollary64_real_moment_factor_le
    {s k N : ℕ} {P t C delta : ℝ}
    (hP : 1 ≤ P) (ht : 0 < t)
    (hW : fordLemma63WReal N k P t ≤ (2 : ℝ) ^ k * P)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          P ^ fordVinogradovKappa k) *
        fordLemma63WReal N k P t *
        (fordVinogradovMoment s k P : ℝ) ≤
      (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        P ^ (2 * (s : ℝ) + 1 + delta) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hJ := hmoment.real_endpoint hP
  have hD : 0 ≤ Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
      P ^ fordVinogradovKappa k := by positivity
  have hW0 : 0 ≤ fordLemma63WReal N k P t := by
    unfold fordLemma63WReal
    positivity
  calc
    (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          P ^ fordVinogradovKappa k) *
        fordLemma63WReal N k P t *
        (fordVinogradovMoment s k P : ℝ) ≤
      (Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
          P ^ fordVinogradovKappa k) *
        ((2 : ℝ) ^ k * P) *
        (C * P ^ fordLambda34 s k delta) := by
          gcongr
    _ = (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        (P ^ fordVinogradovKappa k * P *
          P ^ fordLambda34 s k delta) := by
      rw [mul_pow]
      ring
    _ = (C * (2 * Real.pi * k) ^ k * (k.factorial : ℝ)) *
        P ^ (2 * (s : ℝ) + 1 + delta) := by
      rw [fordCorollary64_real_scale_power_identity hPpos]

#print axioms fordCorollary64_real_scale_power_identity
#print axioms fordCorollary64_real_moment_factor_le

end

end GafniTao
