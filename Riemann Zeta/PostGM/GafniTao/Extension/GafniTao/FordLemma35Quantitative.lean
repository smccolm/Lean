import GafniTao.FordLemma34Explicit

/-!
# Ford Lemma 3.5 with an explicit finite-prefix coefficient

The earlier global theorem used an existential maximum over an unspecified
eventual endpoint.  This file replaces it by the ceiling of the quantitative
Lemma 3.4 endpoint.  Consequently every later recurrence coefficient is a
literal expression in the previous coefficient, `s`, `k`, and one fixed PNT
constant.
-/

namespace GafniTao

noncomputable section

/-- Integral endpoint above which the quantitative Lemma 3.4 applies. -/
def fordLemma34Endpoint (s k : ℕ) : ℕ :=
  ⌈fordLemma34ExplicitThreshold s k⌉₊

/-- The exact finite-prefix repair coefficient for one recurrence step. -/
def fordStepGlobalCoefficient (s k : ℕ) (C : ℝ) : ℝ :=
  max (fordStepCoefficient35 s k C (53 / 50 : ℝ))
    ((fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k)))

theorem fordLemma34Threshold_le_endpoint (s k : ℕ) :
    fordLemma34ExplicitThreshold s k ≤ (fordLemma34Endpoint s k : ℝ) := by
  exact Nat.le_ceil _

/-- The source one-step estimate above the explicit endpoint. -/
theorem ford_lemma_3_5_one_step_above_endpoint
    {s k r : ℕ} {C delta : ℝ}
    (hk : 1000 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hy : 0 ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤ fordPhiStar35 k r delta)
    (hmoment : FordVinogradovMomentBound s k C delta)
    {Q : ℕ} (hQEndpoint : fordLemma34Endpoint s k ≤ Q) :
    (fordVinogradovMomentNat (s + k) k Q : ℝ) ≤
      fordStepCoefficient35 s k C (53 / 50 : ℝ) *
        (Q : ℝ) ^ fordLambda34 (s + k) k (fordDeltaZero35 k r delta) := by
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  have hj : 2 ≤ j := fordJ35_lower hr hy
  have hjr : 10 * j ≤ 9 * r := fordJ35_ten_mul_le_nine_mul
  have h38Y : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta :=
    (fordJ35_admissible hr hy).2
  have h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ) :=
    fordJ35_equation_3_8 hr hrk hy
  have hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / (((k + 1 : ℕ) : ℝ)) ≤ Φ.phi i :=
    fordCanonicalPhiSchedule_lower (show 1 ≤ k by omega)
      (show 1 ≤ r by omega) h38Y hdelta hstar
  have hthreshold : fordLemma34ExplicitThreshold s k ≤ (Q : ℝ) :=
    (fordLemma34Threshold_le_endpoint s k).trans (by exact_mod_cast hQEndpoint)
  have hreal := ford_lemma_3_4_explicit Φ hk hr hrk hks hj hjr h38 hlower
    hmoment hthreshold
  simpa only [fordVinogradovMoment, Nat.floor_natCast, fordDeltaZero35,
    fordLambda34, Nat.cast_add, Φ, j] using hreal

/-- Quantitative all-positive-endpoint recurrence. -/
theorem ford_lemma_3_5_one_step_global_quantitative
    {s k r : ℕ} {C delta : ℝ}
    (hk : 1000 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hy : 0 ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤ fordPhiStar35 k r delta)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    FordVinogradovMomentBound (s + k) k
      (fordStepGlobalCoefficient s k C) (fordDeltaZero35 k r delta) := by
  have hC : 0 ≤ C :=
    zero_le_one.trans (hmoment.one_le_coefficient)
  have hstepNonneg : 0 ≤ fordStepCoefficient35 s k C (53 / 50 : ℝ) := by
    unfold fordStepCoefficient35
    positivity
  have hlambda : 0 ≤ fordLambda34 (s + k) k (fordDeltaZero35 k r delta) := by
    have heventual := eventually_ford_lemma_3_5_one_step
      (eta := (53 / 50 : ℝ)) (omega := (3 / 50 : ℝ))
      (by omega : 26 ≤ k)
      hr hrk hks hy hdelta hstar
      (by
        have hlog := ford_log_k_lower hk
        have hlog0 : 0 < Real.log (k : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < k by omega))
        rw [div_le_iff₀ (by positivity : 0 < 3 * Real.log (k : ℝ))]
        nlinarith)
      (by norm_num) (by norm_num) hmoment
    exact heventual.lambda_nonneg
  intro Q hQ
  by_cases hlarge : fordLemma34Endpoint s k ≤ Q
  · have hsource := ford_lemma_3_5_one_step_above_endpoint hk hr hrk hks
      hy hdelta hstar hmoment hlarge
    exact hsource.trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · have hQR : Q ≤ fordLemma34Endpoint s k := by omega
    have htrivialNat := fordVinogradovMomentNat_le_trivial (s + k) k Q
    have htrivial : (fordVinogradovMomentNat (s + k) k Q : ℝ) ≤
        (Q : ℝ) ^ (2 * (s + k)) := by exact_mod_cast htrivialNat
    have hpower : (Q : ℝ) ^ (2 * (s + k)) ≤
        (fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k)) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQR) _
    have htoCoefficient : (fordVinogradovMomentNat (s + k) k Q : ℝ) ≤
        fordStepGlobalCoefficient s k C :=
      htrivial.trans (hpower.trans (le_max_right _ _))
    have hglobalNonneg : 0 ≤ fordStepGlobalCoefficient s k C :=
      hstepNonneg.trans (le_max_left _ _)
    have hQrpow : 1 ≤ (Q : ℝ) ^
        fordLambda34 (s + k) k (fordDeltaZero35 k r delta) :=
      Real.one_le_rpow (by exact_mod_cast hQ) hlambda
    exact htoCoefficient.trans (by
      calc
        fordStepGlobalCoefficient s k C =
            fordStepGlobalCoefficient s k C * 1 := by ring
        _ ≤ fordStepGlobalCoefficient s k C *
            (Q : ℝ) ^ fordLambda34 (s + k) k
              (fordDeltaZero35 k r delta) := by gcongr)

#print axioms fordLemma34Threshold_le_endpoint
#print axioms ford_lemma_3_5_one_step_above_endpoint
#print axioms ford_lemma_3_5_one_step_global_quantitative

end

end GafniTao
