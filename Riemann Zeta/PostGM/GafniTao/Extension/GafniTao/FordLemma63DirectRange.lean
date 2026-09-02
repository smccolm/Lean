import GafniTao.FordLemma63DirectPowerSaving
import GafniTao.FordCorollary64Range

/-!
# Ford's direct Lemma-6.3 range

This is the interval `13 / 5 ≤ λ ≤ 4` left between Ford's elementary
shifted-Weyl treatment and Corollary 6.4.  We use the source choice `k = 4`,
`P = N^(1-λ/5)` and the already proved fifteen-block Lemma-6.5 moment.
The resulting constant is qualitative; the exponent saving is explicit.
-/

namespace GafniTao

noncomputable section

def fordDirectMomentCoefficient : ℝ := fordCor64MomentCoefficient 4

def fordDirectCoefficient : ℝ :=
  fordLemma63DirectCoefficient (fordModerateMomentDegree 4)
    fordDirectMomentCoefficient

theorem fordDirectCoefficient_nonneg : 0 ≤ fordDirectCoefficient := by
  unfold fordDirectCoefficient fordLemma63DirectCoefficient
  have hC : 0 ≤ fordDirectMomentCoefficient := by
    exact fordCor64MomentCoefficient_nonneg 4
  positivity

theorem ford_direct_saving_bounds
    {lambda : ℝ} (hlower : 13 / 5 ≤ lambda) (hupper : lambda ≤ 4) :
    1 / (1000 * lambda ^ 2) ≤
        fordLemma63DirectSaving (fordModerateMomentDegree 4)
          (fordModerateMomentDelta 4) lambda ∧
      fordLemma63DirectSaving (fordModerateMomentDegree 4)
          (fordModerateMomentDelta 4) lambda ≤ fordLemma63DirectMu lambda ∧
      fordLemma63DirectSaving (fordModerateMomentDegree 4)
          (fordModerateMomentDelta 4) lambda ≤
        1 - fordLemma63DirectMu lambda := by
  let delta := fordModerateMomentDelta 4
  let c := fordLemma63DirectSaving (fordModerateMomentDegree 4) delta lambda
  have hlambdaPos : 0 < lambda := by linarith
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact fordModerateMomentDelta_nonneg (by norm_num)
  have hdeltaTop : delta ≤ (1 / 4096 : ℝ) := by
    dsimp [delta]
    have h := fordModerateMomentDelta_le (k := 4) (by norm_num)
    norm_num at h ⊢
    exact h
  have hsEq : (fordModerateMomentDegree 4 : ℝ) = 244 := by
    norm_num [fordModerateMomentDegree]
  have hcEq : c =
      (lambda / 5 - (1 - lambda / 5) * delta) / 488 := by
    dsimp [c, fordLemma63DirectSaving, fordLemma63DirectMu]
    rw [hsEq]
    ring
  have hmu0 : 0 ≤ 1 - lambda / 5 := by linarith
  have hmuTop : 1 - lambda / 5 ≤ (12 / 25 : ℝ) := by linarith
  have hdeltaProd : (1 - lambda / 5) * delta ≤
      (12 / 25 : ℝ) * (1 / 4096 : ℝ) := by gcongr
  have hnumLower : (13 / 25 : ℝ) - (12 / 25 : ℝ) / 4096 ≤
      lambda / 5 - (1 - lambda / 5) * delta := by linarith
  have hcLowerConst : (1 / 1000 : ℝ) ≤ c := by
    rw [hcEq, le_div_iff₀ (by norm_num : (0 : ℝ) < 488)]
    norm_num at hnumLower ⊢
    linarith
  have htarget : 1 / (1000 * lambda ^ 2) ≤ (1 / 1000 : ℝ) := by
    have hsquare : (1 : ℝ) ≤ lambda ^ 2 := by nlinarith
    have hden : (1000 : ℝ) ≤ 1000 * lambda ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hcUpper : c ≤ 1 / 488 := by
    rw [hcEq]
    have hnum : lambda / 5 - (1 - lambda / 5) * delta ≤ 1 := by
      have : 0 ≤ (1 - lambda / 5) * delta := mul_nonneg hmu0 hdelta0
      linarith
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 488)).2 (by linarith)
  have hcMu : c ≤ 1 - lambda / 5 := by
    have : (1 / 488 : ℝ) ≤ 1 / 5 := by norm_num
    linarith
  have hcOneMu : c ≤ lambda / 5 := by
    have : (1 / 488 : ℝ) ≤ 13 / 25 := by norm_num
    linarith
  dsimp [c, delta] at hcMu hcOneMu hcLowerConst ⊢
  exact ⟨htarget.trans hcLowerConst, hcMu, by
    simpa [fordLemma63DirectMu] using hcOneMu⟩

theorem ford_shifted_exponential_sum_direct_range
    {N R : ℕ} {u t : ℝ}
    (hN : 2 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (hlambda : 13 / 5 ≤ fordLambda N t)
    (hlambdaTop : fordLambda N t ≤ 4) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordDirectCoefficient * (N : ℝ) ^
        (1 - 1 / (1000 * fordLambda N t ^ 2)) := by
  let lambda := fordLambda N t
  let s := fordModerateMomentDegree 4
  let delta := fordModerateMomentDelta 4
  let C := fordDirectMomentCoefficient
  let P : ℝ := (N : ℝ) ^ fordLemma63DirectMu lambda
  have hs : 1 ≤ s := by simp [s, fordModerateMomentDegree]
  have hmoment : FordVinogradovMomentBound s 4 C delta := by
    dsimp [s, C, delta, fordDirectMomentCoefficient]
    exact fordCor64MomentCoefficient_bound (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C, fordDirectMomentCoefficient]
    exact fordCor64MomentCoefficient_nonneg 4
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact fordModerateMomentDelta_nonneg (by norm_num)
  have hmu0 : 0 ≤ fordLemma63DirectMu lambda := by
    unfold fordLemma63DirectMu
    linarith
  have hmu1 : fordLemma63DirectMu lambda ≤ 1 := by
    unfold fordLemma63DirectMu
    have : 0 ≤ lambda := by linarith
    linarith
  obtain ⟨hcLower, hcMu, hcOneMu⟩ :=
    ford_direct_saving_bounds hlambda hlambdaTop
  have hsource := fordLemma63_direct_le_power_saving
    (s := s) (N := N) (R := R) (P := P) (u := u) (t := t)
    (lambda := lambda) (C := C) (delta := delta)
    hs (by omega) hRlower hR hu0 hu1 hlambdaTop
      hmu0 hmu1 (ford_rpow_lambda_eq_height (by omega) ht).symm rfl
      hC hmoment hcMu hcOneMu
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^
      (1 - fordLemma63DirectSaving s delta lambda) ≤
      (N : ℝ) ^ (1 - 1 / (1000 * lambda ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    linarith
  apply hsource.trans
  dsimp [fordDirectCoefficient, s, C]
  exact mul_le_mul_of_nonneg_left hpow fordDirectCoefficient_nonneg

#print axioms ford_direct_saving_bounds
#print axioms ford_shifted_exponential_sum_direct_range

end

end GafniTao
