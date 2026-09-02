import GafniTao.FordLemma65Iteration
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantitative decay in Ford's Lemma 6.5 iteration

Fifteen blocks of `k` iterations suffice for the moderate-degree application.
The proof keeps the elementary source contraction explicit: first
`(1-1/k)^k < 1/2`, then fifteen powers give `1/32768`.
-/

namespace GafniTao

noncomputable section

theorem ford_one_sub_inv_pow_le_half
    {k : ℕ} (hk : 2 ≤ k) :
    (1 - 1 / (k : ℝ)) ^ k ≤ (1 / 2 : ℝ) := by
  let q : ℝ := 1 - 1 / (k : ℝ)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by linarith
  have hqPos : 0 < q := by
    dsimp [q]
    rw [sub_pos, div_lt_one hkPos]
    linarith
  have hlog := Real.log_le_sub_one_of_pos hqPos
  have hmul : (k : ℝ) * Real.log q ≤ (k : ℝ) * (q - 1) :=
    mul_le_mul_of_nonneg_left hlog hkPos.le
  have hright : (k : ℝ) * (q - 1) = -1 := by
    dsimp [q]
    field_simp
  have hexp : Real.exp ((k : ℝ) * Real.log q) ≤ Real.exp (-1) := by
    rw [Real.exp_le_exp]
    linarith
  have hpow : q ^ k ≤ Real.exp (-1) := by
    rw [← Real.exp_log hqPos, ← Real.exp_nat_mul]
    exact hexp
  exact hpow.trans Real.exp_neg_one_lt_half.le

theorem ford_one_sub_inv_pow_fifteen_blocks
    {k : ℕ} (hk : 4 ≤ k) :
    (1 - 1 / (k : ℝ)) ^ (15 * k) ≤ (1 / 32768 : ℝ) := by
  have hq0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact sub_nonneg.mpr (div_le_one (by positivity) |>.2 hkR)
  have hhalf := ford_one_sub_inv_pow_le_half (by omega : 2 ≤ k)
  calc
    (1 - 1 / (k : ℝ)) ^ (15 * k) =
        ((1 - 1 / (k : ℝ)) ^ k) ^ 15 := by rw [mul_comm, pow_mul]
    _ ≤ ((1 / 2 : ℝ)) ^ 15 := pow_le_pow_left₀ (pow_nonneg hq0 _) hhalf 15
    _ = (1 / 32768 : ℝ) := by norm_num

def fordModerateMomentDegree (k : ℕ) : ℕ := (15 * k + 1) * k

def fordModerateMomentDelta (k : ℕ) : ℝ :=
  fordDeltaInitial35 k * (1 - 1 / (k : ℝ)) ^ (15 * k)

theorem fordModerateMomentDelta_nonneg
    {k : ℕ} (hk : 4 ≤ k) :
    0 ≤ fordModerateMomentDelta k := by
  unfold fordModerateMomentDelta fordDeltaInitial35
  have hkR : (0 : ℝ) ≤ k := by positivity
  positivity

theorem fordModerateMomentDelta_le
    {k : ℕ} (hk : 4 ≤ k) :
    fordModerateMomentDelta k ≤ (k : ℝ) ^ 2 / 65536 := by
  have hpow := ford_one_sub_inv_pow_fifteen_blocks hk
  have hdelta0 : 0 ≤ fordDeltaInitial35 k := by
    unfold fordDeltaInitial35
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hdeltaTop : fordDeltaInitial35 k ≤ (k : ℝ) ^ 2 / 2 := by
    unfold fordDeltaInitial35
    have hkR : (0 : ℝ) ≤ k := by positivity
    linarith
  unfold fordModerateMomentDelta
  calc
    fordDeltaInitial35 k * (1 - 1 / (k : ℝ)) ^ (15 * k) ≤
        fordDeltaInitial35 k * (1 / 32768 : ℝ) := by gcongr
    _ ≤ ((k : ℝ) ^ 2 / 2) * (1 / 32768 : ℝ) := by gcongr
    _ = (k : ℝ) ^ 2 / 65536 := by ring

theorem ford_moderate_moment_bound
    {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, FordVinogradovMomentBound
      (fordModerateMomentDegree k) k C (fordModerateMomentDelta k) := by
  obtain ⟨C, hC⟩ := fordDeltaSequence65_moment_bound
    (k := k) (n := 15 * k) hk
  refine ⟨C, ?_⟩
  simpa [fordModerateMomentDegree, fordModerateMomentDelta,
    fordDeltaSequence65_closed, Nat.add_mul] using hC

#print axioms ford_one_sub_inv_pow_le_half
#print axioms ford_one_sub_inv_pow_fifteen_blocks
#print axioms fordModerateMomentDelta_le
#print axioms ford_moderate_moment_bound

end

end GafniTao
