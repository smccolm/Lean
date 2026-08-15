import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

#check Real.one_lt_rpow
#check Real.rpow_lt_rpow
#check Nat.lt_ceil
#check Nat.ceil_lt_add_one
#check Nat.ceil_pos
#check Nat.ceil_mono
#check Nat.ceil_le
#check Nat.cast_sub
#check Nat.le_ceil
#check Real.rpow_le_rpow_of_exponent_le
#check Real.rpow_le_rpow

namespace RiemannZeta.GuthMaynard

noncomputable def testCutoff (Q eta : ℝ) : ℕ :=
  ⌈Q ^ (1 - eta)⌉₊ - 1

theorem testCutoff_spec {Q eta : ℝ} (hQ : 2 ≤ Q)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    1 ≤ testCutoff Q eta ∧
      testCutoff Q eta < ⌈2 * Q⌉₊ ∧
      testCutoff Q eta + 1 = ⌈Q ^ (1 - eta)⌉₊ := by
  have hQ1 : 1 < Q := lt_of_lt_of_le (by norm_num) hQ
  have he : 0 < 1 - eta := by linarith
  have hpow1 : 1 < Q ^ (1 - eta) := Real.one_lt_rpow hQ1 he
  have hceil2 : 2 ≤ ⌈Q ^ (1 - eta)⌉₊ := by
    have hltR : (1 : ℝ) < (⌈Q ^ (1 - eta)⌉₊ : ℝ) :=
      hpow1.trans_le (Nat.le_ceil _)
    have hltN : 1 < ⌈Q ^ (1 - eta)⌉₊ := by exact_mod_cast hltR
    omega
  have hsub : 1 ≤ ⌈Q ^ (1 - eta)⌉₊ - 1 := by omega
  have hpowQ : Q ^ (1 - eta) ≤ Q := by
    have h := Real.rpow_le_rpow_of_exponent_le hQ1.le
      (by linarith : 1 - eta ≤ 1)
    simpa using h
  have hceilLe : ⌈Q ^ (1 - eta)⌉₊ ≤ ⌈Q⌉₊ := Nat.ceil_mono hpowQ
  have hceilQLt : ⌈Q⌉₊ < ⌈2 * Q⌉₊ := by
    have hceilQ : (⌈Q⌉₊ : ℝ) < Q + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2ceil : 2 * Q ≤ (⌈2 * Q⌉₊ : ℝ) := Nat.le_ceil _
    have hGap : Q + 1 ≤ 2 * Q := by linarith
    exact_mod_cast hceilQ.trans_le (hGap.trans h2ceil)
  refine ⟨?_, ?_, ?_⟩
  · simpa [testCutoff] using hsub
  · unfold testCutoff
    omega
  · unfold testCutoff
    omega

theorem testCutoff_scale {Q eta : ℝ} (hQ : 2 ≤ Q)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    Q ^ (1 - eta) ≤ ((testCutoff Q eta + 1 : ℕ) : ℝ) ∧
      ((testCutoff Q eta + 1 : ℕ) : ℝ) ≤ 2 * Q ^ (1 - eta) := by
  have hspec := testCutoff_spec hQ heta0 heta1
  rw [hspec.2.2]
  constructor
  · exact Nat.le_ceil _
  · have hpow1 : 1 ≤ Q ^ (1 - eta) :=
      (Real.one_lt_rpow (lt_of_lt_of_le (by norm_num) hQ) (by linarith)).le
    have hceil : (⌈Q ^ (1 - eta)⌉₊ : ℝ) < Q ^ (1 - eta) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
    linarith

theorem testCutoff_inv_le {Q eta : ℝ} (hQ : 2 ≤ Q)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    (1 / ((testCutoff Q eta + 1 : ℕ) : ℝ)) ≤
      Q ^ (-(1 - eta)) := by
  have hlower := (testCutoff_scale hQ heta0 heta1).1
  have hpow : 0 < Q ^ (1 - eta) := Real.rpow_pos_of_pos (by linarith) _
  have hcut : 0 < ((testCutoff Q eta + 1 : ℕ) : ℝ) := by positivity
  rw [one_div, Real.rpow_neg (by linarith : 0 ≤ Q)]
  exact (inv_le_inv₀ hcut hpow).2 hlower

end RiemannZeta.GuthMaynard
