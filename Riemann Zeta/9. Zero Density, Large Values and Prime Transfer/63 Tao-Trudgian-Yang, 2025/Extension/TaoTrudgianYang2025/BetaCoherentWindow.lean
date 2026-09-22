import TaoTrudgianYang2025.BetaTwistedLogCoherence

/-!
# A genuine coherent block of length N/sqrt(T)

The integer length is rounded down, but the closed sum has L+1 terms.
This preserves the lower bound even when the rounded length is zero.
All selected endpoints remain inside the original dyadic source block.
-/

noncomputable section

open Expdb RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

def betaCoherentLength (T N : ℝ) : ℕ := ⌊N/(4*Real.sqrt T)⌋₊

theorem betaCoherentLength_le_scale {T N : ℝ} (hT : 1 ≤ T) (hN : 0 ≤ N) :
    (betaCoherentLength T N : ℝ) ≤ N := by
  have hs : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  exact (Nat.floor_le (by positivity : 0 ≤ N/(4*Real.sqrt T))).trans
    (div_le_self hN (by linarith))

theorem betaCoherentLength_quadratic_budget {T N : ℝ}
    (hT : 1 ≤ T) (hN : 0 < N) {j : ℕ}
    (hj : j ≤ betaCoherentLength T N) :
    T*(j : ℝ)^2/N^2 ≤ 1/16 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hjreal : (j : ℝ) ≤ N/(4*Real.sqrt T) :=
    (show (j : ℝ) ≤ betaCoherentLength T N by exact_mod_cast hj).trans
      (Nat.floor_le (by positivity))
  have hprod : (j : ℝ)*(4*Real.sqrt T) ≤ N := (le_div_iff₀ (by positivity)).mp hjreal
  have hsq : ((j : ℝ)*(4*Real.sqrt T))^2 ≤ N^2 :=
    (sq_le_sq₀ (by positivity) hN.le).mpr hprod
  simp only [mul_pow,Real.sq_sqrt hTpos.le] at hsq
  apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
  nlinarith

theorem betaCoherentLength_count_lower {T N : ℝ} :
    N/(8*Real.sqrt T) ≤ ((betaCoherentLength T N : ℝ)+1)/2 := by
  have hcount := Nat.lt_floor_add_one (N/(4*Real.sqrt T))
  change N/(8*Real.sqrt T) ≤ ((⌊N/(4*Real.sqrt T)⌋₊ : ℝ)+1)/2
  rw [show N/(8*Real.sqrt T) = (N/(4*Real.sqrt T))/2 by ring]
  linarith

theorem betaCoherentLength_source_end {T : ℝ} (hT : 1 ≤ T) (N : ℕ) :
    ((N+betaCoherentLength T N : ℕ) : ℝ) ≤ 2*(N : ℝ) := by
  rw [Nat.cast_add]
  linarith [betaCoherentLength_le_scale hT (Nat.cast_nonneg N)]

theorem norm_twistedLog_coherent_sum_lower {T : ℝ} {N : ℕ}
    (hT : 1 ≤ T) (hN : 1 ≤ N) :
    (N : ℝ)/(8*Real.sqrt T) ≤
      ‖exponentialSumAt (twistedLogPhase (betaResonantCorrection T N)) T N
        N (N+betaCoherentLength T N)‖ := by
  let L := betaCoherentLength T N
  let c := betaResonantCorrection T N
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hinteger := betaResonantCorrection_integer_slope hTp.ne' hNp.ne'
  have hsum : exponentialSumAt (twistedLogPhase c) T N N (N+L) =
      ∑ j ∈ Finset.range (L+1), oscillatory (twistedLogPhase c) T N ((N : ℝ)+j) := by
    unfold exponentialSumAt
    rw [sum_Icc_eq_shifted_range _ N (N+L) (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.cast_add]
  change (N : ℝ)/(8*Real.sqrt T) ≤
    ‖exponentialSumAt (twistedLogPhase c) T N N (N+L)‖
  rw [hsum]
  have hre : ((L : ℝ)+1)/2 ≤
      (∑ j ∈ Finset.range (L+1), oscillatory (twistedLogPhase c) T N ((N : ℝ)+j)).re := by
    have hpoint (j : ℕ) (hj : j ∈ Finset.range (L+1)) :
        (1 : ℝ)/2 ≤ (oscillatory (twistedLogPhase c) T N ((N : ℝ)+j)).re := by
      apply oscillatory_twistedLog_re_ge_half hTp.le hNp ⌈T/(N : ℝ)⌉₊ j hinteger
      exact betaCoherentLength_quadratic_budget hT hNp (by
        have hm := Finset.mem_range.mp hj
        omega)
    have hs := Finset.sum_le_sum hpoint
    simpa [← Complex.re_sum] using hs
  exact betaCoherentLength_count_lower.trans
    (hre.trans (Complex.re_le_norm _))

end TaoTrudgianYang2025
