import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
open scoped BigOperators
namespace HuxleyCubicCompletionWeightScratch
private theorem cubic_completion_weight_bound
    {Q q μ₀ μ N A : ℝ}
    (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : Q ≤ 2*q) (hμ : μ₀ ≤ μ) (hNA : N ≤ A) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) := by
  have hq : 0 < q := by linarith only [hQ,hQq]
  have hμp := hμ₀.trans_le hμ
  have hAp := hN.trans_le hNA
  have hμA := mul_pos hμp hAp
  have hμN : μ₀*N ≤ μ*A := mul_le_mul hμ hNA hN.le hμp.le
  have hden := mul_pos hQ (mul_pos hμ₀ hN)
  have hright : 0 ≤ 4/(Q*(μ₀*N)) := div_nonneg (by norm_num) hden.le
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq.le (Real.sqrt_nonneg _)))
    (Real.sqrt_nonneg _)).mp
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*q),
    Real.sq_sqrt hμA.le,Real.sq_sqrt hright]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hq 2) hμA) hden).mpr
  have hm := mul_le_mul hQq hμN (mul_nonneg hμ₀.le hN.le) (by positivity : 0 ≤ 2*q)
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*q)
  nlinarith only [hh]

private theorem cubic_completion_weighted_twelfth
    {ι : Type*} (S : Finset ι) (q μ A : ι → ℝ) (z : ι → ℂ)
    {Q μ₀ N : ℝ} (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : ∀ i∈S, Q ≤ 2*q i) (hμ : ∀ i∈S, μ₀ ≤ μ i)
    (hNA : ∀ i∈S, N ≤ A i) :
    (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖)^12 ≤
      (4/(Q*(μ₀*N)))^6*(∑ i∈S,‖z i‖)^12 := by
  let B := 4/(Q*(μ₀*N))
  have hB : 0 ≤ B := div_nonneg (by norm_num) (mul_nonneg hQ.le (mul_nonneg hμ₀.le hN.le))
  have hweight i (hi : i∈S) :
      Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) ≤ Real.sqrt B :=
    cubic_completion_weight_bound hQ hμ₀ hN (hQq i hi) (hμ i hi) (hNA i hi)
  have hweightNonneg i (hi : i∈S) :
      0 ≤ Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) := by
    have hq : 0 ≤ q i := by linarith only [hQ,hQq i hi]
    exact div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq (Real.sqrt_nonneg _))
  have hs : (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖) ≤
      Real.sqrt B*(∑ i∈S,‖z i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hweight i hi) (norm_nonneg _)
  have hs0 : 0 ≤ ∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖ :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hweightNonneg i hi) (norm_nonneg _))
  have hp := pow_le_pow_left₀ hs0 hs 12
  have hpow : (Real.sqrt B)^12=B^6 := by
    rw [show (12:ℕ)=2*6 by norm_num,pow_mul,Real.sq_sqrt hB]
  rw [mul_pow,hpow] at hp
  exact hp

example
    {Q q μ₀ μ N A : ℝ}
    (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : Q ≤ 2*q) (hμ : μ₀ ≤ μ) (hNA : N ≤ A) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) :=
  HuxleyCubicCompletionWeightScratch.cubic_completion_weight_bound (Q:=Q) (q:=q) (μ₀:=μ₀) (μ:=μ) (N:=N) (A:=A) hQ hμ₀ hN hQq hμ hNA

example
    {ι : Type*} (S : Finset ι) (q μ A : ι → ℝ) (z : ι → ℂ)
    {Q μ₀ N : ℝ} (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : ∀ i∈S, Q ≤ 2*q i) (hμ : ∀ i∈S, μ₀ ≤ μ i)
    (hNA : ∀ i∈S, N ≤ A i) :
    (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖)^12 ≤
      (4/(Q*(μ₀*N)))^6*(∑ i∈S,‖z i‖)^12 :=
  HuxleyCubicCompletionWeightScratch.cubic_completion_weighted_twelfth (ι:=ι) S q μ A z (Q:=Q) (μ₀:=μ₀) (N:=N) hQ hμ₀ hN hQq hμ hNA

#print axioms cubic_completion_weight_bound
#print axioms cubic_completion_weighted_twelfth
end HuxleyCubicCompletionWeightScratch
