import GafniTao.FordLemma51Holder
import Mathlib.Analysis.MeanInequalities

/-!
# Ford Lemma 5.1: the second Hölder inequality

This file isolates the exact three-factor Hölder estimate used in Ford's
equation (5.3).  The three factors are the total representation count, its
square moment, and the `2s`-moment of the oscillatory fiber sum.
-/

open Finset
open scoped NNReal

namespace GafniTao

noncomputable section

/-- The root form of Ford's second Hölder application. -/
theorem ford_second_holder_root
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w f : ι → ℝ≥0)
    {s : ℕ} (hs : 1 ≤ s) :
    ∑ i ∈ S, w i * f i ≤
      (∑ i ∈ S, w i) ^ (1 - ((s : ℝ)⁻¹)) *
        (∑ i ∈ S, w i ^ (2 : ℝ)) ^ (1 / (2 * (s : ℝ))) *
        (∑ i ∈ S, f i ^ (2 * (s : ℝ))) ^ (1 / (2 * (s : ℝ))) := by
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsPos : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le zero_lt_one hsR
  have hweighted := NNReal.inner_le_weight_mul_Lp S hsR w f
  have hcauchy := NNReal.inner_le_Lp_mul_Lq S w (fun i => f i ^ (s : ℝ))
    Real.HolderConjugate.two_two
  have hpow :
      (∑ i ∈ S, w i * f i ^ (s : ℝ)) ^ ((s : ℝ)⁻¹) ≤
        ((∑ i ∈ S, w i ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) *
          (∑ i ∈ S, f i ^ (2 * (s : ℝ))) ^ ((2 : ℝ)⁻¹)) ^ ((s : ℝ)⁻¹) := by
    apply NNReal.rpow_le_rpow
    · convert hcauchy using 1
      all_goals simp only [one_div, ← NNReal.rpow_mul, mul_comm]
    · exact inv_nonneg.mpr hsPos.le
  calc
    ∑ i ∈ S, w i * f i ≤
        (∑ i ∈ S, w i) ^ (1 - ((s : ℝ)⁻¹)) *
          (∑ i ∈ S, w i * f i ^ (s : ℝ)) ^ ((s : ℝ)⁻¹) := by
      simpa [one_div] using hweighted
    _ ≤ (∑ i ∈ S, w i) ^ (1 - ((s : ℝ)⁻¹)) *
          (((∑ i ∈ S, w i ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) *
            (∑ i ∈ S, f i ^ (2 * (s : ℝ))) ^ ((2 : ℝ)⁻¹)) ^
              ((s : ℝ)⁻¹)) := by
      gcongr
    _ = (∑ i ∈ S, w i) ^ (1 - ((s : ℝ)⁻¹)) *
          (∑ i ∈ S, w i ^ (2 : ℝ)) ^ (1 / (2 * (s : ℝ))) *
          (∑ i ∈ S, f i ^ (2 * (s : ℝ))) ^ (1 / (2 * (s : ℝ))) := by
      rw [NNReal.mul_rpow]
      simp only [← NNReal.rpow_mul]
      have hcalc : (2 : ℝ)⁻¹ * (s : ℝ)⁻¹ = 1 / (2 * (s : ℝ)) := by
        field_simp
      rw [hcalc]
      ac_rfl

/-- Ford's second Hölder inequality in the integer-power form appearing in
equation (5.3). -/
theorem ford_second_holder_power
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w f : ι → ℝ≥0)
    {s : ℕ} (hs : 1 ≤ s) :
    (∑ i ∈ S, w i * f i) ^ (2 * s) ≤
      (∑ i ∈ S, w i) ^ (2 * s - 2) *
        (∑ i ∈ S, w i ^ 2) *
        (∑ i ∈ S, f i ^ (2 * s)) := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have h := NNReal.rpow_le_rpow (ford_second_holder_root S w f hs)
    (show (0 : ℝ) ≤ (2 * s : ℕ) by positivity)
  have hTwo : 2 ≤ 2 * s := by omega
  have hA :
      (1 - (s : ℝ)⁻¹) * (2 * (s : ℝ)) = ((2 * s - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hTwo]
    push_cast
    field_simp
  have hBC : (1 / (2 * (s : ℝ))) * (2 * (s : ℝ)) = 1 := by
    field_simp
  have hTwoS : (2 * (s : ℝ)) = ((2 * s : ℕ) : ℝ) := by norm_num
  simp_rw [NNReal.mul_rpow, ← NNReal.rpow_mul] at h
  rw [← hTwoS] at h
  rw [hA, hBC] at h
  simp only [NNReal.rpow_one] at h
  have hw2 :
      (∑ i ∈ S, w i ^ (2 : ℝ)) = ∑ i ∈ S, w i ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact NNReal.rpow_natCast (w i) 2
  rw [hw2] at h
  simpa only [hTwoS, NNReal.rpow_natCast, NNReal.rpow_one] using h

#print axioms ford_second_holder_root
#print axioms ford_second_holder_power

end

end GafniTao
