import GafniTao.FordRiemannDadaroRemainder
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Ford Lemma 7.1 on the low-sigma branch

This file proves the ordinary-zeta specialization of the first alternative
in Ford's Lemma 7.1: `1 / 2 ≤ sigma ≤ 15 / 16`.  It uses the exact Dadaro
truncation already established in this package and a direct integral
comparison for the finite Dirichlet sum.  The bounded-height alternative of
the source lemma is deliberately kept separate because it uses the sharper
logarithmic estimate (7.2).
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem sum_Icc_two_eq_sum_Ico_succ (f : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 2 M, f n) =
      ∑ i ∈ Finset.Ico 1 M, f (i + 1) := by
  symm
  apply Finset.sum_bij (fun i _hi => i + 1)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    rfl

theorem ford_rpow_partial_sum_le_integral
    {sigma : ℝ} (hsigmaPos : 0 < sigma) {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-sigma)) ≤
      1 + ∫ x in (1 : ℝ)..(M : ℝ), x ^ (-sigma) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-sigma))
      (Set.Icc (1 : ℝ) (M : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -sigma ≤ 0 by linarith)).mono
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hanti' : AntitoneOn (fun x : ℝ => x ^ (-sigma))
      (Set.Icc ((1 : ℕ) : ℝ) (M : ℝ)) := by
    simpa only [Nat.cast_one] using hanti
  have htail := hanti'.sum_le_integral_Ico hM
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hM,
    Finset.sum_insert (by simp)]
  norm_num
  have hshift :
      (∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-sigma)) =
        ∑ i ∈ Finset.Ico 1 M, ((i + 1 : ℕ) : ℝ) ^ (-sigma) :=
    sum_Icc_two_eq_sum_Ico_succ
      (fun n => (n : ℝ) ^ (-sigma)) M
  rw [hshift]
  simpa only [Nat.cast_add, Nat.cast_one] using htail

theorem ford_rpow_partial_sum_le_seventeen
    {sigma t : ℝ} (hsigmaPos : 0 < sigma)
    (hsigmaUpper : sigma ≤ 15 / 16) (ht : 3 ≤ t) :
    (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℝ) ^ (-sigma)) ≤
      17 * t ^ (1 - sigma) := by
  have htPos : 0 < t := by linarith
  have htOne : 1 ≤ t := by linarith
  have hM : 1 ≤ fordFiniteEndpoint t :=
    fordFiniteEndpoint_pos (by linarith)
  have hMle : (fordFiniteEndpoint t : ℝ) ≤ t :=
    fordFiniteEndpoint_le (by linarith)
  have haPos : 0 < 1 - sigma := by linarith
  have haNonneg : 0 ≤ 1 - sigma := haPos.le
  have hIntegral :
      (∫ x in (1 : ℝ)..(fordFiniteEndpoint t : ℝ), x ^ (-sigma)) =
        (((fordFiniteEndpoint t : ℝ) ^ (1 - sigma)) - 1) /
          (1 - sigma) := by
    rw [integral_rpow]
    · norm_num
      ring_nf
    · left
      linarith
  have hsum := ford_rpow_partial_sum_le_integral hsigmaPos hM
  rw [hIntegral] at hsum
  have hdenLower : (1 / 16 : ℝ) ≤ 1 - sigma := by linarith
  have hpowMNonneg :
      0 ≤ (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) :=
    Real.rpow_nonneg (by positivity) _
  have hpowMOne :
      1 ≤ (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) := by
    exact Real.one_le_rpow (by exact_mod_cast hM) haNonneg
  have hquot :
      (((fordFiniteEndpoint t : ℝ) ^ (1 - sigma)) - 1) /
          (1 - sigma) ≤
        16 * (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) := by
    rw [div_le_iff₀ haPos]
    nlinarith
  have hpowMt :
      (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) ≤ t ^ (1 - sigma) :=
    Real.rpow_le_rpow (by positivity) hMle haNonneg
  have hpowtOne : 1 ≤ t ^ (1 - sigma) :=
    Real.one_le_rpow htOne haNonneg
  calc
    (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℝ) ^ (-sigma)) ≤
        1 + (((fordFiniteEndpoint t : ℝ) ^ (1 - sigma)) - 1) /
          (1 - sigma) := hsum
    _ ≤ 1 + 16 * (fordFiniteEndpoint t : ℝ) ^ (1 - sigma) := by
      gcongr
    _ ≤ 1 + 16 * t ^ (1 - sigma) := by
      gcongr
    _ ≤ 17 * t ^ (1 - sigma) := by nlinarith

theorem norm_fordPartialSum_le_seventeen
    {sigma t : ℝ} (hsigmaPos : 0 < sigma)
    (hsigmaUpper : sigma ≤ 15 / 16) (ht : 3 ≤ t) :
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      17 * t ^ (1 - sigma) := by
  calc
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
        ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          ‖(n : ℂ) ^ (-fordComplexHeight sigma t)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℝ) ^ (-sigma) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnPos : 0 < (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp [fordComplexHeight]
    _ ≤ 17 * t ^ (1 - sigma) :=
      ford_rpow_partial_sum_le_seventeen hsigmaPos hsigmaUpper ht

theorem one_sub_sigma_le_four_mul_three_halves
    {sigma : ℝ} (hsigmaUpper : sigma ≤ 15 / 16) :
    1 - sigma ≤ 4 * (1 - sigma) ^ (3 / 2 : ℝ) := by
  let eta : ℝ := 1 - sigma
  have heta : 0 ≤ eta := by dsimp [eta]; linarith
  have hetaLower : (1 / 16 : ℝ) ≤ eta := by dsimp [eta]; linarith
  have hsqrt : 1 / 4 ≤ eta ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hsq : (1 / 4 : ℝ) = Real.sqrt (1 / 16 : ℝ) := by
      rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]
    rw [hsq]
    exact Real.sqrt_le_sqrt hetaLower
  rw [eta_three_halves_eq_mul_sqrt heta]
  dsimp [eta] at heta ⊢
  nlinarith

theorem norm_riemannZeta_le_ford_lowSigma
    {sigma t : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 15 / 16) (ht : 3 ≤ t) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  have htPos : 0 < t := by linarith
  have htOne : 1 ≤ t := by linarith
  have hsigmaPos : 0 < sigma := by linarith
  have hsigmaOne : sigma ≤ 1 := by linarith
  have hsum := norm_fordPartialSum_le_seventeen hsigmaPos hsigmaUpper ht
  have hrem := norm_riemannZeta_sub_fordPartialSum_le_thirty
    (by linarith : 0 ≤ sigma) hsigmaOne ht
  have htri :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
            (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
          ‖riemannZeta (fordComplexHeight sigma t) -
            (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := by
    have := norm_add_le
      (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t))
      (riemannZeta (fordComplexHeight sigma t) -
        (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℂ) ^ (-fordComplexHeight sigma t)))
    simpa [add_sub_cancel_right] using this
  have hexp :
      t ^ (1 - sigma) ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le htOne
      (one_sub_sigma_le_four_mul_three_halves hsigmaUpper)
  have hneg : t ^ (-sigma) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos htOne (by linarith)
  have htargetOne :
      1 ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
    apply Real.one_le_rpow htOne
    positivity
  have hlogOne : 1 ≤ Real.log t := by
    apply (Real.le_log_iff_exp_le htPos).2
    exact Real.exp_one_lt_three.le.trans ht
  have hlogPowerOne : 1 ≤ Real.log t ^ (2 / 3 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hcore :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        47 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
    calc
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
          ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
              (n : ℂ) ^ (-fordComplexHeight sigma t)‖ +
            ‖riemannZeta (fordComplexHeight sigma t) -
              (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
                (n : ℂ) ^ (-fordComplexHeight sigma t))‖ := htri
      _ ≤ 17 * t ^ (1 - sigma) + 30 * t ^ (-sigma) := by gcongr
      _ ≤ 17 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) + 30 := by
        gcongr
        nlinarith
      _ ≤ 47 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) := by
        nlinarith
  have hmajor :
      47 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        58.1 * t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ) := by
    have hpowNonneg :
        0 ≤ t ^ (4 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
      Real.rpow_nonneg htPos.le _
    nlinarith
  simpa [fordComplexHeight, mul_comm] using hcore.trans hmajor

#print axioms ford_rpow_partial_sum_le_integral
#print axioms ford_rpow_partial_sum_le_seventeen
#print axioms norm_fordPartialSum_le_seventeen
#print axioms one_sub_sigma_le_four_mul_three_halves
#print axioms norm_riemannZeta_le_ford_lowSigma

end

end GafniTao
