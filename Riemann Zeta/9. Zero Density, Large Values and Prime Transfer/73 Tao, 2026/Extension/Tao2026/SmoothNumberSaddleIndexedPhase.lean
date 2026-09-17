import Tao2026.SmoothNumberSaddleIndexedShell

/-!
# Uniform phase loss on indexed outer shells

This module proves the phase calculation once for the full iterated-root
family.  If the `k`th scale retains at least four fifths of its ideal
`2^(-k)` logarithmic size, its CEP alphabet begins at two thirds of that
ideal size.  On the corresponding doubling shell every retained phase lies
in `[pi/2, 3*pi/2]`, giving the accumulated cosine-loss lower bound.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

theorem indexedShell_lower_coefficient_mul_support_coefficient
    {k : ℕ} (hk : 2 ≤ k) :
    (3 * (2 : ℝ) ^ (k - 2)) *
        (1 / (3 * (2 : ℝ) ^ (k - 1))) = 1 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsub : 2 + m - 1 = m + 1 := by omega
  rw [show 2 + m - 2 = m by omega, hsub]
  rw [pow_succ]
  have hpow : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp [hpow]

theorem indexedShell_upper_coefficient_mul_support_coefficient
    {k : ℕ} (hk : 2 ≤ k) :
    (3 * (2 : ℝ) ^ (k - 1)) * (1 / 2 : ℝ) ^ k = 3 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsub : 2 + m - 1 = m + 1 := by omega
  rw [hsub, pow_succ, show (2 + m : ℕ) = m + 2 by omega,
    pow_succ, pow_succ]
  rw [div_pow]
  field_simp
  norm_num

theorem indexedPrimeLogLower_le_of_scale
    {B k y N : ℕ} {u : ℝ} (hk : 2 ≤ k) (hB : 4 ≤ B) (hN : 2 ≤ N)
    (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt N)
    (hscale : (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) ≤
      Real.log (N : ℝ))
    {p : TaoBoundedPrime N}
    (hp : p ∈ cepDyadicPrimeAlphabet N (cepDyadicBlockCount N u)) :
    (1 / (3 * (2 : ℝ) ^ (k - 1))) * Real.log (y : ℝ) ≤
      Real.log (p : ℝ) := by
  have hcut := one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
    hB hN (by linarith) hBu huN
  have hlogUPos : 0 < Real.log u := by linarith
  have hcoeff : (5 / 6 : ℝ) ≤ 1 - 2 / Real.log u := by
    have hdiv : 2 / Real.log u ≤ (1 / 6 : ℝ) := by
      apply (div_le_iff₀ hlogUPos).mpr
      nlinarith
    linarith
  have hlogNNonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogyNonneg : 0 ≤ Real.log (y : ℝ) := by
    by_cases hy : y = 0
    · subst y
      norm_num
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hy))
  have hcoefficient :
      (1 / (3 * (2 : ℝ) ^ (k - 1))) ≤
        (5 / 6 : ℝ) * ((4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hsub : 2 + m - 1 = m + 1 := by omega
    rw [hsub, pow_succ, show (2 + m : ℕ) = m + 2 by omega,
      pow_succ, pow_succ]
    rw [div_pow]
    field_simp
    norm_num
  have hcutPos : (0 : ℝ) < cepDyadicCofactorCutoff N u := by
    have hw := nat_le_cepDyadicCofactorCutoff_of_criticalRange
      (show 1 ≤ N by omega) (by linarith) hBu huN
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < B) hw)
  have hpCut : (cepDyadicCofactorCutoff N u : ℝ) < (p : ℝ) := by
    exact_mod_cast cepDyadicCofactorCutoff_lt_of_mem hp
  calc
    (1 / (3 * (2 : ℝ) ^ (k - 1))) * Real.log (y : ℝ) ≤
        ((5 / 6 : ℝ) * ((4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k)) *
          Real.log (y : ℝ) := mul_le_mul_of_nonneg_right hcoefficient hlogyNonneg
    _ ≤ (5 / 6 : ℝ) * Real.log (N : ℝ) := by
      nlinarith
    _ ≤ (1 - 2 / Real.log u) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hlogNNonneg
    _ ≤ Real.log (cepDyadicCofactorCutoff N u : ℕ) := hcut
    _ ≤ Real.log (p : ℝ) := Real.log_le_log hcutPos hpCut.le

theorem one_le_cosineLossTerm_of_indexedPrimeAlphabet
    {B k y N : ℕ} {u t : ℝ} (hk : 2 ≤ k) (hB : 4 ≤ B) (hN : 2 ≤ N)
    (hy : 2 ≤ y) (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt N)
    (hscaleLower : (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k *
      Real.log (y : ℝ) ≤ Real.log (N : ℝ))
    (hscaleUpper : Real.log (N : ℝ) ≤
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ))
    (htLower : smoothSaddleIndexedOuterUpperHeight (k - 1) y ≤ t)
    (htUpper : t ≤ smoothSaddleIndexedOuterUpperHeight k y)
    {p : TaoBoundedPrime N}
    (hp : p ∈ cepDyadicPrimeAlphabet N (cepDyadicBlockCount N u)) :
    1 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
  have hpData := Nat.mem_primesLE.mp p.2
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogpLower := indexedPrimeLogLower_le_of_scale
    hk hB hN hlogU hBu huN hscaleLower hp
  have hlogpUpper : Real.log (p : ℝ) ≤
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) :=
    (Real.log_le_log hpPos (by exact_mod_cast hpData.1)).trans hscaleUpper
  have hheightPos : 0 < smoothSaddleIndexedOuterUpperHeight (k - 1) y := by
    unfold smoothSaddleIndexedOuterUpperHeight
    positivity [Real.pi_pos]
  have htPos : 0 < t := hheightPos.trans_le htLower
  have hphaseLower : Real.pi / 2 ≤ t * Real.log (p : ℝ) := by
    have hmul := mul_le_mul htLower hlogpLower
      (by positivity) htPos.le
    have hkSub : k - 1 - 1 = k - 2 := by omega
    have hleft : smoothSaddleIndexedOuterUpperHeight (k - 1) y *
        ((1 / (3 * (2 : ℝ) ^ (k - 1))) * Real.log (y : ℝ)) =
          Real.pi / 2 := by
      unfold smoothSaddleIndexedOuterUpperHeight
      rw [hkSub]
      field_simp [hlogy.ne']
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
    calc
      Real.pi / 2 = smoothSaddleIndexedOuterUpperHeight (k - 1) y *
          ((1 / (3 * (2 : ℝ) ^ (k - 1))) * Real.log (y : ℝ)) := hleft.symm
      _ ≤ t * Real.log (p : ℝ) := hmul
  have hphaseUpper : t * Real.log (p : ℝ) ≤ Real.pi + Real.pi / 2 := by
    have hmul := mul_le_mul htUpper hlogpUpper
      (Real.log_nonneg (by exact_mod_cast hpData.2.one_le))
      (by
        unfold smoothSaddleIndexedOuterUpperHeight
        positivity [Real.pi_pos])
    have hcoeff := indexedShell_upper_coefficient_mul_support_coefficient hk
    have hleft : smoothSaddleIndexedOuterUpperHeight k y *
        ((1 / 2 : ℝ) ^ k * Real.log (y : ℝ)) = 3 * Real.pi / 2 := by
      unfold smoothSaddleIndexedOuterUpperHeight
      field_simp [hlogy.ne']
      nlinarith [hcoeff]
    calc
      t * Real.log (p : ℝ) ≤ smoothSaddleIndexedOuterUpperHeight k y *
          ((1 / 2 : ℝ) ^ k * Real.log (y : ℝ)) := hmul
      _ = 3 * Real.pi / 2 := hleft
      _ = Real.pi + Real.pi / 2 := by ring
  linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hphaseLower hphaseUpper]

theorem indexedOuterMultiShell_cosineLoss_lower
    {B k y N : ℕ} {u sigma t : ℝ} (hk : 2 ≤ k) (hB : 4 ≤ B)
    (hN : 2 ≤ N) (hy : 2 ≤ y) (hNy : N ≤ y)
    (hlogU : 12 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huN : u ≤ Real.sqrt N)
    (hscaleLower : (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k *
      Real.log (y : ℝ) ≤ Real.log (N : ℝ))
    (hscaleUpper : Real.log (N : ℝ) ≤
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ))
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigma1 : sigma ≤ 1)
    (htLower : smoothSaddleIndexedOuterUpperHeight (k - 1) y ≤ t)
    (htUpper : t ≤ smoothSaddleIndexedOuterUpperHeight k y) :
    (cepDyadicCofactorCutoff N u : ℝ) ^ (1 - sigma) /
          (16 * Real.log 2 * Real.log u) ≤
      smoothSaddleCosineLoss y sigma t := by
  let P := cepDyadicPrimeAlphabet N (cepDyadicBlockCount N u)
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let f : ℕ → ℝ := fun p =>
    (p : ℝ) ^ (-sigma) * (1 - Real.cos (t * Real.log (p : ℝ)))
  have hweight := cofactor_rpow_div_log_le_sum_rpow_neg_cepDyadicPrimeAlphabet
    hB hN (by linarith) hBu huN hpnt hsigma1
  have hphase (p : TaoBoundedPrime N) (hp : p ∈ P) :
      1 ≤ 1 - Real.cos (t * Real.log ((p : ℕ) : ℝ)) :=
    one_le_cosineLossTerm_of_indexedPrimeAlphabet hk hB hN hy hlogU hBu
      huN hscaleLower hscaleUpper htLower htUpper hp
  have hsubset : P.image (fun p : TaoBoundedPrime N => (p : ℕ)) ⊆ S := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqData := Nat.mem_primesLE.mp q.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqData.2.two_le, hqData.1.trans hNy⟩, hqData.2⟩
  calc
    (cepDyadicCofactorCutoff N u : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ P, ((p : ℕ) : ℝ) ^ (-sigma) := hweight
    _ ≤ ∑ p ∈ P, f (p : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact le_mul_of_one_le_right (by positivity) (hphase p hp)
    _ = ∑ p ∈ P.image (fun p : TaoBoundedPrime N => (p : ℕ)), f p := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      exact Subtype.ext hpq
    _ ≤ ∑ p ∈ S, f p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => mul_nonneg (by positivity)
          (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]))
    _ = smoothSaddleCosineLoss y sigma t := rfl

end

end Tao2026
