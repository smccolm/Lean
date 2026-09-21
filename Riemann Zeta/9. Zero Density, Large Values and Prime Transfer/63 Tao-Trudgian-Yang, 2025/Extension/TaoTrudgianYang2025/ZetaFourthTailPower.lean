import TaoTrudgianYang2025.ZetaFourthTruncation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative decay of the actual divisor tail

The integral comparison retains the precise power of the cutoff.
Its application below uses the ordinary divisor coefficients, not an
assumed tail estimate for the contour source.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace TaoTrudgianYang2025

theorem tsum_nat_rpow_tail_le {p : ℝ} (hp : p < -1) {N : ℕ} (hN : 0 < N) :
    (∑' j : ℕ, ((j+N+1:ℕ):ℝ)^p) ≤ (N:ℝ)^(p+1)/(-p-1) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hi := integrableOn_Ioi_rpow_of_lt hp hN0
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro k
  have hanti : AntitoneOn (fun x : ℝ => x^p) (Icc (N:ℝ) ((N:ℝ)+k)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : p ≤ 0)).mono
      (fun _ hx => hN0.trans_le hx.1)
  calc
    (∑ j ∈ Finset.range k, ((j+N+1:ℕ):ℝ)^p)
        ≤ ∫ x : ℝ in (N:ℝ)..(N:ℝ)+k, x^p := by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using
        hanti.sum_le_integral
    _ ≤ ∫ x : ℝ in Ioi (N:ℝ), x^p := by
      rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg k))]
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (hN0.le.trans hx.le) _
      · exact Eventually.of_forall (fun _ hx => hx.1)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hp hN0,
        show -p-1 = -(p+1) by ring,div_neg,neg_div]

theorem fourth_divisorWeight_le_rpow (b : ℝ) (n : ℕ) :
    (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+b)) ≤ (n:ℝ)^(1/2-b) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ (n:ℝ)*(n:ℝ)^(-(1/2+b)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
        (Real.rpow_nonneg hn0.le _)
    _ = (n:ℝ)^(1+(-(1/2+b))) := by rw [Real.rpow_add hn0,Real.rpow_one]
    _ = _ := by congr 1; ring

theorem tsum_fourth_divisorWeight_tail_le {b : ℝ} (hb : 3/2 < b)
    {N : ℕ} (hN : 0 < N) :
    (∑' n : {n : ℕ // n ∉ Finset.range (N+1)},
      ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))) ≤
      (N:ℝ)^(3/2-b)/(b-3/2) := by
  have hp : 1/2-b < (-1:ℝ) := by linarith
  have hs := (Real.summable_nat_rpow.mpr hp).subtype
    (fun n => n ∉ Finset.range (N+1))
  calc
    _ ≤ ∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, ((n:ℕ):ℝ)^(1/2-b) :=
      Summable.tsum_le_tsum (fun n => fourth_divisorWeight_le_rpow b n)
        ((summable_fourth_divisorWeight hb).subtype _) hs
    _ = ∑' j : ℕ, ((j+N+1:ℕ):ℝ)^(1/2-b) := by
      simpa only [coe_notMemRangeEquiv_symm,Nat.add_assoc] using
        ((notMemRangeEquiv (N+1)).symm.tsum_eq
          (fun n : {n : ℕ // n ∉ Finset.range (N+1)} =>
            ((n:ℕ):ℝ)^(1/2-b))).symm
    _ ≤ _ := by
      have h := tsum_nat_rpow_tail_le hp hN
      have hnum : (1/2-b)+1 = 3/2-b := by ring
      have hden : -(1/2-b)-1 = b-3/2 := by ring
      simpa only [hnum,hden] using h

theorem exists_norm_zetaFourthTail_cutoff_le {b : ℝ} (hb : 3/2 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → 4*b ≤ t →
      ∀ N : ℕ, 0 < N →
      ‖zetaFourthTail t b (Finset.range (N+1))‖ ≤
        K*t^b*(N:ℝ)^(3/2-b) := by
  obtain ⟨A,hA,hbound⟩ := exists_norm_zetaFourthTail_le hb
  refine ⟨A/(b-3/2),div_pos hA (by linarith),?_⟩
  intro t ht hbt N hN
  calc
    _ ≤ A*t^b*(∑' n : {n : ℕ // n ∉ Finset.range (N+1)},
        ((n:ℕ).divisors.card:ℝ)*((n:ℕ):ℝ)^(-(1/2+b))) :=
      hbound t ht hbt _
    _ ≤ A*t^b*((N:ℝ)^(3/2-b)/(b-3/2)) :=
      mul_le_mul_of_nonneg_left (tsum_fourth_divisorWeight_tail_le hb hN)
        (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
