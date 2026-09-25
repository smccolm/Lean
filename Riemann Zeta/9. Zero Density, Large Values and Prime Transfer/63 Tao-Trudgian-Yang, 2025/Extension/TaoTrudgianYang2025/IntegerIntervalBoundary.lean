import TaoTrudgianYang2025.RobertSargosCorrelationSum

/-! Quantitative error for moving both endpoints of an integer interval.
The common finite mask is arbitrary, so extra source support is retained. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem integer_interval_contraction_subset (S : Finset ℤ) (a b r : ℤ)
    (hr : 0 ≤ r) :
    S ∩ Finset.Icc (a+r) (b-r) ⊆ S ∩ Finset.Icc a b := by
  intro m hm
  simp only [Finset.mem_inter,Finset.mem_Icc] at hm ⊢
  exact ⟨hm.1,by omega,by omega⟩

theorem integer_interval_contraction_boundary (S : Finset ℤ) (a b r : ℤ) :
    (S ∩ Finset.Icc a b) \ (S ∩ Finset.Icc (a+r) (b-r)) ⊆
      Finset.Ico a (a+r) ∪ Finset.Ioc (b-r) b := by
  intro m hm
  simp only [Finset.mem_sdiff,Finset.mem_inter,Finset.mem_Icc] at hm
  simp only [Finset.mem_union,Finset.mem_Ico,Finset.mem_Ioc]
  have hn : ¬ (a+r ≤ m ∧ m ≤ b-r) := fun ht => hm.2 ⟨hm.1.1,ht⟩
  omega

theorem integer_interval_contraction_card (S : Finset ℤ) (a b r : ℤ)
    (hr : 0 ≤ r) :
    (((S ∩ Finset.Icc a b) \ (S ∩ Finset.Icc (a+r) (b-r))).card : ℝ) ≤
      2*(r:ℝ) := by
  have hc := (Finset.card_le_card (integer_interval_contraction_boundary S a b r)).trans
    (Finset.card_union_le _ _)
  simp only [Int.card_Ico,Int.card_Ioc] at hc
  have ha : a+r-a = r := by omega
  have hb : b-(b-r) = r := by omega
  rw [ha,hb] at hc
  have hcast : (r.toNat : ℝ) = (r:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  have hc' : (((S ∩ Finset.Icc a b) \
      (S ∩ Finset.Icc (a+r) (b-r))).card : ℝ) ≤
      (r.toNat:ℝ)+(r.toNat:ℝ) := by exact_mod_cast hc
  rw [hcast] at hc'
  linarith

theorem norm_integer_interval_contraction (w : ℤ → ℂ) (S : Finset ℤ)
    (a b r : ℤ) (hr : 0 ≤ r) (hw : ∀ m ∈ S, ‖w m‖ ≤ 1) :
    ‖(∑ m ∈ S ∩ Finset.Icc a b, w m) -
      ∑ m ∈ S ∩ Finset.Icc (a+r) (b-r), w m‖ ≤ 2*(r:ℝ) := by
  rw [← Finset.sum_sdiff_eq_sub (integer_interval_contraction_subset S a b r hr)]
  calc
    _ ≤ ∑ m ∈ (S ∩ Finset.Icc a b) \ (S ∩ Finset.Icc (a+r) (b-r)),
        ‖w m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ (S ∩ Finset.Icc a b) \ (S ∩ Finset.Icc (a+r) (b-r)),
        (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hw m (Finset.mem_inter.mp (Finset.mem_sdiff.mp hm).1).1
    _ ≤ 2*(r:ℝ) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
        integer_interval_contraction_card S a b r hr

theorem norm_integer_interval_endpoint_shift (w : ℤ → ℂ) (S : Finset ℤ)
    (a b r : ℤ) (hw : ∀ m ∈ S, ‖w m‖ ≤ 1) :
    ‖(∑ m ∈ S ∩ Finset.Icc (a+r) (b-r), w m) -
      ∑ m ∈ S ∩ Finset.Icc a b, w m‖ ≤ 2*|(r:ℝ)| := by
  by_cases hr : 0 ≤ r
  · rw [norm_sub_rev,abs_of_nonneg (by exact_mod_cast hr)]
    exact norm_integer_interval_contraction w S a b r hr hw
  · have hn : 0 ≤ -r := by omega
    have hs := norm_integer_interval_contraction w S (a+r) (b-r) (-r) hn hw
    have ha : a+r+-r = a := by omega
    have hb : b-r- -r = b := by omega
    rw [ha,hb] at hs
    simpa only [Int.cast_neg,abs_of_neg (show (r:ℝ) < 0 by exact_mod_cast
      (show r < 0 by omega))] using hs

end TaoTrudgianYang2025
