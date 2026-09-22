import TaoTrudgianYang2025.ZetaFourthTailPower
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Quantitative two-sided integer inverse-square tails

The frequency cutoff is a positive natural number. Both signs are
counted, and the actual omitted series is bounded, not just declared summable.
-/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem tsum_nat_inverse_square_tail_le {R : ℕ} (hR : 0 < R) :
    (∑' n : ℕ, if R < n then 1/(n : ℝ)^2 else 0) ≤ 1/(R : ℝ) := by
  let f : ℕ → ℝ := fun n => if R < n then 1/(n : ℝ)^2 else 0
  have hs : Summable f := by
    have hi := (Real.summable_one_div_nat_pow.mpr
      (by norm_num : 1 < (2 : ℕ))).indicator {n | R < n}
    apply hi.congr
    intro n
    by_cases hn : R < n <;> simp [f,hn]
  have hsum : ∑ n ∈ Finset.range (R+1), f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp only [f,if_neg (by omega : ¬ R < n)]
  have he := hs.sum_add_tsum_nat_add (R+1)
  rw [hsum,zero_add] at he
  have hshift : (fun j : ℕ => f (j+(R+1))) =
      fun j : ℕ => 1/((j+R+1 : ℕ) : ℝ)^2 := by
    funext j
    simp only [f,if_pos (by omega : R < j+(R+1)),Nat.add_assoc]
  rw [hshift] at he
  change (∑' n, f n) ≤ _
  rw [← he]
  have ht := tsum_nat_rpow_tail_le (p := -2) (by norm_num) hR
  have hr (n : ℕ) : (n : ℝ)^(-2 : ℝ) = 1/(n : ℝ)^2 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_two,one_div]
  simpa only [hr,show (-2 : ℝ)+1 = -1 by norm_num,
    show -(-2 : ℝ)-1 = 1 by norm_num,div_one,Real.rpow_neg_one,one_div] using ht

theorem tsum_int_inverse_square_tail_le {R : ℕ} (hR : 0 < R) :
    (∑' q : ℤ, if R < q.natAbs then 1/(q : ℝ)^2 else 0) ≤ 2/(R : ℝ) := by
  let g : ℤ → ℝ := fun q => if R < q.natAbs then 1/(q : ℝ)^2 else 0
  let f : ℕ → ℝ := fun n => if R < n then 1/(n : ℝ)^2 else 0
  have hg : Summable g := by
    have hi := (Real.summable_one_div_int_pow.mpr
      (by norm_num : 1 < (2 : ℕ))).indicator {q | R < q.natAbs}
    apply hi.congr
    intro q
    by_cases hq : R < q.natAbs <;> simp [g,hq]
  have hf : Summable f := by
    have hi := (Real.summable_one_div_nat_pow.mpr
      (by norm_num : 1 < (2 : ℕ))).indicator {n | R < n}
    apply hi.congr
    intro n
    by_cases hn : R < n <;> simp [f,hn]
  have hp : (fun n : ℕ => g n) = f := by
    funext n
    simp only [g,f,Int.natAbs_natCast,Int.cast_natCast]
  have hm : (fun n : ℕ => g (-(n+1))) = fun n => f (n+1) := by
    funext n
    simp only [g,f,Int.natAbs_neg,
      Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,Nat.cast_add,Nat.cast_one,neg_sq]
    rfl
  have hpSum := hg.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ)) from
    Nat.cast_injective)
  have hnSum := hg.comp_injective
    (show Function.Injective (fun n : ℕ => -((n : ℤ)+1)) from by
      intro a b h
      simp only [neg_inj,add_left_inj] at h
      exact_mod_cast h)
  have hz : f 0 = 0 := by simp [f]
  have hshift : (∑' n : ℕ, f (n+1)) = ∑' n : ℕ, f n := by
    simpa only [hz,zero_add] using hf.tsum_eq_zero_add.symm
  change (∑' q, g q) ≤ _
  rw [tsum_of_nat_of_neg_add_one hpSum hnSum,hp,hm,hshift]
  have hb := tsum_nat_inverse_square_tail_le hR
  change (∑' n, f n) ≤ 1/(R : ℝ) at hb
  calc
    _ ≤ 1/(R : ℝ)+1/(R : ℝ) := add_le_add hb hb
    _ = _ := by ring

theorem norm_integer_far_tail_le_of_inverse_square
    {f : ℤ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hf : Summable (fun q => ‖f q‖))
    (hb : ∀ q : ℤ, q ≠ 0 → ‖f q‖ ≤ K/(q : ℝ)^2)
    {R : ℕ} (hR : 0 < R) :
    ‖∑' q : ℤ, if R < q.natAbs then f q else 0‖ ≤ 2*K/(R : ℝ) := by
  have hs : Summable (fun q : ℤ => if R < q.natAbs then ‖f q‖ else 0) := by
    apply (hf.indicator {q | R < q.natAbs}).congr
    intro q
    by_cases hq : R < q.natAbs <;> simp [hq]
  have hg : Summable (fun q : ℤ => if R < q.natAbs then 1/(q : ℝ)^2 else 0) := by
    have hi := (Real.summable_one_div_int_pow.mpr
      (by norm_num : 1 < (2 : ℕ))).indicator {q | R < q.natAbs}
    apply hi.congr
    intro q
    by_cases hq : R < q.natAbs <;> simp [hq]
  have hnorm : (fun q : ℤ => ‖if R < q.natAbs then f q else 0‖) =
      fun q => if R < q.natAbs then ‖f q‖ else 0 := by
    funext q
    by_cases hq : R < q.natAbs <;> simp [hq]
  calc
    _ ≤ ∑' q : ℤ, if R < q.natAbs then ‖f q‖ else 0 := by
      simpa only [hnorm] using norm_tsum_le_tsum_norm (hs.congr (fun q => (congrFun hnorm q).symm))
    _ ≤ ∑' q : ℤ, K*(if R < q.natAbs then 1/(q : ℝ)^2 else 0) := by
      apply Summable.tsum_le_tsum _ hs (hg.mul_left K)
      intro q
      by_cases hq : R < q.natAbs
      · rw [if_pos hq,if_pos hq]
        have hq₀ : q ≠ 0 := by intro hz; subst q; simp at hq
        simpa only [mul_one_div] using hb q hq₀
      · simp only [if_neg hq,mul_zero,le_refl]
    _ = K*(∑' q : ℤ, if R < q.natAbs then 1/(q : ℝ)^2 else 0) := tsum_mul_left
    _ ≤ K*(2/(R : ℝ)) := mul_le_mul_of_nonneg_left (tsum_int_inverse_square_tail_le hR) hK
    _ = _ := by ring

theorem tsum_int_eq_sum_Icc_add_far {f : ℤ → ℂ}
    (hf : Summable f) (R : ℕ) :
    (∑' q : ℤ, f q) =
      (∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), f q) +
        ∑' q : ℤ, if R < q.natAbs then f q else 0 := by
  have hc : Summable (fun q : ℤ => if q.natAbs ≤ R then f q else 0) := by
    apply (hf.indicator {q | q.natAbs ≤ R}).congr
    intro q
    by_cases hq : q.natAbs ≤ R <;> simp [hq]
  have ht : Summable (fun q : ℤ => if R < q.natAbs then f q else 0) := by
    apply (hf.indicator {q | R < q.natAbs}).congr
    intro q
    by_cases hq : R < q.natAbs <;> simp [hq]
  have he : (∑' q : ℤ, f q) =
      (∑' q : ℤ, if q.natAbs ≤ R then f q else 0) +
        ∑' q : ℤ, if R < q.natAbs then f q else 0 := by
    rw [← hc.tsum_add ht]
    apply tsum_congr
    intro q
    by_cases hq : q.natAbs ≤ R
    · simp only [if_pos hq,if_neg (Nat.not_lt_of_ge hq),add_zero]
    · simp only [if_neg hq,if_pos (Nat.lt_of_not_ge hq),zero_add]
  rw [he]
  congr 1
  rw [tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) (R : ℤ))]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [if_pos]
    have hh := Finset.mem_Icc.mp hq
    omega
  · intro q hq
    rw [if_neg]
    intro h
    apply hq
    apply Finset.mem_Icc.mpr
    omega

end TaoTrudgianYang2025
