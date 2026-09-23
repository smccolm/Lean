import TaoTrudgianYang2025.SargosSourceSixthMoment
import Mathlib.Algebra.Order.Chebyshev

/-! Literal initial integer intervals and their dyadic sixth-power decomposition. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosInitialQuarticSum (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (0:ℤ) N,
    z n*fordAdditiveCharacter ((n:ℝ)^2*α+(n:ℝ)^4*γ)

theorem sargos_integer_Ioc_sum_split {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Finset.Ioc a c, f n) =
      (∑ n ∈ Finset.Ioc a b, f n)+(∑ n ∈ Finset.Ioc b c, f n) := by
  classical
  have hu : Finset.Ioc a c = Finset.Ioc a b ∪ Finset.Ioc b c := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  rw [hu,Finset.sum_union hd]

theorem sargosInitialQuarticSum_double (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosInitialQuarticSum (2*N) z α γ =
      sargosInitialQuarticSum N z α γ+sargosQuarticSum N z α γ := by
  unfold sargosInitialQuarticSum sargosQuarticSum sargosPlanarSum sargosSourceInterval
  push_cast
  exact sargos_integer_Ioc_sum_split _ (Int.natCast_nonneg N) (by omega)

theorem sargosInitialQuarticSum_dyadic (K : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosInitialQuarticSum (2^(K+1)) z α γ =
      sargosInitialQuarticSum 2 z α γ+
        ∑ i ∈ Finset.range K, sargosQuarticSum (2^(i+1)) z α γ := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show 2^(K+1+1) = 2*(2^(K+1)) by rw [pow_succ]; omega,
        sargosInitialQuarticSum_double,ih,Finset.sum_range_succ]
      abel

theorem sargos_complex_sum_sixth {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖^6 ≤ (S.card:ℝ)^5*∑ i ∈ S, ‖f i‖^6 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 6).trans
    (pow_sum_le_card_mul_sum_pow (fun _ _ => norm_nonneg _) 5)

theorem sargosInitialQuarticSum_dyadic_sixth (K : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosInitialQuarticSum (2^(K+1)) z α γ‖^6 ≤
      32*(‖sargosInitialQuarticSum 2 z α γ‖^6+
        (K:ℝ)^5*∑ i ∈ Finset.range K, ‖sargosQuarticSum (2^(i+1)) z α γ‖^6) := by
  rw [sargosInitialQuarticSum_dyadic]
  have ht := norm_add_le (sargosInitialQuarticSum 2 z α γ)
    (∑ i ∈ Finset.range K, sargosQuarticSum (2^(i+1)) z α γ)
  have hp := add_pow_le (norm_nonneg (sargosInitialQuarticSum 2 z α γ))
    (norm_nonneg (∑ i ∈ Finset.range K, sargosQuarticSum (2^(i+1)) z α γ)) 6
  norm_num at hp
  have hs := sargos_complex_sum_sixth (Finset.range K)
    (fun i => sargosQuarticSum (2^(i+1)) z α γ)
  simp only [Finset.card_range] at hs
  exact ((pow_le_pow_left₀ (norm_nonneg _) ht 6).trans hp).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hs) (by norm_num))

end TaoTrudgianYang2025
