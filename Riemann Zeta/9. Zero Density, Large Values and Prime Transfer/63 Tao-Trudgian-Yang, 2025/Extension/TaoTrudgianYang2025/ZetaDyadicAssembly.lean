import TaoTrudgianYang2025.ZetaWeightedPair
import TaoTrudgianYang2025.ZetaSharpTruncation
import TaoTrudgianYang2025.TruncatedDyadicPartition

/-! Assembly of the genuine sharp-cutoff Dirichlet sum from dyadic blocks. -/

noncomputable section
open Complex
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem sum_Icc_one_eq_truncatedDyadic (s : ℂ) (hs : s ≠ 0) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℂ)^(-s)) =
      ∑ j ∈ Finset.range (Nat.clog 2 (K+1)),
        ∑ i ∈ Finset.range (truncatedDyadicLength (K+1) j),
          ((2^j+i : ℕ) : ℂ)^(-s) := by
  have hz : (0 : ℂ)^(-s) = 0 := Complex.zero_cpow (neg_ne_zero.mpr hs)
  calc
    _ = ∑ n ∈ Finset.range (K+1), (n : ℂ)^(-s) := by
      apply Finset.sum_subset
      · intro n hn
        have hn' := Finset.mem_Icc.mp hn
        simp only [Finset.mem_range]
        omega
      · intro n hn hnnot
        have hn' := Finset.mem_range.mp hn
        have hn0 : n = 0 := by
          simp only [Finset.mem_Icc,not_and_or,not_le] at hnnot
          omega
        subst n
        simpa using hz
    _ = _ := sum_range_eq_truncatedDyadic (fun n => (n : ℂ)^(-s)) (by simpa using hz) _

theorem ExponentPair.zeta_sharp_sum_bound {k l ε : ℝ}
    (h : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∑ n ∈ Finset.Icc 1 ⌊sharpZetaCutoff t⌋₊,
        (n : ℂ)^(-(((l-k : ℝ) : ℂ)+(t : ℂ)*I))‖ ≤
      C*Nat.clog 2 (⌊sharpZetaCutoff t⌋₊+1)*t^(k+ε) := by
  obtain ⟨C,hC,hbound⟩ := h.zeta_weighted_dyadic_bound hε
  refine ⟨C,hC,?_⟩
  intro t ht
  have hs : ((l-k : ℝ) : ℂ)+(t : ℂ)*I ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith
  rw [sum_Icc_one_eq_truncatedDyadic _ hs]
  have hcut : 0 ≤ sharpZetaCutoff t := by
    linarith [four_mul_lt_sharpZetaCutoff t]
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.clog 2 (⌊sharpZetaCutoff t⌋₊+1)),
        ‖∑ i ∈ Finset.range (truncatedDyadicLength (⌊sharpZetaCutoff t⌋₊+1) j),
          ((2^j+i : ℕ) : ℂ)^(-(((l-k : ℝ) : ℂ)+(t : ℂ)*I))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (Nat.clog 2 (⌊sharpZetaCutoff t⌋₊+1)),
        C*t^(k+ε) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := truncatedDyadic_start_lt (Finset.mem_range.mp hj)
      have haK : (2^j : ℕ) ≤ ⌊sharpZetaCutoff t⌋₊ := by omega
      apply hbound t (2^j) _ ht (by positivity)
      · exact (show ((2^j : ℕ) : ℝ) ≤ ⌊sharpZetaCutoff t⌋₊ by
          exact_mod_cast haK).trans
          ((Nat.floor_le hcut).trans (sharpZetaCutoff_le_six_mul (by linarith)))
      · exact truncatedDyadicLength_le_width _ _
    _ = C*Nat.clog 2 (⌊sharpZetaCutoff t⌋₊+1)*t^(k+ε) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      ring

end TaoTrudgianYang2025

