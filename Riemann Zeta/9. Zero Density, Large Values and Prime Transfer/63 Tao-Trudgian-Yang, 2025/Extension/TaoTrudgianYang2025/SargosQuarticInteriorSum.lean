import TaoTrudgianYang2025.SargosQuarticInteriorFrequency
import TaoTrudgianYang2025.BetaBufferedInteriorSum

/-! Logarithmic sums of the actual quartic stationary errors over integer interior blocks. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedInteriorRange_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (N α γ Q : ℝ) (L : ℕ),
        0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
        sargosQuarticSlope α γ (N*(l+2*η)) ≤ Q →
        Q+(L : ℝ)+1 ≤ sargosQuarticSlope α γ (N*(r-2*η)) →
        ‖∑ n ∈ Finset.range L,
          (sargosQuarticFourierMode (modelPhaseBufferedCutoff l r η) N α γ (Q+((n+1 : ℕ) : ℝ))-
            sargosQuarticStationaryMainTerm N α γ (Q+((n+1 : ℕ) : ℝ)))‖ ≤
          C*(1+Real.log (L : ℝ)) := by
  obtain ⟨C,hC,hmode⟩ := sargosQuarticBufferedFourierMode_interior_frequency_uniform
  refine ⟨2*C,by linarith,?_⟩
  intro l r η hl hr hη hflat N α γ Q L hN hα hγ hleft hright
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have h := norm_sum_range_le_two_edge_harmonic hC₀ (L := L) (by
    intro n hn
    let lam := min ((n+1 : ℕ) : ℝ) ((L-n : ℕ) : ℝ)
    have hpos : 0 < ((L-n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
    have hlam : 0 < lam := lt_min (by positivity) hpos
    have hlambda₁ : lam ≤ ((n+1 : ℕ) : ℝ) := min_le_left _ _
    have hlambda₂ : lam ≤ ((L-n : ℕ) : ℝ) := min_le_right _ _
    have hsub : ((L-n : ℕ) : ℝ) = (L : ℝ)-(n : ℝ) := Nat.cast_sub (Nat.le_of_lt hn)
    apply hmode l r η hl hr hη hflat N α γ (Q+((n+1 : ℕ) : ℝ)) lam
      hN hα hγ hlam
    · linarith
    · rw [hsub] at hlambda₂
      norm_num only [Nat.cast_add,Nat.cast_one]
      linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity))

theorem sargosQuarticBufferedInteriorBlock_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (N α γ : ℝ) (A B : ℤ),
        0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
        sargosQuarticSlope α γ (N*(l+2*η)) ≤ (A : ℝ) →
        (B : ℝ) ≤ sargosQuarticSlope α γ (N*(r-2*η)) →
        ‖∑ q ∈ Finset.Ioo A B,
          (sargosQuarticFourierMode (modelPhaseBufferedCutoff l r η) N α γ q-
            sargosQuarticStationaryMainTerm N α γ q)‖ ≤
          C*(1+Real.log ((B-A-1).toNat : ℝ)) := by
  obtain ⟨C,hC,hblock⟩ := sargosQuarticBufferedInteriorRange_error
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη hflat N α γ A B hN hα hγ hright hleft
  by_cases hAB : A+1 ≤ B
  · have hlen : ((B-A-1).toNat : ℤ) = B-A-1 := Int.toNat_of_nonneg (by omega)
    have hlen' : ((B-A-1).toNat : ℝ) = (B : ℝ)-(A : ℝ)-1 := by exact_mod_cast hlen
    have h := hblock l r η hl hr hη hflat N α γ A (B-A-1).toNat
      hN hα hγ hright (by rw [hlen']; linarith)
    have he : (∑ q ∈ Finset.Ioo A B,
        (sargosQuarticFourierMode (modelPhaseBufferedCutoff l r η) N α γ q-
          sargosQuarticStationaryMainTerm N α γ q)) =
        ∑ n ∈ Finset.range (B-A-1).toNat,
        (sargosQuarticFourierMode (modelPhaseBufferedCutoff l r η) N α γ ((A : ℝ)+((n+1 : ℕ) : ℝ))-
          sargosQuarticStationaryMainTerm N α γ ((A : ℝ)+((n+1 : ℕ) : ℝ))) := by
      symm
      apply Finset.sum_bij (fun n _ => A+((n+1 : ℕ) : ℤ))
      · intro n hn
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ioo,Nat.cast_add,Nat.cast_one]
        omega
      · intro n hn m hm heq
        simp only [Nat.cast_add,Nat.cast_one] at heq
        omega
      · intro q hq
        simp only [Finset.mem_Ioo] at hq
        have hc : ((q-A-1).toNat : ℤ) = q-A-1 := Int.toNat_of_nonneg (by omega)
        refine ⟨(q-A-1).toNat,?_,?_⟩
        · simp only [Finset.mem_range]
          omega
        · simp only [Nat.cast_add,Nat.cast_one]
          omega
      · intro n hn
        simp only [Int.cast_add,Int.cast_natCast]
    rw [he]
    exact h
  · have hs : Finset.Ioo A B = ∅ := by
      ext q
      simp only [Finset.mem_Ioo,Finset.notMem_empty,iff_false]
      omega
    have hz : (B-A-1).toNat = 0 := by omega
    rw [hs,hz,Finset.sum_empty,norm_zero,Nat.cast_zero,Real.log_zero,add_zero,mul_one]
    exact zero_le_one.trans hC

end TaoTrudgianYang2025

