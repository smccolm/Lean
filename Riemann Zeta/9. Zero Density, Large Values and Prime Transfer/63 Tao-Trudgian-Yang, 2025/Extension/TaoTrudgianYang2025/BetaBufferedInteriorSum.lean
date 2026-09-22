import TaoTrudgianYang2025.BetaBufferedInteriorFrequency
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic sum of the actual interior stationary errors

Each original Fourier mode uses the smaller of its two frequency-edge
distances. Summing both reciprocal distances gives two harmonic sums.
No stationary-image or per-mode error certificate is assumed downstream.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sum_range_two_edge_reciprocals (L : ℕ) :
    (∑ n ∈ Finset.range L, (1/((n+1 : ℕ) : ℝ)+1/((L-n : ℕ) : ℝ))) =
      2*(harmonic L : ℝ) := by
  have hleft : (∑ n ∈ Finset.range L, 1/((n+1 : ℕ) : ℝ)) = (harmonic L : ℝ) := by
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  have hright : (∑ n ∈ Finset.range L, 1/((L-n : ℕ) : ℝ)) =
      ∑ n ∈ Finset.range L, 1/((n+1 : ℕ) : ℝ) := by
    calc
      _ = ∑ n ∈ Finset.range L, 1/((L-1-n+1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have he : L-n = L-1-n+1 := by have hn' := Finset.mem_range.mp hn; omega
        rw [he]
      _ = _ := Finset.sum_range_reflect (fun n => 1/((n+1 : ℕ) : ℝ)) L
  rw [Finset.sum_add_distrib,hright,hleft]
  ring

theorem norm_sum_range_le_two_edge_harmonic
    {f : ℕ → ℂ} {C : ℝ} {L : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n < L, ‖f n‖ ≤ C/min ((n+1 : ℕ) : ℝ) ((L-n : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range L, f n‖ ≤ 2*C*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L,
        C*(1/((n+1 : ℕ) : ℝ)+1/((L-n : ℕ) : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have hpos : 0 < ((L-n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn'
      have hpos' : 0 < ((n+1 : ℕ) : ℝ) := by positivity
      apply (hb n hn').trans
      by_cases h : ((n+1 : ℕ) : ℝ) ≤ ((L-n : ℕ) : ℝ)
      · rw [min_eq_left h]
        have hc := div_nonneg hC hpos.le
        calc
          _ ≤ C/((n+1 : ℕ) : ℝ)+C/((L-n : ℕ) : ℝ) := by linarith
          _ = _ := by ring
      · rw [min_eq_right (le_of_not_ge h)]
        have hc := div_nonneg hC hpos'.le
        calc
          _ ≤ C/((n+1 : ℕ) : ℝ)+C/((L-n : ℕ) : ℝ) := by linarith
          _ = _ := by ring
    _ = _ := by
      rw [← Finset.mul_sum,sum_range_two_edge_reciprocals]
      ring

theorem modelPhaseBufferedInteriorRange_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N Q : ℝ) (L : ℕ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N →
        (T/N)*deriv F (r-2*η) ≤ Q →
        Q+(L : ℝ)+1 ≤ (T/N)*deriv F (l+2*η) →
        ‖∑ n ∈ Finset.range L,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N (Q+((n+1 : ℕ) : ℝ))-
            modelPhaseStationaryMainTerm F T N (Q+((n+1 : ℕ) : ℝ)))‖ ≤
          C*(1+Real.log (L : ℝ)) := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_interior_frequency_uniform hσ
  refine ⟨2*C,by linarith,?_⟩
  intro l r η hl hr hη hflat F δ T N Q L hδ hF hT hN hright hleft
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have h := norm_sum_range_le_two_edge_harmonic hC₀ (L := L) (by
    intro n hn
    let lam := min ((n+1 : ℕ) : ℝ) ((L-n : ℕ) : ℝ)
    have hpos : 0 < ((L-n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
    have hlam : 0 < lam := lt_min (by positivity) hpos
    have hlambda₁ : lam ≤ ((n+1 : ℕ) : ℝ) := min_le_left _ _
    have hlambda₂ : lam ≤ ((L-n : ℕ) : ℝ) := min_le_right _ _
    have hsub : ((L-n : ℕ) : ℝ) = (L : ℝ)-(n : ℝ) := Nat.cast_sub (Nat.le_of_lt hn)
    apply hmode l r η hl hr hη hflat F δ T N (Q+((n+1 : ℕ) : ℝ)) lam
      hδ hF hT hN hlam
    · linarith
    · rw [hsub] at hlambda₂
      norm_num only [Nat.cast_add,Nat.cast_one]
      linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity))

theorem modelPhaseBufferedInteriorBlock_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ) (A B : ℤ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N →
        (T/N)*deriv F (r-2*η) ≤ (A : ℝ) →
        (B : ℝ) ≤ (T/N)*deriv F (l+2*η) →
        ‖∑ q ∈ Finset.Ioo A B,
          (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
            modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(1+Real.log ((B-A-1).toNat : ℝ)) := by
  obtain ⟨C,hC,hblock⟩ := modelPhaseBufferedInteriorRange_error hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη hflat F δ T N A B hδ hF hT hN hright hleft
  by_cases hAB : A+1 ≤ B
  · have hlen : ((B-A-1).toNat : ℤ) = B-A-1 := Int.toNat_of_nonneg (by omega)
    have hlen' : ((B-A-1).toNat : ℝ) = (B : ℝ)-(A : ℝ)-1 := by exact_mod_cast hlen
    have h := hblock l r η hl hr hη hflat F δ T N A (B-A-1).toNat
      hδ hF hT hN hright (by rw [hlen']; linarith)
    have he : (∑ q ∈ Finset.Ioo A B,
        (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          modelPhaseStationaryMainTerm F T N q)) =
        ∑ n ∈ Finset.range (B-A-1).toNat,
        (modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N ((A : ℝ)+((n+1 : ℕ) : ℝ))-
          modelPhaseStationaryMainTerm F T N ((A : ℝ)+((n+1 : ℕ) : ℝ))) := by
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
