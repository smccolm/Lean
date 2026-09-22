import TaoTrudgianYang2025.ExponentPairCorrelationNormalized
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Exact finite shift sums, retaining the harmonic loss. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sum_shift_rpow_le {q : ℝ} (hq : 0 ≤ q) (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H-1), (r : ℝ)^q ≤ (H : ℝ)*(H : ℝ)^q := by
  have hc : (Finset.Icc 1 (H-1)).card ≤ H := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 (H-1), (H : ℝ)^q := by
      apply Finset.sum_le_sum
      intro r hr
      exact Real.rpow_le_rpow (Nat.cast_nonneg r)
        (by exact_mod_cast (show r ≤ H by have := Finset.mem_Icc.mp hr; omega)) hq
    _ = ((Finset.Icc 1 (H-1)).card : ℝ)*(H : ℝ)^q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem sum_shift_inv_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H-1), (r : ℝ)⁻¹ ≤ 1+Real.log H := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 H, (r : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega)) (by intros; positivity)
    _ = (harmonic H : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log H

theorem sum_sourceShiftCorrelation_le
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/2 ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N : ℝ) (a L H : ℕ),
          0 < T → 2 ≤ N → (H : ℝ) ≤ η₀*N →
          N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          (∑ r ∈ Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) ≤
            C*((T/N^2)^(k+ε)*N^(l+ε)*(H : ℝ)*(H : ℝ)^(k+ε)+
              (N^2/T)*(1+Real.log H)) := by
  obtain ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,C,hC,hbound⟩ :=
    sourceShiftCorrelation_normalized_bound hkl hσ hε
  refine ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,C,hC,?_⟩
  intro F T N a L H hT hN hHN ha hb hF
  have hNpos : 0 < N := by linarith
  have hM : 0 ≤ (T/N^2)^(k+ε)*N^(l+ε) := by positivity
  have hI : 0 ≤ N^2/T := by positivity
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (H-1),
        C*((T/N^2)^(k+ε)*N^(l+ε)*(r : ℝ)^(k+ε)+N^2/(T*r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrI := Finset.mem_Icc.mp hr
      exact hbound F T N a L r hT hN (by omega)
        ((by exact_mod_cast (show r ≤ H by omega) : (r : ℝ) ≤ H).trans hHN) ha hb hF
    _ = C*((T/N^2)^(k+ε)*N^(l+ε)*(∑ r ∈ Finset.Icc 1 (H-1), (r : ℝ)^(k+ε))+
        (N^2/T)*(∑ r ∈ Finset.Icc 1 (H-1), (r : ℝ)⁻¹)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ C*((T/N^2)^(k+ε)*N^(l+ε)*((H : ℝ)*(H : ℝ)^(k+ε))+
        (N^2/T)*(1+Real.log H)) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_shift_rpow_le
          (show 0 ≤ k+ε by linarith [hkl.inTriangle.1]) H) hM)
        (mul_le_mul_of_nonneg_left (sum_shift_inv_le H) hI)
    _ = _ := by ring

end TaoTrudgianYang2025
