import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

#check sum_Ioo_gcd_div_le
#check Finset.sum_mul
#check Finset.mul_sum
#check Finset.sum_le_sum_of_subset_of_nonneg

theorem sum_Icc_gcd_div_le_harmonic
    (L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Icc 1 L, (Nat.gcd H q : ℝ) / q) ≤
      (H.divisors.card : ℝ) * (((harmonic (L + 1) : ℚ) : ℝ)) := by
  have hset : Finset.Ioo 0 (L + 1) = Finset.Icc 1 L := by
    ext q
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [← hset]
  exact sum_Ioo_gcd_div_le 0 (L + 1) H hH

theorem weightedGCDMass_le
    (c : ℕ → ℂ) (L : ℕ) {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : ∀ n ∈ Finset.Icc 1 L, ‖c n‖ ≤ B)
    (hdiv : ∀ n ∈ Finset.Icc 1 L, (n.divisors.card : ℝ) ≤ E) :
    (∑ h ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
      B ^ 2 * E * (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
  let H : ℝ := (((harmonic (L + 1) : ℚ) : ℝ))
  have hH : 0 ≤ H := by
    dsimp only [H]
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hinner : ∀ h ∈ Finset.Icc 1 L,
      (∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
        (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) := by
    intro h hh
    have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
    calc
      (∑ k ∈ Finset.Icc 1 L,
          ‖c h‖ * ‖c k‖ *
            ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
        ∑ k ∈ Finset.Icc 1 L,
          (B ^ 2 / (h : ℝ)) * ((Nat.gcd h k : ℝ) / (k : ℝ)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk0 : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
            have hg : 0 ≤ (Nat.gcd h k : ℝ) := by positivity
            have hden : 0 ≤ ((h : ℝ) * (k : ℝ)) := by positivity
            have hcprod : ‖c h‖ * ‖c k‖ ≤ B ^ 2 := by
              calc
                ‖c h‖ * ‖c k‖ ≤ B * B :=
                  mul_le_mul (hc h hh) (hc k hk) (norm_nonneg _) hB
                _ = B ^ 2 := by ring
            calc
              ‖c h‖ * ‖c k‖ *
                    ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) ≤
                  B ^ 2 *
                    ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) := by
                      gcongr
              _ = (B ^ 2 / (h : ℝ)) *
                    ((Nat.gcd h k : ℝ) / (k : ℝ)) := by
                      field_simp
      _ = (B ^ 2 / (h : ℝ)) *
          (∑ k ∈ Finset.Icc 1 L, (Nat.gcd h k : ℝ) / (k : ℝ)) := by
            rw [Finset.mul_sum]
      _ ≤ (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) := by
            gcongr
            exact sum_Icc_gcd_div_le_harmonic L h hh0.ne'
  calc
    (∑ h ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        ‖c h‖ * ‖c k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ)))) ≤
      ∑ h ∈ Finset.Icc 1 L,
        (B ^ 2 / (h : ℝ)) * ((h.divisors.card : ℝ) * H) :=
          Finset.sum_le_sum hinner
    _ ≤ ∑ h ∈ Finset.Icc 1 L,
        (B ^ 2 / (h : ℝ)) * (E * H) := by
          apply Finset.sum_le_sum
          intro h hh
          gcongr
          exact hdiv h hh
    _ = (B ^ 2 * E * H) *
        (∑ h ∈ Finset.Icc 1 L, (h : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [div_eq_mul_inv]
          ring
    _ = (B ^ 2 * E * H) * (((harmonic L : ℚ) : ℝ)) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rfl
    _ ≤ (B ^ 2 * E * H) * H := by
          gcongr
          dsimp only [H]
          rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
          push_cast
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          · intro n _hn _hnL
            positivity
    _ = B ^ 2 * E * (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
          dsimp only [H]
          ring

end RiemannZeta.GuthMaynard
