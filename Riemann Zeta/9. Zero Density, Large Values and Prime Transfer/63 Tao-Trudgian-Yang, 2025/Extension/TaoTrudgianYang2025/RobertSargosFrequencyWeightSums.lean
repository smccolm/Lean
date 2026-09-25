import TaoTrudgianYang2025.IntegerFixedDisplacementCount
import TaoTrudgianYang2025.RobertSargosSignedDisplacementSums

/-! Weighted counting of actual displacement/frequency triples in an affine band. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_affine_frequency_weight_le
    (S : Finset (ℤ × ℤ × ℤ)) (f : ℕ → ℝ) {N : ℕ} {Q B : ℝ}
    (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hf : ∀ n ∈ Finset.Icc 1 N, 0 ≤ f n)
    (hd : ∀ p ∈ S, p.1.natAbs ∈ Finset.Icc 1 N)
    (hq : ∀ p ∈ S, |(p.2.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*(p.1:ℝ)+(p.2.1:ℝ)-(p.2.2:ℝ)| ≤ B) :
    (∑ p ∈ S, f p.1.natAbs) ≤
      (4*Q+1)*(2*B+1)*(2*∑ n ∈ Finset.Icc 1 N, f n) := by
  classical
  let D := S.image Prod.fst
  have hmaps : ∀ p ∈ S, p.1 ∈ D := fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hD : ∀ d ∈ D, d.natAbs ∈ Finset.Icc 1 N := by
    intro d hd'
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd'
    exact hd p hp
  have hcard : ∀ d : ℤ,
      ((S.filter (fun p => p.1 = d)).card:ℝ) ≤ (4*Q+1)*(2*B+1) := by
    intro d
    apply integer_fixed_displacement_band_card_le _ hQ hB
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      exact hq p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact hband p (Finset.mem_filter.mp hp).1
  calc
    _ = ∑ d ∈ D, ∑ _p ∈ S.filter (fun p => p.1 = d), f d.natAbs :=
      (Finset.sum_fiberwise_of_maps_to' hmaps (fun d => f d.natAbs)).symm
    _ ≤ ∑ d ∈ D, (4*Q+1)*(2*B+1)*f d.natAbs := by
      apply Finset.sum_le_sum
      intro d hd'
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcard d) (hf _ (hD d hd'))
    _ = (4*Q+1)*(2*B+1)*(∑ d ∈ D, f d.natAbs) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_integer_natAbs_le_twice D f hf hD) (by positivity)

theorem sum_affine_frequency_rpow_weight_le
    (S : Finset (ℤ × ℤ × ℤ)) {N : ℕ} {Q B ε A : ℝ}
    (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hε : 0 < ε) (hA : 0 ≤ A) (hN : 1 ≤ N)
    (hd : ∀ p ∈ S, p.1.natAbs ∈ Finset.Icc 1 N)
    (hq : ∀ p ∈ S, |(p.2.1:ℝ)| ≤ 2*Q)
    (hband : ∀ p ∈ S, |2*(p.1:ℝ)+(p.2.1:ℝ)-(p.2.2:ℝ)| ≤ B) :
    (∑ p ∈ S, (p.1.natAbs:ℝ)^(ε/2)*(1+A/p.1.natAbs)) ≤
      2*(1+2/ε)*(4*Q+1)*(2*B+1)*(N:ℝ)^ε*((N:ℝ)+A) := by
  calc
    _ ≤ (4*Q+1)*(2*B+1)*
        (2*∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(ε/2)*(1+A/n)) :=
      sum_affine_frequency_weight_le S _ hQ hB (fun _ _ => by positivity) hd hq hband
    _ ≤ (4*Q+1)*(2*B+1)*
        (2*((1+2/ε)*(N:ℝ)^ε*((N:ℝ)+A))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_positive_displacement_weight_le hε hA hN)
          (by norm_num)) (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025

