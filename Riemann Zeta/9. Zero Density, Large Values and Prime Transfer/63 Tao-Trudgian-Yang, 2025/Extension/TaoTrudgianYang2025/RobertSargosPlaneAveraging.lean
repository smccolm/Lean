import TaoTrudgianYang2025.ExponentPairWeylSum

/-! Actual two-coordinate zero-padding and rectangular shift averaging.
This is the finite Cauchy step of the A-times-A argument, before
reindexing the Gram expansion into signed differences. -/

noncomputable section
open RiemannZeta.GuthMaynard
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

def robertSargosPaddedPlane (a : ℤ → ℤ → ℂ) (M H : ℕ) (m h : ℤ) : ℂ :=
  if m ∈ Finset.Ico (0:ℤ) M then
    if h ∈ Finset.Ico (0:ℤ) H then a m h else 0
  else 0

theorem robertSargos_plane_shift_sum (a : ℤ → ℤ → ℂ) (M H Q R q r : ℕ)
    (hq : q < Q) (hr : r < R) :
    (∑ m ∈ Finset.Ico (-(Q:ℤ)) M, ∑ h ∈ Finset.Ico (-(R:ℤ)) H,
      robertSargosPaddedPlane a M H (m+q) (h+r)) =
        ∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a m h := by
  have hi (m : ℤ) :
      (∑ h ∈ Finset.Ico (-(R:ℤ)) H, robertSargosPaddedPlane a M H (m+q) (h+r)) =
        paddedShift (fun n => ∑ h ∈ Finset.Ico (0:ℤ) H, a n h) M m q := by
    by_cases hm : m+q ∈ Finset.Ico (0:ℤ) M
    · simp only [robertSargosPaddedPlane,paddedShift,if_pos hm]
      exact sum_paddedShift_eq (a (m+q)) H R r hr
    · simp only [robertSargosPaddedPlane,paddedShift,if_neg hm,Finset.sum_const_zero]
  simp only [hi]
  exact sum_paddedShift_eq (fun n => ∑ h ∈ Finset.Ico (0:ℤ) H, a n h) M Q q hq

theorem robertSargos_plane_averaging (a : ℤ → ℤ → ℂ) (M H Q R : ℕ) :
    ((Q*R:ℕ):ℝ)^2*
      ‖∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a m h‖^2 ≤
      (((M+Q)*(H+R):ℕ):ℝ)*
        ∑ x ∈ Finset.Ico (-(Q:ℤ)) M ×ˢ Finset.Ico (-(R:ℤ)) H,
          ‖∑ t ∈ Finset.range Q ×ˢ Finset.range R,
            robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)‖^2 := by
  let A := Finset.Ico (-(Q:ℤ)) (M:ℤ) ×ˢ Finset.Ico (-(R:ℤ)) (H:ℤ)
  let T := Finset.range Q ×ˢ Finset.range R
  let U : ℤ × ℤ → ℂ := fun x =>
    ∑ t ∈ T, robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)
  let S : ℂ := ∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a m h
  have hs : (∑ x ∈ A, U x) = (Q*R) • S := by
    dsimp only [U]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _t ∈ T, S := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_product.mp ht
        dsimp only [A,S]
        rw [Finset.sum_product]
        exact robertSargos_plane_shift_sum a M H Q R t.1 t.2
          (Finset.mem_range.mp ht'.1) (Finset.mem_range.mp ht'.2)
      _ = _ := by simp [T]
  have hcm : ((Finset.Ico (-(Q:ℤ)) (M:ℤ)).card:ℝ) = ((M+Q:ℕ):ℝ) := by
    norm_num [Int.card_Ico]
    norm_cast
  have hch : ((Finset.Ico (-(R:ℤ)) (H:ℤ)).card:ℝ) = ((H+R:ℕ):ℝ) := by
    norm_num [Int.card_Ico]
    norm_cast
  have hc : (A.card:ℝ) = (((M+Q)*(H+R):ℕ):ℝ) := by
    dsimp only [A]
    rw [Finset.card_product,Nat.cast_mul,hcm,hch,Nat.cast_mul]
  have ht := norm_sum_sq_le_card_mul_sum_norm_sq A U
  rw [hs,hc,RCLike.norm_nsmul ℂ,nsmul_eq_mul] at ht
  simpa only [mul_pow] using ht

theorem robertSargos_plane_gram (a : ℤ → ℤ → ℂ) (M H Q R : ℕ) :
    (∑ x ∈ Finset.Ico (-(Q:ℤ)) M ×ˢ Finset.Ico (-(R:ℤ)) H,
      ‖∑ t ∈ Finset.range Q ×ˢ Finset.range R,
        robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)‖^2) =
      ∑ s ∈ Finset.range Q ×ˢ Finset.range R,
        ∑ t ∈ Finset.range Q ×ˢ Finset.range R,
          ∑ x ∈ Finset.Ico (-(Q:ℤ)) M ×ˢ Finset.Ico (-(R:ℤ)) H,
            ⟪robertSargosPaddedPlane a M H (x.1+s.1) (x.2+s.2),
              robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)⟫_ℝ := by
  simp only [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro x _
  exact real_inner_comm _ _

end TaoTrudgianYang2025
