import TaoTrudgianYang2025.RobertSargosPlaneAveraging

/-! Reindexing the actual rectangular Gram terms into signed A-times-A
correlations, retaining the exact zero-padding at every boundary. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

def robertSargosPlaneCorrelation (a : ℤ → ℤ → ℂ) (M H : ℕ) (q r : ℤ) : ℝ :=
  ∑ x ∈ Finset.Ico (0:ℤ) M ×ˢ Finset.Ico (0:ℤ) H,
    ⟪robertSargosPaddedPlane a M H (x.1+q) x.2,
      robertSargosPaddedPlane a M H x.1 (x.2+r)⟫_ℝ

theorem robertSargos_plane_gram_term (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (s t : ℕ × ℕ) (hs : s ∈ Finset.range Q ×ˢ Finset.range R)
    (ht : t ∈ Finset.range Q ×ˢ Finset.range R) :
    (∑ x ∈ Finset.Ico (-(Q:ℤ)) M ×ˢ Finset.Ico (-(R:ℤ)) H,
      ⟪robertSargosPaddedPlane a M H (x.1+s.1) (x.2+s.2),
        robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)⟫_ℝ) =
      robertSargosPlaneCorrelation a M H ((s.1:ℤ)-t.1) ((t.2:ℤ)-s.2) := by
  classical
  let B := Finset.Ico (-(Q:ℤ)) (M:ℤ) ×ˢ Finset.Ico (-(R:ℤ)) (H:ℤ)
  let P : ℤ × ℤ → Prop := fun x =>
    x.1+t.1 ∈ Finset.Ico (0:ℤ) M ∧ x.2+s.2 ∈ Finset.Ico (0:ℤ) H
  let F : ℤ × ℤ → ℝ := fun x =>
    ⟪robertSargosPaddedPlane a M H (x.1+s.1) (x.2+s.2),
      robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)⟫_ℝ
  have hfilt : (∑ x ∈ B.filter P, F x) = ∑ x ∈ B, F x := by
    apply Finset.sum_filter_of_ne
    intro x _ hn
    constructor
    · by_contra hm
      simp only [F,robertSargosPaddedPlane,if_neg hm,inner_zero_right] at hn
      exact hn rfl
    · by_contra hh
      simp only [F,robertSargosPaddedPlane,if_neg hh,ite_self,inner_zero_left] at hn
      exact hn rfl
  change (∑ x ∈ B, F x) = _
  rw [← hfilt]
  unfold robertSargosPlaneCorrelation
  apply Finset.sum_bij (fun x _ => (x.1+(t.1:ℤ),x.2+(s.2:ℤ)))
  · intro x hx
    exact Finset.mem_product.mpr (Finset.mem_filter.mp hx).2
  · intro x hx y hy he
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at * <;> omega
  · intro y hy
    have hy' := Finset.mem_product.mp hy
    have hym := Finset.mem_Ico.mp hy'.1
    have hyh := Finset.mem_Ico.mp hy'.2
    have htq := Finset.mem_range.mp (Finset.mem_product.mp ht).1
    have hsr := Finset.mem_range.mp (Finset.mem_product.mp hs).2
    refine ⟨(y.1-(t.1:ℤ),y.2-(s.2:ℤ)),?_,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_Ico.mpr <;> dsimp only <;> constructor <;> omega
      · dsimp [P]
        simpa only [sub_add_cancel] using hy'
    · ext <;> simp only [sub_add_cancel]
  · intro x hx
    dsimp only [F]
    congr 2 <;> omega

end TaoTrudgianYang2025
