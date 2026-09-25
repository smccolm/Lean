import TaoTrudgianYang2025.RobertSargosATimesA
import TaoTrudgianYang2025.SargosSourceDifferencing

/-! Literal one-based support entry for Robert--Sargos (2002), Lemma 1.
The source array vanishes outside its actual finite rectangle. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

theorem robertSargos_sum_one_based {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (M : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, f (m+1)) = ∑ m ∈ Finset.Icc (1:ℤ) M, f m := by
  have he : Finset.Ioc (0:ℤ) M = Finset.Icc (1:ℤ) M := by
    ext m
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  simpa only [he] using sargos_sum_Ico_add_one f M

theorem robertSargos_padded_source_plane (a : ℤ → ℤ → ℂ) (M H : ℕ)
    (ha : ∀ m h : ℤ, m ∉ Finset.Icc (1:ℤ) M ∨ h ∉ Finset.Icc (1:ℤ) H →
      a m h = 0) (m h : ℤ) :
    robertSargosPaddedPlane (fun n k => a (n+1) (k+1)) M H m h = a (m+1) (h+1) := by
  by_cases hm : m ∈ Finset.Ico (0:ℤ) M
  · by_cases hh : h ∈ Finset.Ico (0:ℤ) H
    · simp only [robertSargosPaddedPlane,if_pos hm,if_pos hh]
    · have hh' : h+1 ∉ Finset.Icc (1:ℤ) H := by
        simp only [Finset.mem_Ico] at hh
        simp only [Finset.mem_Icc]
        omega
      simp only [robertSargosPaddedPlane,if_pos hm,if_neg hh,ha _ _ (Or.inr hh')]
  · have hm' : m+1 ∉ Finset.Icc (1:ℤ) M := by
      simp only [Finset.mem_Ico] at hm
      simp only [Finset.mem_Icc]
      omega
    simp only [robertSargosPaddedPlane,if_neg hm,ha _ _ (Or.inl hm')]

theorem robertSargos_source_plane_sum (a : ℤ → ℤ → ℂ) (M H : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a (m+1) (h+1)) =
      ∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) H, a m h := by
  simp_rw [robertSargos_sum_one_based]
  exact robertSargos_sum_one_based (fun m => ∑ h ∈ Finset.Icc (1:ℤ) H, a m h) M

theorem robertSargos_source_plane_correlation (a : ℤ → ℤ → ℂ) (M H : ℕ)
    (ha : ∀ m h : ℤ, m ∉ Finset.Icc (1:ℤ) M ∨ h ∉ Finset.Icc (1:ℤ) H →
      a m h = 0) (q r : ℤ) :
    robertSargosPlaneCorrelation (fun m h => a (m+1) (h+1)) M H q r =
      ∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) H,
        ⟪a (m+q) h,a m (h+r)⟫_ℝ := by
  unfold robertSargosPlaneCorrelation
  simp_rw [robertSargos_padded_source_plane a M H ha]
  rw [Finset.sum_product]
  simp only [show ∀ x y : ℤ, x+y+1 = x+1+y by intros; omega]
  have hi (m : ℤ) :
      (∑ h ∈ Finset.Ico (0:ℤ) H, ⟪a (m+1+q) (h+1),a (m+1) (h+1+r)⟫_ℝ) =
        ∑ h ∈ Finset.Icc (1:ℤ) H, ⟪a (m+1+q) h,a (m+1) (h+r)⟫_ℝ :=
    robertSargos_sum_one_based (fun h => ⟪a (m+1+q) h,a (m+1) (h+r)⟫_ℝ) H
  simp only [hi]
  exact robertSargos_sum_one_based
    (fun m => ∑ h ∈ Finset.Icc (1:ℤ) H, ⟪a (m+q) h,a m (h+r)⟫_ℝ) M

theorem robertSargos_source_a_times_a (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hQM : Q ≤ M) (hRH : R ≤ H)
    (ha : ∀ m h : ℤ, m ∉ Finset.Icc (1:ℤ) M ∨ h ∉ Finset.Icc (1:ℤ) H →
      a m h = 0) :
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) H, a m h‖^2 ≤
      (4*(M:ℝ)*H/((Q:ℝ)*R))*
        ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            (∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) H,
              ⟪a (m+q) h,a m (h+r)⟫_ℝ) := by
  have ht := robertSargos_a_times_a (fun m h => a (m+1) (h+1)) M H Q R
    hQ hR hQM hRH
  rw [robertSargos_source_plane_sum] at ht
  simpa only [robertSargosWeightedCorrelations,
    robertSargos_source_plane_correlation a M H ha] using ht

end TaoTrudgianYang2025

