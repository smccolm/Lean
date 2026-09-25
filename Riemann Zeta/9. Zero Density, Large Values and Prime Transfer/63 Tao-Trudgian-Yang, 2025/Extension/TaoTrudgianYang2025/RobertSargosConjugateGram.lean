import TaoTrudgianYang2025.SargosSymmetricAveraging
import TaoTrudgianYang2025.TriangularShiftBounds

/-! Exact centered conjugated Gram terms for the initial Robert--Sargos A-process. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace TaoTrudgianYang2025

def robertSargosCenteredCorrelation (a : ℤ → ℂ) (M : ℕ) (h : ℤ) : ℝ :=
  ∑ m ∈ Finset.Ico (0:ℤ) M,
    ⟪sargosPaddedSequence a M (m+h),sargosPaddedSequence a M (m-h)⟫_ℝ

theorem robertSargos_centered_correlation_neg (a : ℤ → ℂ) (M : ℕ) (h : ℤ) :
    robertSargosCenteredCorrelation a M (-h) = robertSargosCenteredCorrelation a M h := by
  unfold robertSargosCenteredCorrelation
  simp only [sub_neg_eq_add,← sub_eq_add_neg]
  apply Finset.sum_congr rfl
  intro m _
  exact real_inner_comm _ _

theorem robertSargos_centered_correlation_zero (a : ℤ → ℂ) (M : ℕ) :
    robertSargosCenteredCorrelation a M 0 =
      ∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2 := by
  unfold robertSargosCenteredCorrelation
  simp only [add_zero,sub_zero,real_inner_self_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sargosPaddedSequence_eq a M hm]

theorem robertSargos_even_gram_term (a : ℤ → ℂ) (M H s t : ℕ)
    (hs : s < H) (ht : t < H) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
      ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ) =
      robertSargosCenteredCorrelation a M ((s:ℤ)-t) := by
  classical
  let B := Finset.Ico (-(2*(H:ℤ))) (M:ℤ)
  let P : ℤ → Prop := fun n => n+(s:ℤ)+t ∈ Finset.Ico (0:ℤ) M
  let F : ℤ → ℝ := fun n =>
    ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ
  have hfilt : (∑ n ∈ B.filter P, F n) = ∑ n ∈ B, F n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    have hsupp : n+2*s ∈ Finset.Ico (0:ℤ) M ∧
        n+2*t ∈ Finset.Ico (0:ℤ) M := by
      constructor
      · by_contra hn'
        simp only [F,sargosPaddedSequence,if_neg hn',inner_zero_left] at hn
        exact hn rfl
      · by_contra hn'
        simp only [F,sargosPaddedSequence,if_neg hn',inner_zero_right] at hn
        exact hn rfl
    change n+(s:ℤ)+t ∈ Finset.Ico (0:ℤ) M
    simp only [Finset.mem_Ico] at hsupp ⊢
    constructor <;> omega
  change (∑ n ∈ B, F n) = _
  rw [← hfilt]
  unfold robertSargosCenteredCorrelation
  apply Finset.sum_bij (fun n _ => n+(s:ℤ)+t)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n _ k _ he
    omega
  · intro m hm
    have hm' := Finset.mem_Ico.mp hm
    refine ⟨m-(s:ℤ)-t,?_,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · dsimp only [B]
        apply Finset.mem_Ico.mpr
        constructor <;> omega
      · dsimp only [P]
        have he : m-(s:ℤ)-t+s+t = m := by omega
        simpa only [he] using hm
    · omega
  · intro n _
    dsimp only [F]
    congr 2 <;> omega

theorem robertSargos_even_gram (a : ℤ → ℂ) (M H : ℕ) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
      ‖∑ s ∈ Finset.range H, sargosPaddedSequence a M (n+2*s)‖^2) =
      ∑ h ∈ Finset.Ioo (-(H:ℤ)) H,
        ((H-h.natAbs:ℕ):ℝ)*robertSargosCenteredCorrelation a M h := by
  calc
    _ = ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        ∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
          ⟪sargosPaddedSequence a M (n+2*s),sargosPaddedSequence a M (n+2*t)⟫_ℝ := by
      simp only [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro n _
      exact real_inner_comm _ _
    _ = ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        robertSargosCenteredCorrelation a M ((s:ℤ)-t) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      exact robertSargos_even_gram_term a M H s t
        (Finset.mem_range.mp hs) (Finset.mem_range.mp ht)
    _ = _ := sum_signed_shift_differences H (robertSargosCenteredCorrelation a M)

end TaoTrudgianYang2025
