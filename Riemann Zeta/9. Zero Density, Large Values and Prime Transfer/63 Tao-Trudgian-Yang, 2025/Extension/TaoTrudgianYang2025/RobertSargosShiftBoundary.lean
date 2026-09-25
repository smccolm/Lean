import TaoTrudgianYang2025.RobertSargosShiftSupport
import TaoTrudgianYang2025.IntegerIntervalShift

/-! Explicit norm error for the genuinely common translated source interval. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem norm_robertSargos_shifted_boundary (w : ℤ → ℂ) (M H Q N : ℕ) (h q n : ℤ)
    (hh : h ∈ Finset.Ico (H:ℤ) (2*H))
    (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q)
    (hn : n ∈ Finset.Icc (1:ℤ) N)
    (hw : ∀ m, ‖w m‖ ≤ 1) :
    ‖(∑ m ∈ robertSargosShiftedMInterval M h q n, w (m+n))-
      ∑ m ∈ robertSargosCommonMInterval M H Q N, w (m+n)‖ ≤
      4*(H:ℝ)+4*Q+2*N := by
  rw [← Finset.sum_sdiff_eq_sub (robertSargos_common_interval_subset M H Q N h q n hh hq hn)]
  calc
    _ ≤ ∑ m ∈ robertSargosShiftedMInterval M h q n \ robertSargosCommonMInterval M H Q N,
        ‖w (m+n)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ robertSargosShiftedMInterval M h q n \ robertSargosCommonMInterval M H Q N,
        (1:ℝ) := Finset.sum_le_sum (fun m _ => hw (m+n))
    _ ≤ _ := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
        robertSargos_shifted_boundary_card M H Q N h q n hh hq hn

theorem robertSargos_m_overlap_zero_source (M : ℕ) (h q : ℤ) :
    robertSargosMOverlap M h q 0 =
      Finset.Icc (max (h+1) (h+1-q)) (min ((M:ℤ)-h) ((M:ℤ)-h-q)) := by
  ext m
  simp only [robertSargosMOverlap,Finset.mem_Icc,max_le_iff,le_min_iff]
  omega

theorem robertSargos_source_shift_average (w : ℤ → ℂ) (M N : ℕ) (h q : ℤ)
    (hN : 0 < N) :
    (∑ m ∈ robertSargosMOverlap M h q 0, w m) =
      (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ robertSargosShiftedMInterval M h q n, w (m+n) := by
  rw [robertSargos_m_overlap_zero_source]
  exact sum_integer_interval_average w _ _ N hN

end TaoTrudgianYang2025
